module
public import Theory.Representation.SevenMultiplicity
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.GroupTheory.FaithfulNormalRestriction

/-!
# Selecting homogeneous sections for a central order-seven action

A fixed-point-free operator remains fixed-point-free on every invariant
subquotient. A perfect actor survives on an irreducible section. In a direct
product, the commuting second factor spans isomorphic copies of every simple
first-factor constituent, so the restriction is homogeneous. Constituent
kernels equal the kernel of the whole restriction; a surviving simple normal
subgroup with trivial centralizer makes those constituents faithful.

These facts are used by L3Four.SevenProduct to prove the displacement bound
in Aschbacher–Smith 5.1.17, printed p.641 (refs/quasithin.pdf).
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace Representation.FixedFreeSections
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

theorem quotient_fixedFree (ρ : Representation k G V) (a : G)
    (hf : ∀ v, ρ a v = v → v = 0) (N : Subrepresentation ρ) :
    ∀ v, N.quotientRepresentation a v = v → v = 0 := by
  have hinj : Function.Injective (ρ a - (1 : Module.End k V)) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    exact hf v (sub_eq_zero.mp hv)
  let δ : N.toSubmodule →ₗ[k] N.toSubmodule := N.toRepresentation a - 1
  have hδ : Function.Injective δ := by
    intro u v huv
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val huv
  have hsur : Function.Surjective δ := (LinearMap.injective_iff_surjective).mp hδ
  intro q hq
  obtain ⟨v,rfl⟩ := N.toSubmodule.mkQ_surjective q
  have hv : (ρ a - 1) v ∈ N.toSubmodule := (Submodule.Quotient.eq _).mp hq
  obtain ⟨u,hu⟩ := hsur ⟨(ρ a - 1) v,hv⟩
  have he : (u : V) = v := hinj (congrArg Subtype.val hu)
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact he ▸ u.property

omit [FiniteDimensional k V] in
theorem subrepresentation_fixedFree (ρ : Representation k G V) (a : G)
    (hf : ∀ v, ρ a v = v → v = 0) (U : Subrepresentation ρ) :
    ∀ v, U.toRepresentation a v = v → v = 0 := by
  intro v hv
  apply Subtype.ext
  exact hf v (congrArg Subtype.val hv)
end Representation.FixedFreeSections

namespace Representation.SevenMultiplicity
open BinaryOffender.Homogeneous
variable {M A V : Type*} [Group M] [Group A] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional (ZMod 2) V] in
theorem product_homogeneous (ρ : Representation (ZMod 2) (M × A) V)
    (hi : IsIrreducible ρ)
    (I : Subrepresentation (ρ.comp (MonoidHom.inl M A)))
    (hI : IsIrreducible I.toRepresentation) : homogeneousPart I ⊤ = ⊤ := by
  let σ := ρ.comp (MonoidHom.inl M A)
  let J (a : A) : Subrepresentation σ := {
    toSubmodule := I.toSubmodule.map (ρ (1,a))
    apply_mem_toSubmodule m v hv := by
      obtain ⟨u,hu,rfl⟩ := hv
      refine ⟨σ m u,I.apply_mem_toSubmodule m hu,?_⟩
      change ρ (1,a) (ρ (m,1) u) = ρ (m,1) (ρ (1,a) u)
      simp only [← Module.End.mul_apply,← map_mul,Prod.mk_mul_mk,one_mul,mul_one]
  }
  have hJ (a : A) : SameModule I (J a) := by
    let e := Submodule.equivMapOfInjective (ρ (1,a)) (ρ.apply_bijective (1,a)).injective I.toSubmodule
    refine ⟨e,?_⟩
    intro m v
    apply Subtype.ext
    change ρ (1,a) (ρ (m,1) v) = ρ (m,1) (ρ (1,a) v)
    simp only [← Module.End.mul_apply,← map_mul,Prod.mk_mul_mk,one_mul,mul_one]
  let U : Submodule (ZMod 2) V := ⨆ a, (J a).toSubmodule
  let P : Subrepresentation ρ := {
    toSubmodule := U
    apply_mem_toSubmodule g v hv := by
      apply Submodule.iSup_induction _ (motive := fun w => ρ g w ∈ U) hv
      · intro a u hu
        obtain ⟨w,hw,rfl⟩ := hu
        apply le_iSup (fun b => (J b).toSubmodule) (g.2*a)
        refine ⟨σ g.1 w,I.apply_mem_toSubmodule g.1 hw,?_⟩
        change ρ (1,g.2*a) (ρ (g.1,1) w) = ρ g (ρ (1,a) w)
        simp only [← Module.End.mul_apply,← map_mul,Prod.mul_def,one_mul,mul_one]
      · simpa only [map_zero] using U.zero_mem
      · intro u v hu hv
        simpa only [map_add] using U.add_mem hu hv
  }
  have hIP : I.toSubmodule ≤ P.toSubmodule := by
    intro v hv
    apply le_iSup (fun a => (J a).toSubmodule) 1
    exact ⟨v,hv,show ρ (1 : M × A) v = v from by rw [map_one]; rfl⟩
  have hP : P ≠ ⊥ := by
    intro hz
    have hz' : P.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hz
    have hIz : I.toSubmodule = ⊥ := bot_unique (hIP.trans hz'.le)
    exact ((Subrepresentation.irreducible_iff_isAtom I).mp hI).ne_bot
      (Subrepresentation.toSubmodule_injective hIz)
  have htop : P = ⊤ := (hi.eq_bot_or_eq_top P).resolve_left hP
  apply top_unique
  calc
    ⊤ = P.toSubmodule := (congrArg Subrepresentation.toSubmodule htop).symm
    _ ≤ homogeneousPart I ⊤ :=
      iSup_le fun a => le_iSup_of_le (J a) (le_iSup_of_le ⟨le_top,hJ a⟩ le_rfl)
end Representation.SevenMultiplicity

namespace Representation.SevenMultiplicity
open BinaryOffender.Homogeneous
variable {M A V : Type*} [Group M] [Group A] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem exists_product_section (ρ : Representation (ZMod 2) (M × A) V)
    (K : Subgroup (M × A)) [Group.IsPerfect K]
    (hn : ¬ K ≤ ρ.ker)
    (hf : ∀ a : A, a ≠ 1 → ∀ v, ρ (1,a) v = v → v = 0) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      IsIrreducible N.quotientRepresentation ∧
      ¬ K ≤ N.quotientRepresentation.ker ∧
      (∀ a : A, a ≠ 1 → ∀ v, N.quotientRepresentation (1,a) v = v → v = 0) ∧
      (∀ y : M, fixedCodim N.quotientRepresentation (zpowers (y,1)) ≤
        fixedCodim ρ (zpowers (y,1))) ∧
      ∀ I : Subrepresentation (N.quotientRepresentation.comp (MonoidHom.inl M A)),
        IsIrreducible I.toRepresentation → homogeneousPart I ⊤ = ⊤ := by
  obtain ⟨U,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect K hn
  refine ⟨U,N,hi,hn,?_,?_,?_⟩
  · intro a ha
    exact FixedFreeSections.quotient_fixedFree U.toRepresentation (1,a)
      (FixedFreeSections.subrepresentation_fixedFree ρ (1,a) (hf a ha) U) N
  · intro y
    have hu := fixedCodim_subrepresentation_le ρ U (zpowers (y,1))
    have hn := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N (zpowers (y,1))
    omega
  · intro I hI
    exact product_homogeneous N.quotientRepresentation hi I hI
end Representation.SevenMultiplicity

namespace Representation.SevenMultiplicity
open BinaryOffender.Homogeneous
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]

theorem ker_eq_of_homogeneous (σ : Representation (ZMod 2) M V)
    (I : Subrepresentation σ) (hh : homogeneousPart I ⊤ = ⊤) :
    I.toRepresentation.ker = σ.ker := by
  apply le_antisymm
  · intro m hm
    have hfix : homogeneousPart I ⊤ ≤ (σ m - 1).ker := by
      apply iSup_le
      intro J
      apply iSup_le
      rintro ⟨_,e,he⟩
      intro v hv
      obtain ⟨u,hu⟩ := e.surjective (⟨v,hv⟩ : J.toSubmodule)
      have hh := he m u
      have hmu : I.toRepresentation m u = u := LinearMap.congr_fun hm u
      rw [hmu,hu] at hh
      exact sub_eq_zero.mpr (congrArg Subtype.val hh.symm)
    rw [hh] at hfix
    apply LinearMap.ext
    intro v
    exact sub_eq_zero.mp (hfix Submodule.mem_top)
  · intro m hm
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun hm (v : V)
end Representation.SevenMultiplicity

namespace Representation.SevenMultiplicity
open BinaryOffender.Homogeneous
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]

theorem faithful_constituent_of_surviving_simple (σ : Representation (ZMod 2) M V)
    (K : Subgroup M) [K.Normal] [IsSimpleGroup K]
    (hc : centralizer (K : Set M) = ⊥) (hn : ¬ K ≤ σ.ker)
    (I : Subrepresentation σ) (hh : homogeneousPart I ⊤ = ⊤) :
    Function.Injective I.toRepresentation := by
  apply MonoidHom.injective_of_injective_normal_restriction I.toRepresentation K _ hc
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (I.toRepresentation.comp K.subtype).ker inferInstance with hb | ht
  · exact hb
  · exfalso
    apply hn
    rw [← ker_eq_of_homogeneous σ I hh]
    intro k hk
    have hmem : (⟨k,hk⟩ : K) ∈ (I.toRepresentation.comp K.subtype).ker := by rw [ht]; trivial
    exact hmem
end Representation.SevenMultiplicity
