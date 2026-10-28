module
public import Theory.Representation.NormalElementaryQuotient.MinimalNormal
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]

theorem central_dichotomy (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hmin : ∀ D : Subgroup G, D.Normal → D ≤ V → D = V ∨ D ≤ center G)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (P : Subrepresentation (representation V q hq hker)) :
    P = ⊤ ∨ P.toSubmodule ≤ fixedSpace (representation V q hq hker) ⊤ := by
  let ρ := representation V q hq hker
  let D : Subgroup V := P.toSubmodule.toAddSubgroup.toSubgroup'
  let N := D.map V.subtype
  have hn : N.Normal := by
    constructor
    rintro _ ⟨v,hv,rfl⟩ g
    let w : V := ⟨g * (v : G) * g⁻¹,(inferInstance : V.Normal).conj_mem _ v.property g⟩
    refine ⟨w,?_,rfl⟩
    have hh := P.apply_mem_toSubmodule (q g) (show Additive.ofMul v ∈ P.toSubmodule from hv)
    have he : (ρ (q g) (Additive.ofMul v)).toMul = w := by
      apply Subtype.ext
      exact representation_apply V q hq hker g (Additive.ofMul v)
    change (ρ (q g) (Additive.ofMul v)).toMul ∈ D at hh
    rwa [he] at hh
  rcases hmin N hn (map_subtype_le _) with he | hc
  · left
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    have hh : (v.toMul : G) ∈ N := he.ge v.toMul.property
    obtain ⟨w,hw,heq⟩ := hh
    have heq' : w = v.toMul := Subtype.ext heq
    change v.toMul ∈ D
    rwa [heq'] at hw
  · right
    intro v hv a
    obtain ⟨g,hg⟩ := hq a.val
    have hh := hc (show (v.toMul:G) ∈ N from mem_map_of_mem V.subtype hv)
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ a.val v).toMul:G) = (v.toMul:G)
    rw [←hg,representation_apply]
    rw [mem_center_iff.mp hh g, mul_inv_cancel_right]

theorem commutator_top (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hwhole : ⁅V, (⊤ : Subgroup G)⁆ = V)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) :
    subspaceCommutator (representation V q hq hker) ⊤ ⊤ = ⊤ := by
  have hh := commutatorSpace_eq V q hq hker (⊤:Subgroup G)
  rw [map_top_of_surjective q hq] at hh
  rw [←hh]
  ext v
  change (v.toMul:G) ∈ ⁅V,(⊤:Subgroup G)⁆ ↔ True
  rw [hwhole]
  exact iff_true_intro v.toMul.property
end Representation.NormalElementaryQuotient

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem faithful_fixedQuotient_of_core (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hc : pCore 2 G = ⊥) :
    Function.Injective (fixedQuotient ρ ⊤) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  have hh : (⟨g,mem_top g⟩ : (⊤:Subgroup G)) ∈
      (fixedQuotientRepresentation ρ ⊤).ker := by
    exact (mem_fixedQuotient_ker_iff ρ ⊤ _).mpr
      ((quotient_kernel_iff ρ ⊤ g).mp hg)
  have hle := fixedQuotient_ker_le_pCore ρ hf ⊤ hh
  have he : (pCore 2 (⊤:Subgroup G)).map (⊤:Subgroup G).subtype ≤ pCore 2 G := by
    exact (pCore_map_iso 2 (Subgroup.topEquiv : (⊤:Subgroup G) ≃* G)).le
  have hgcore := he (mem_map_of_mem (⊤:Subgroup G).subtype hle)
  exact hc ▸ hgcore
end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def HasUniqueCentralChief (ρ : Representation (ZMod 2) G V) : Prop :=
  IsCoatom (fixedSubrepresentation ρ ⊤) ∧
  IsIrreducible (fixedQuotient ρ ⊤) ∧
  Function.Injective (fixedQuotient ρ ⊤) ∧
  ∀ (c : ℕ → Subrepresentation ρ) (n : ℕ), c 0 = ⊥ → c n = ⊤ →
    (∀ i < n, c i ⋖ c (i+1)) →
    ∃! i, i < n ∧ ¬ (⊤:Subgroup G) ≤ (sectionRepresentation ρ (c i) (c (i+1))).ker

theorem unique_central_chief (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hc : pCore 2 G=⊥)
    (hwhole : subspaceCommutator ρ ⊤ ⊤=⊤) (hn : ¬ (⊤:Subgroup G)≤ρ.ker)
    (hmax : ∀ P : Subrepresentation ρ, P=⊤ ∨ P.toSubmodule≤fixedSpace ρ ⊤) :
    HasUniqueCentralChief ρ := by
  have hcoat : IsCoatom (fixedSubrepresentation ρ ⊤) := by
    refine ⟨?_,?_⟩
    · intro he
      apply hn
      intro g hg
      apply LinearMap.ext
      intro v
      have hv : v ∈ fixedSubrepresentation ρ ⊤ := by rw [he]; trivial
      exact hv ⟨g,hg⟩
    · intro P hP
      rcases hmax P with ht | hz
      · exact ht
      · exact ((not_le_of_gt hP) hz).elim
  exact ⟨hcoat,SimpleHeadQuotient.irreducible_quotient_of_isCoatom _ hcoat,
    faithful_fixedQuotient_of_core ρ hf hc,
    fun c n hzero hstop hchief => unique_noncentral_in_flag ρ ⊤ hwhole hn hmax
      c n hzero hstop hchief⟩
end Representation.BinaryOffender
