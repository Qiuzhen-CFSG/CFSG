module
public import Theory.Representation.NormalConstituentDisplacement.FixedLine
public import Theory.Representation.BinaryOffender.FaithfulInvariantSection

/-!
# Small displacement bounds homogeneous multiplicity

A nonidentity actor whose binary displacement has rank at most two preserves
every simple normal constituent of degree at least three. It cannot centralize
the normal subgroup. Faithfulness on each constituent therefore makes each
restricted displacement nonzero. Three independent constituents would give
three independent displacement directions, a contradiction.

The result is the numerical part of Aschbacher--Smith G.10.16(4), printed
pp.363--364. Its actual marked terminal consumer is
ComponentCatalogueMarkedKernelHigher in Chapter14.Section03. No irreducibility
of the whole restricted module or preservation of actor rank in a quotient is
assumed.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace Representation.NormalConstituentDisplacement
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private theorem sup_submodule (ρ : Representation (ZMod 2) G V)
    (A B : Subrepresentation ρ) :
    (A ⊔ B).toSubmodule = A.toSubmodule ⊔ B.toSubmodule := by
  let e : Subrepresentation ρ ≃o Submodule (ZMod 2)[G] ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have h := congrArg (fun P : Submodule (ZMod 2)[G] ρ.asModule => P.restrictScalars (ZMod 2))
    (e.map_sup A B)
  rw [Submodule.restrictScalars_sup] at h
  exact h

private theorem compl_submodules (ρ : Representation (ZMod 2) G V)
    (A B : Subrepresentation ρ) (h : IsCompl A B) :
    IsCompl A.toSubmodule B.toSubmodule := by
  refine ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule h.inf_eq_bot),
    codisjoint_iff.mpr ?_⟩
  rw [← sup_submodule, h.sup_eq_top]
  rfl

private theorem displacement_le (ρ : Representation (ZMod 2) G V) (a : G)
    (A : Submodule (ZMod 2) V) (hA : A.map (ρ a) = A) :
    A.map (ρ a - LinearMap.id) ≤ A := by
  rintro _ ⟨v,hv,rfl⟩
  exact A.sub_mem (hA ▸ Submodule.mem_map_of_mem hv) hv

variable [FiniteDimensional (ZMod 2) V]

private theorem displacement_rank_sup (ρ : Representation (ZMod 2) G V) (a : G)
    (A B : Submodule (ZMod 2) V) (hAB : Disjoint A B)
    (hA : A.map (ρ a) = A) (hB : B.map (ρ a) = B) :
    Module.finrank (ZMod 2) (A.map (ρ a - LinearMap.id)) +
      Module.finrank (ZMod 2) (B.map (ρ a - LinearMap.id)) =
        Module.finrank (ZMod 2) ((A ⊔ B).map (ρ a - LinearMap.id)) := by
  have hd := hAB.mono (displacement_le ρ a A hA) (displacement_le ρ a B hB)
  have hr := (A.map (ρ a - LinearMap.id)).finrank_sup_add_finrank_inf_eq
    (B.map (ρ a - LinearMap.id))
  rw [hd.eq_bot,finrank_bot,add_zero,← Submodule.map_sup] at hr
  exact hr.symm

/-- The numerical part of G.10.16(4): a nonidentity actor with displacement
at most two has at most two copies of a faithful normal constituent of degree
at least three. Faithfulness is on each actual constituent. -/
theorem finrank_le_twice_of_small_displacement
    (ρ : Representation (ZMod 2) G V) (hρ : ρ.IsIrreducible)
    (hf : Function.Injective ρ) (H : Subgroup G) [H.Normal]
    (d : ℕ) (hd : 2 < d)
    (hdegree : ∀ J : Subrepresentation (ρ.comp H.subtype),
      J.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) J.toSubmodule = d)
    (hfaith : ∀ J : Subrepresentation (ρ.comp H.subtype),
      J.toRepresentation.IsIrreducible → Function.Injective J.toRepresentation)
    (a : G) (ha : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2) :
    Module.finrank (ZMod 2) V ≤ 2 * d := by
  have hsmall (J : Subrepresentation (ρ.comp H.subtype))
      (hJ : J.toRepresentation.IsIrreducible) :
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) <
        Module.finrank (ZMod 2) J.toSubmodule := by rw [hdegree J hJ]; omega
  have hp : 0 < Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply ha
    apply hf
    rw [map_one]
    ext v
    have hv : ρ a v - v ∈ LinearMap.range (ρ a - LinearMap.id) := ⟨v,rfl⟩
    rw [Submodule.finrank_eq_zero.mp hz] at hv
    exact sub_eq_zero.mp hv
  have hnc : a ∉ centralizer (H : Set G) := by
    intro hc
    apply not_le_centralizer_of_small_displacement ρ H a hsmall hp
    intro b hb c hc'
    rw [Set.mem_singleton_iff.mp hc']
    exact ((mem_centralizer_iff.mp hc) b hb).symm
  have hi (J : Subrepresentation (ρ.comp H.subtype))
      (hJ : J.toRepresentation.IsIrreducible) :
      J.toSubmodule.map (ρ a) = J.toSubmodule :=
    map_constituent_eq_self_of_displacement_lt ρ H a J hJ (hsmall J hJ)
  have hpos (J : Subrepresentation (ρ.comp H.subtype))
      (hJ : J.toRepresentation.IsIrreducible) :
      0 < Module.finrank (ZMod 2) (J.toSubmodule.map (ρ a - LinearMap.id)) := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hnc
    have hs : H ≤ subspaceStabilizer ρ J.toSubmodule :=
      le_subspaceStabilizer ρ _ (fun b hb v hv => J.apply_mem_toSubmodule ⟨b,hb⟩ hv)
    apply centralizes_of_fixes_faithful_section ρ H J.toSubmodule hs
    · intro b hb hh
      have he : J.toRepresentation ⟨b,hb⟩ = J.toRepresentation 1 := by
        rw [map_one]
        ext v
        exact hh v v.property
      exact congrArg Subtype.val (hfaith J hJ he)
    · exact le_normalizer_of_normal (mem_top _)
    · intro v hv
      have hm := Submodule.mem_map_of_mem (f := ρ a - LinearMap.id) hv
      rw [Submodule.finrank_eq_zero.mp hz] at hm
      exact sub_eq_zero.mp hm
  let := hρ
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨I,hI⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp H.subtype)
  by_cases hItop : I = ⊤
  · have he := hdegree I hI
    rw [hItop] at he
    change Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) = d at he
    rw [finrank_top] at he
    omega
  let : IsSemisimpleModule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype)) :=
    restriction_semisimple ρ hρ H
  let e : Subrepresentation (ρ.comp H.subtype) ≃o
      Submodule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype)) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  let : ComplementedLattice (Subrepresentation (ρ.comp H.subtype)) := e.symm.complementedLattice
  obtain ⟨C,hC⟩ := exists_isCompl I
  have hCne : C ≠ ⊥ := by intro hz; apply hItop; simpa only [hz,sup_bot_eq] using hC.sup_eq_top
  obtain ⟨J,hJa,hJC⟩ := (eq_bot_or_exists_atom_le C).resolve_left hCne
  have hJ := (Subrepresentation.irreducible_iff_isAtom J).mpr hJa
  have hIJ : Disjoint I.toSubmodule J.toSubmodule :=
    (compl_submodules (ρ.comp H.subtype) I C hC).disjoint.mono_right hJC
  have hsum := displacement_rank_sup ρ a I.toSubmodule J.toSubmodule hIJ (hi I hI) (hi J hJ)
  have hpI := hpos I hI
  have hpJ := hpos J hJ
  have hIJtop : I ⊔ J = ⊤ := by
    obtain ⟨D,hD⟩ := exists_isCompl (I ⊔ J)
    by_contra hn
    have hDne : D ≠ ⊥ := by intro hz; apply hn; simpa only [hz,sup_bot_eq] using hD.sup_eq_top
    obtain ⟨K,hKa,hKD⟩ := (eq_bot_or_exists_atom_le D).resolve_left hDne
    have hK := (Subrepresentation.irreducible_iff_isAtom K).mpr hKa
    have hIK : Disjoint (I.toSubmodule ⊔ J.toSubmodule) K.toSubmodule := by
      rw [← sup_submodule]
      exact (compl_submodules (ρ.comp H.subtype) (I ⊔ J) D hD).disjoint.mono_right hKD
    have hsIJ : (I.toSubmodule ⊔ J.toSubmodule).map (ρ a) = I.toSubmodule ⊔ J.toSubmodule := by
      rw [Submodule.map_sup,hi I hI,hi J hJ]
    have hsumK := displacement_rank_sup ρ a (I.toSubmodule ⊔ J.toSubmodule)
      K.toSubmodule hIK hsIJ (hi K hK)
    have hpK := hpos K hK
    have hb := Submodule.finrank_mono
      (Submodule.map_mono (f := ρ a - LinearMap.id)
        (show I.toSubmodule ⊔ J.toSubmodule ⊔ K.toSubmodule ≤ ⊤ from le_top))
    rw [Submodule.map_top] at hb
    omega
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq I.toSubmodule J.toSubmodule
  rw [hIJ.eq_bot,finrank_bot,add_zero,← sup_submodule,hIJtop] at hdim
  change Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) = _ at hdim
  rw [finrank_top,hdegree I hI,hdegree J hJ] at hdim
  omega
end Representation.NormalConstituentDisplacement
