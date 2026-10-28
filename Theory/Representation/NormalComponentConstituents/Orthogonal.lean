module
public import Theory.Representation.NormalComponentConstituents
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Orthogonal pairing of normal-subgroup constituents

For a faithful irreducible symplectic action, an isotropic constituent of a
normal subgroup pairs nontrivially with an ambient conjugate, since the
conjugates span the whole module. Schur injectivity and the equal dimensions
of conjugates make this pairing an equivariant duality. The two isotropic
summands then form a nondegenerate subspace. Its orthogonal complement is
invariant, as is the orthogonal complement of any nondegenerate constituent.

These are the adapted orthogonal decompositions used in Aschbacher--Smith
G.10.7(3), printed p.359. Semisimplicity of the remaining invariant complement
comes from the normal restriction theorem; no component catalogue is used.
-/

public noncomputable section
open Representation Subgroup Module Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  (B : LinearMap.BilinForm (ZMod 2) V)
  (hpres : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
include hpres

/-- An invariant form pairs two actual subrepresentations as dual representations
of the same actor. -/
@[expose] def bilinearCrossPairing (I J : Subrepresentation ρ) :
    IntertwiningMap I.toRepresentation J.toRepresentation.dual where
  toLinearMap := B.compl₁₂ I.toSubmodule.subtype J.toSubmodule.subtype
  isIntertwining' g := by
    ext v w
    change B (ρ g v.val) w.val = B v.val (ρ g⁻¹ w.val)
    simpa only [ρ.self_inv_apply] using hpres g v.val (ρ g⁻¹ w.val)

/-- Schur injectivity of any nonzero constituent pairing. -/
theorem bilinearCrossPairing_injective (I J : Subrepresentation ρ)
    (hi : I.toRepresentation.IsIrreducible)
    (hne : ∃ v ∈ I.toSubmodule, ∃ w ∈ J.toSubmodule, B v w ≠ 0) :
    Function.Injective (bilinearCrossPairing ρ B hpres I J) := by
  let := hi
  apply (IsIrreducible.injective_or_eq_zero _).resolve_right
  intro hz
  obtain ⟨v,hv,w,hw,hn⟩ := hne
  exact hn (congrArg (fun f : IntertwiningMap I.toRepresentation J.toRepresentation.dual =>
    f ⟨v,hv⟩ ⟨w,hw⟩) hz)

/-- Orthogonal complements of invariant subspaces remain invariant. -/
theorem orthogonal_invariant {H : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : H ≤ subspaceStabilizer ρ I) : H ≤ subspaceStabilizer ρ (B.orthogonal I) := by
  apply le_subspaceStabilizer
  intro g hg w hw v hv
  have hv' := (hI (H.inv_mem hg) v).2 hv
  have he := hpres g (ρ g⁻¹ v) w
  simpa only [ρ.self_inv_apply] using he.trans (hw _ hv')

/-- Two isotropic irreducible subspaces with nonzero invariant pairing form a
nondegenerate subspace. No ambient nondegeneracy is needed for this step. -/
theorem nondegenerate_sup_of_irreducible_pairing
    (halt : B.IsAlt) (I J : Subrepresentation ρ)
    (hi : I.toRepresentation.IsIrreducible) (hj : J.toRepresentation.IsIrreducible)
    (hisoI : ∀ v ∈ I.toSubmodule, ∀ w ∈ I.toSubmodule, B v w = 0)
    (hisoJ : ∀ v ∈ J.toSubmodule, ∀ w ∈ J.toSubmodule, B v w = 0)
    (hne : ∃ v ∈ I.toSubmodule, ∃ w ∈ J.toSubmodule, B v w ≠ 0) :
    (B.restrict (I.toSubmodule ⊔ J.toSubmodule)).Nondegenerate := by
  have hf := bilinearCrossPairing_injective ρ B hpres I J hi hne
  have hg := bilinearCrossPairing_injective ρ B hpres J I hj (by
    obtain ⟨v,hv,w,hw,hn⟩ := hne
    exact ⟨w,hw,v,hv,fun he => hn (halt.isRefl _ _ he)⟩)
  have hl : (B.restrict (I.toSubmodule ⊔ J.toSubmodule)).SeparatingLeft := by
    intro z hz
    obtain ⟨i,hiI,j,hjJ,hij⟩ := Submodule.mem_sup.mp z.property
    have hzeroI : i = 0 := by
      have he : bilinearCrossPairing ρ B hpres I J ⟨i,hiI⟩ =
          bilinearCrossPairing ρ B hpres I J 0 := by
        ext w
        change B i w.val = B 0 w.val
        have hh := hz ⟨w.val,Submodule.mem_sup_right w.property⟩
        change B z.val w.val = 0 at hh
        rw [← hij,map_add,LinearMap.add_apply,hisoJ j hjJ w.val w.property,add_zero] at hh
        exact hh.trans (by simp)
      exact congrArg Subtype.val (hf he)
    have hzeroJ : j = 0 := by
      have he : bilinearCrossPairing ρ B hpres J I ⟨j,hjJ⟩ =
          bilinearCrossPairing ρ B hpres J I 0 := by
        ext w
        change B j w.val = B 0 w.val
        have hh := hz ⟨w.val,Submodule.mem_sup_left w.property⟩
        change B z.val w.val = 0 at hh
        rw [← hij,map_add,LinearMap.add_apply,hisoI i hiI w.val w.property,zero_add] at hh
        exact hh.trans (by simp)
      exact congrArg Subtype.val (hg he)
    apply Subtype.ext
    change z.val = 0
    rw [← hij,hzeroI,hzeroJ,add_zero]
  exact ⟨hl,fun w hw => hl w fun v => halt.isRefl _ _ (hw v)⟩

variable [FiniteDimensional (ZMod 2) V]

/-- A totally isotropic normal-restriction constituent has a conjugate with a
nonzero pairing: otherwise the ambient spanning orbit would be orthogonal to I. -/
theorem IsIrrPlus.exists_conjugate_nonzero_pairing (hi : ρ.IsIrreducible)
    (hnd : B.Nondegenerate) (H : Subgroup G) [H.Normal]
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ H I) :
    ∃ g : G, ∃ v ∈ I, ∃ w ∈ I.map (ρ g⁻¹), B v w ≠ 0 := by
  by_contra! hall
  let R := invariantSubspace ρ H I hI.choose
  let P : Subrepresentation (ρ.comp H.subtype) :=
    ⟨B.orthogonal I, fun g w hw => (orthogonal_invariant ρ B hpres hI.choose g.property w).2 hw⟩
  have hle : (⨆ g : G, conjugateSubrepresentation ρ H R g) ≤ P := by
    apply iSup_le
    intro g w hw v hv
    exact hall g v hv w hw
  rw [iSup_conjugateSubrepresentations_eq_top ρ H hi R
    (hI.irreducible_of_normal_restriction ρ hi H)] at hle
  apply hI.ne_bot ρ
  apply le_bot_iff.mp
  intro v hv
  apply hnd.1 v
  intro w
  exact hle (show w ∈ (⊤ : Subrepresentation (ρ.comp H.subtype)) from by trivial) v hv

/-- An isotropic constituent pairs perfectly with an actual ambient conjugate.
Their sum is nondegenerate and has its literal orthogonal complement. -/
theorem IsIrrPlus.isotropic_conjugate_pair (hi : ρ.IsIrreducible)
    (halt : B.IsAlt) (hnd : B.Nondegenerate) (H : Subgroup G) [H.Normal]
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ H I)
    (hiso : ∀ v ∈ I, ∀ w ∈ I, B v w = 0) :
    ∃ g : G,
      let J := conjugateSubrepresentation ρ H (invariantSubspace ρ H I hI.choose) g
      Disjoint I J.toSubmodule ∧
      Nonempty (Representation.Equiv (invariantSubspace ρ H I hI.choose).toRepresentation
        J.toRepresentation.dual) ∧
      (B.restrict (I ⊔ J.toSubmodule)).Nondegenerate ∧
      IsCompl (I ⊔ J.toSubmodule) (B.orthogonal (I ⊔ J.toSubmodule)) := by
  obtain ⟨g,v,hv,w,hw,hn⟩ := hI.exists_conjugate_nonzero_pairing ρ B hpres hi hnd H
  let R := invariantSubspace ρ H I hI.choose
  let J := conjugateSubrepresentation ρ H R g
  have hirr : R.toRepresentation.IsIrreducible := hI.irreducible_of_normal_restriction ρ hi H
  have hja : IsAtom J := by
    simpa [J] using ((conjugateSubrepresentationOrderIso ρ H g⁻¹).isAtom_iff R).mpr
      ((Subrepresentation.irreducible_iff_isAtom R).mp hirr)
  have hjirr := (Subrepresentation.irreducible_iff_isAtom J).mpr hja
  have hisoJ : ∀ u ∈ J.toSubmodule, ∀ z ∈ J.toSubmodule, B u z = 0 := by
    rintro u ⟨u',hu,rfl⟩ z ⟨z',hz,rfl⟩
    exact (hpres g⁻¹ u' z').trans (hiso u' hu z' hz)
  have hpair : ∃ u ∈ R.toSubmodule, ∃ z ∈ J.toSubmodule, B u z ≠ 0 := ⟨v,hv,w,hw,hn⟩
  have hinj := bilinearCrossPairing_injective (ρ.comp H.subtype) B
    (fun h u z => hpres h u z) R J hirr hpair
  have hdim : finrank (ZMod 2) R.toSubmodule = finrank (ZMod 2) J.toSubmodule :=
    (finrank_map_action ρ I g⁻¹).symm
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using hdim)).mp hinj
  have hnondeg := nondegenerate_sup_of_irreducible_pairing (ρ.comp H.subtype) B
    (fun h u z => hpres h u z) halt R J hirr hjirr hiso hisoJ hpair
  refine ⟨g,?_,⟨(bilinearCrossPairing (ρ.comp H.subtype) B
    (fun h u z => hpres h u z) R J).ofBijective ⟨hinj,hsurj⟩⟩,
    hnondeg,B.isCompl_orthogonal_of_restrict_nondegenerate halt.isRefl hnondeg⟩
  rcases hI.eq_or_disjoint_conjugate_of_normal_restriction ρ hi H g⁻¹ with he | hd
  · exact (hn (hiso v hv w (he ▸ hw))).elim
  · exact hd.symm

/-- The adapted orthogonal decomposition at a chosen constituent: either I
has its orthogonal complement, or an actual conjugate is dual to I and their
nondegenerate sum has its orthogonal complement. Both complements are invariant. -/
theorem IsIrrPlus.orthogonal_alternative (hi : ρ.IsIrreducible)
    (halt : B.IsAlt) (hnd : B.Nondegenerate) (H : Subgroup G) [H.Normal]
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ H I) :
    ((B.restrict I).Nondegenerate ∧ IsCompl I (B.orthogonal I) ∧
      H ≤ subspaceStabilizer ρ (B.orthogonal I)) ∨
    ∃ g : G,
      let J := conjugateSubrepresentation ρ H (invariantSubspace ρ H I hI.choose) g
      IsIrrPlus ρ H J.toSubmodule ∧
      (∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∧
      Disjoint I J.toSubmodule ∧
      Nonempty (Representation.Equiv (invariantSubspace ρ H I hI.choose).toRepresentation
        J.toRepresentation.dual) ∧
      (B.restrict (I ⊔ J.toSubmodule)).Nondegenerate ∧
      IsCompl (I ⊔ J.toSubmodule) (B.orthogonal (I ⊔ J.toSubmodule)) ∧
      H ≤ subspaceStabilizer ρ (B.orthogonal (I ⊔ J.toSubmodule)) := by
  rcases hI.isotropic_or_nondegenerate_of_normal_restriction ρ hi H B halt hpres with hiso | hnondeg
  · right
    obtain ⟨g,hdis,he,hndsup,hcompl⟩ := hI.isotropic_conjugate_pair ρ B hpres hi halt hnd H hiso
    have hgn : g⁻¹ ∈ normalizer (H : Set G) := by rw [H.normalizer_eq_top]; trivial
    have hJ := hI.map_normalizer ρ hgn
    refine ⟨g,hJ,hiso,hdis,he,hndsup,hcompl,?_⟩
    exact orthogonal_invariant ρ B hpres
      (subspaceStabilizer_sup ρ hI.choose hJ.choose)
  · exact Or.inl ⟨hnondeg,B.isCompl_orthogonal_of_restrict_nondegenerate halt.isRefl hnondeg,
      orthogonal_invariant ρ B hpres hI.choose⟩

omit hpres in
/-- Every invariant summand or orthogonal complement in a normal restriction
is semisimple for its literal restricted action. -/
theorem subrepresentation_semisimple_of_normal_restriction
    (hi : ρ.IsIrreducible) (H : Subgroup G) [H.Normal]
    (J : Subrepresentation (ρ.comp H.subtype)) : IsSemisimpleRepresentation J.toRepresentation := by
  let := NormalConstituentDisplacement.restriction_semisimple ρ hi H
  let f : IntertwiningMap J.toRepresentation (ρ.comp H.subtype) :=
    { toLinearMap := J.toSubmodule.subtype
      isIntertwining' g := by ext v; rfl }
  let fm := IntertwiningMap.equivLinearMapAsModule J.toRepresentation (ρ.comp H.subtype) f
  apply (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
  exact IsSemisimpleModule.of_injective fm (by
    intro v w he
    apply Subtype.ext
    exact he)

end Representation.BinaryOffender
