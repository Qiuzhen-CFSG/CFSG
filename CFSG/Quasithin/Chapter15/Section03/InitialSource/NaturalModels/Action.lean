module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.NaturalModels
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.ActionComparison
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.DefinitePlanes


/-!
# Original source actions on the actual local module

The quotient action coordinates are lifted through the given centralizer
quotient and actual subgroup inclusion. The full standard orthogonal
action then gives the precise matrix wreath action through the already
proved quadratic-coordinate comparison. A standard definite plane is
pulled back internally; no plane marking is assumed.

The final source consumer applies both alternatives to the original
localModule, deriving reducedness and transporting noncentral J(T).
The rank-two alternative and the literal NaturalOrthogonalAction are both
retained for the subsequent 15.1.3 branch dispatch.

Source: Aschbacher–Smith, 14.1.7, printed p.977, and the natural
action boundary of 15.1.3/15.3, printed pp.1086 and 1121–1122.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
variable {G : Type*} [Group G]

theorem standardAction_of_quotient_coordinates
    (M : Subgroup G) (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (c : Additive U ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
    (e : (M ⧸ centralizer (U : Set M)) ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup)
    (hc : ∀ g v, c (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g v) = (e g).val (c v)) :
    Nonempty (OrthogonalFourBinary.NaturalAction (U.map M.subtype) M) := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let eU := U.equivMapOfInjective M.subtype M.subtype_injective
  let a : U.map M.subtype ≃* Multiplicative OrthogonalFourBinary.Space :=
    eU.symm.trans c.toAddEquiv.toMultiplicativeRight
  refine ⟨⟨a, e.toMonoidHom.comp q, e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩⟩
  intro m v
  have hpre : c.symm ((e (q m)).val (c (Additive.ofMul (eU.symm v)))) =
      ρ (q m) (Additive.ofMul (eU.symm v)) := by
    apply c.injective
    rw [c.apply_symm_apply, hc]
  change (((c.symm ((e (q m)).val (c (Additive.ofMul (eU.symm v))))).toMul : M) : G) =
    (m : G) * (v : G) * (m : G)⁻¹
  rw [hpre]
  have hv : (((eU.symm v : U) : M) : G) = (v : G) :=
    congrArg Subtype.val (eU.apply_symm_apply v)
  rw [NormalElementaryQuotient.representation_apply]
  change (m : G) * (((eU.symm v : U) : M) : G) * (m : G)⁻¹ = _
  rw [hv]

/-- Existing full quadratic/wreath comparison supplies the literal Section 15.3 action. -/
theorem naturalOrthogonalAction_of_standard [Finite G]
    {M V : Subgroup G} (d : OrthogonalFourBinary.NaturalAction V M) :
    Nonempty (NaturalOrthogonalAction M V) := by
  let := TerminalSourceEndgame.OriginalSource.standard_elementary d
  let B := (OrthogonalFourBinary.SylowGeometry.definitePlane false).comap d.coordinates.toMonoidHom
  let P := B.map V.subtype
  have hPV : P ≤ V := map_subtype_le B
  have hPc : Nat.card P = 4 := by
    rw [show P = B.map V.subtype from rfl, card_map_of_injective V.subtype_injective]
    have he := Nat.card_congr (B.equivMapOfInjective d.coordinates.toMonoidHom d.coordinates.injective).toEquiv
    rw [show B.map d.coordinates.toMonoidHom = OrthogonalFourBinary.SylowGeometry.definitePlane false from
      map_comap_eq_self_of_surjective d.coordinates.surjective _] at he
    exact he.trans (OrthogonalFourBinary.SylowGeometry.definitePlane_card false)
  have hP : ∀ p : P, p ≠ 1 → ¬ d.singular ⟨p, hPV p.property⟩ := by
    intro p hp
    obtain ⟨v, hv, hvp⟩ := p.property
    have hvne : v ≠ 1 := by
      intro he
      apply hp
      apply Subtype.ext
      rw [← hvp, he]
      rfl
    have hcv : d.coordinates v ≠ 1 :=
      fun he => hvne (d.coordinates.injective (he.trans d.coordinates.map_one.symm))
    have he : (⟨(p : G), hPV p.property⟩ : V) = v := Subtype.ext hvp.symm
    rw [OrthogonalFourBinary.NaturalAction.singular, he]
    exact (by decide +kernel : ∀ x : OrthogonalFourBinary.Space,
      x.2 = 0 → x ≠ 0 → OrthogonalFourBinary.form x ≠ 0)
      (d.coordinates v).toAdd hv hcv
  have hdef := TerminalSourceEndgame.OriginalSource.definite_of_standard d hPV hPc hP
  obtain ⟨k⟩ := TerminalSourceEndgame.OriginalSource.coordinates_from_standard d hdef
  exact ⟨k.action⟩

universe u

/-- The original reduced module yields the literal Section 15.3 orthogonal action. -/
theorem reduced_natural_action_from_source
    {G : Type u} [Group G] [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) ≤
      centralizer (U : Set M)) :
    letI := hU.normal
    letI := hU.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (∃ (c : Additive U ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : (M ⧸ centralizer (U : Set M)) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      ∀ g v, c (ρ g v) = Representation.specialLinearNatural 2 (e g) (c v)) ∨
    Nonempty (NaturalOrthogonalAction M (U.map M.subtype)) := by
  let := hU.normal
  let := hU.elementary
  rcases reduced_natural_models_from_source hA hC hG T hempty hM hunique hcase U hU hJ with h | h
  · exact Or.inl h
  · obtain ⟨c, e, hc⟩ := h
    obtain ⟨d⟩ := standardAction_of_quotient_coordinates M U c e hc
    exact Or.inr (naturalOrthogonalAction_of_standard d)

/-- Literal localModule consumer of the original 14.1.7 natural-action alternatives. -/
theorem local_natural_action_from_source
    {G : Type u} [Group G] [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    let hH : M ∈ Chapter1.HOver G (T : Set G) :=
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
    let U := (localModule T M).subgroupOf M
    letI := (localModule_reduced_from_source hG T hH).normal
    letI := (localModule_reduced_from_source hG T hH).elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (∃ (c : Additive U ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : (M ⧸ centralizer (U : Set M)) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      ∀ g v, c (ρ g v) = Representation.specialLinearNatural 2 (e g) (c v)) ∨
    Nonempty (NaturalOrthogonalAction M (localModule T M)) := by
  let hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
  let U := (localModule T M).subgroupOf M
  have hU := localModule_reduced_from_source hG T hH
  let := hU.normal
  let := hU.elementary
  have hVM : localModule T M ≤ M := localModule_le T hM.2
  let S := T.subtype hM.2
  have hJS : ¬ elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    intro h
    apply hJ
    have he : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
      simp only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hM.2]
    intro x hx v hv
    obtain ⟨a, ha, rfl⟩ := he.symm ▸ hx
    exact congrArg M.subtype (h ha ⟨v, hVM hv⟩ hv)
  rcases reduced_natural_action_from_source hA hC hG T hempty hM hunique hcase U hU hJS with h | h
  · exact Or.inl h
  · right
    have he : U.map M.subtype = localModule T M := map_subgroupOf_eq_of_le hVM
    simpa only [he] using h


end CFSG.Quasithin.Chapter15.Section03.InitialSource
