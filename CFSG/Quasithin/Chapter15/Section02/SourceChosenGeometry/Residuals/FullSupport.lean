module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SupportAction

/-!
# Excluding the literal proper-support alternative

The O^{3'} residual of the intersection is 2-perfect. Once it centralizes
Z, the prepared seed-residual theorem forces it to centralize the chosen
module. Thus the intersection has image of order prime to three on that
module. The proper-support alternative gives image S₃ × S₃ and intersection
index three, which is impossible: its image would have order 12 or 36.

The final consumer retains just the coprime-index premise for Kc in Mc;
it supplies the residual equality, excludes the actual `SourceCases.Proper`
branch, and builds the original commutator-plane geometry.

Source: Aschbacher--Smith 15.2.12(4)--(5), printed p.1111, combined
manuscript of 1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc V H B : Subgroup G}
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The seed-residual theorem transfers centralization of Z to the chosen module. -/
theorem residual_centralizes_chosen (h : ChosenSmallSource T M Mc V)
    (hc : threePrimeResidual (M ⊓ Mc) ≤
      M ⊓ centralizer (centralInvolutions T : Set G)) :
    threePrimeResidual (M ⊓ Mc) ≤ centralizer (V : Set G) := by
  let J := M ⊓ Mc
  let C := M ⊓ centralizer (centralInvolutions T : Set G)
  let R := primeToResidual 3 J
  let A := R.map J.subtype
  have hAC : A ≤ C := by simpa only [threePrimeResidual_eq] using hc
  let e := R.equivMapOfInjective J.subtype J.subtype_injective
  have hp : IsPPerfect 2 A :=
    (isPPerfect_primeToResidual (G := J) 3 2 (by decide)).of_surjective
      e.toMonoidHom e.surjective
  let a := subgroupOfEquivOfLe hAC
  have hp' : IsPPerfect 2 (A.subgroupOf C) :=
    hp.of_surjective a.symm.toMonoidHom a.symm.surjective
  have hm := map_mono (f := C.subtype) (le_pResidual_of_isPPerfect _ hp')
  rw [map_subgroupOf_eq_of_le hAC] at hm
  rw [threePrimeResidual_eq]
  exact hm.trans h.prepared.seed_residual

/-- The actual intersection action has order prime to three. -/
theorem intersection_image_three_free (h : ChosenSmallSource T M Mc V)
    (hc : threePrimeResidual (M ⊓ Mc) ≤
      M ⊓ centralizer (centralInvolutions T : Set G)) :
    Nat.Coprime 3 (Nat.card (((M ⊓ Mc).subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict)) := by
  let J := M ⊓ Mc
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let g := f.comp (inclusion (show J ≤ M from inf_le_left))
  have hg : primeToResidual 3 J ≤ g.ker := by
    intro x hx
    have hxC := residual_centralizes_chosen h hc
      (show (x : G) ∈ threePrimeResidual J by
        rw [threePrimeResidual_eq]; exact mem_map_of_mem J.subtype hx)
    change inclusion inf_le_left x ∈ f.ker
    rw [MonoidHom.ker_rangeRestrict, actionHom_ker]
    exact hxC
  have hi : Nat.Coprime 3 g.ker.index :=
    (primeToResidual_index_coprime (G := J) 3).coprime_dvd_right (index_dvd_of_le hg)
  rw [index_ker] at hi
  simpa only [g, MonoidHom.range_comp, inclusion_range] using hi

private theorem no_index_three_image_thirtysix (h : ChosenSmallSource T M Mc V)
    (hc : threePrimeResidual (M ⊓ Mc) ≤
      M ⊓ centralizer (centralInvolutions T : Set G))
    (hi : (M ⊓ Mc).relIndex M = 3)
    (hd : Nat.card (internalActionImage M V h.prepared.normalized) = 36) : False := by
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let A := ((M ⊓ Mc).subgroupOf M).map f
  have hAi : A.index ∣ 3 := by
    rw [← hi]
    exact ((M ⊓ Mc).subgroupOf M).index_map_dvd
      (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have hcop := intersection_image_three_free h hc
  have hm := A.card_mul_index
  change Nat.card A * A.index = Nat.card (internalActionImage M V h.prepared.normalized) at hm
  rw [hd] at hm
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hAi with he | he
  · rw [he, mul_one] at hm
    have ha : Nat.card A = 36 := hm
    change Nat.Coprime 3 (Nat.card A) at hcop
    norm_num [ha] at hcop
  · rw [he] at hm
    have ha : Nat.card A = 12 := by omega
    change Nat.Coprime 3 (Nat.card A) at hcop
    norm_num [ha] at hcop

omit [Finite G] in
private theorem action_card_congr {M V W : Subgroup G}
    (hMV : M ≤ normalizer (V : Set G)) (hMW : M ≤ normalizer (W : Set G))
    (he : V = W) : Nat.card (internalActionImage M V hMV) =
      Nat.card (internalActionImage M W hMW) := by
  subst W
  rfl

/-- Exclude the literal proper-support disjunct in `ChosenSmallSource.chosen`. -/
theorem not_proper_of_intersection_centralizes (h : ChosenSmallSource T M Mc V)
    (hc : threePrimeResidual (M ⊓ Mc) ≤
      M ⊓ centralizer (centralInvolutions T : Set G)) :
    letI := localModule_elementary_from_source h.ambient T
      ⟨Chapter1.mem_H_of_isTwoLocal h.maximal.1.1.1, h.maximal.1.2⟩
    ¬ ∃ U : Submodule (ZMod 2) (Additive (localModule T M)),
      SourceCases.Proper T M Mc (localModule T M)
        (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U ∧
      V = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype := by
  let := localModule_elementary_from_source h.ambient T
    ⟨Chapter1.mem_H_of_isTwoLocal h.maximal.1.1.1, h.maximal.1.2⟩
  rintro ⟨U,hU,hV⟩
  obtain ⟨_,_,_,hstable,_,_,_,_,himage,_,hindex,_⟩ := hU
  apply no_index_three_image_thirtysix h hc hindex
  have hnorm : M ≤ normalizer (((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map
      (localModule T M).subtype) : Set G) := hV ▸ h.prepared.normalized
  let a := supportActionEquiv M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    U hstable hnorm
  have he : Nat.card (internalActionImage M V h.prepared.normalized) =
      Nat.card (subspaceActionImage
        (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U) := by
    exact (action_card_congr h.prepared.normalized hnorm hV).trans
      (Nat.card_congr a.toEquiv)
  rw [he, Nat.card_congr himage.some.toEquiv]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm]

/-- The chosen module is the full local module once the intersection residual centralizes Z. -/
theorem full_of_intersection_centralizes (h : ChosenSmallSource T M Mc V)
    (hc : threePrimeResidual (M ⊓ Mc) ≤
      M ⊓ centralizer (centralInvolutions T : Set G)) : V = localModule T M := by
  let := localModule_elementary_from_source h.ambient T
    ⟨Chapter1.mem_H_of_isTwoLocal h.maximal.1.1.1, h.maximal.1.2⟩
  exact h.chosen.resolve_right (not_proper_of_intersection_centralizes h hc)

/-- The remaining index calculation implies original 15.2.12(5). -/
theorem ResidualInput.full_of_index {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B)
    (hi : Nat.Coprime 3 ((partnerSpan H Mc).subgroupOf Mc).index) :
    V = localModule T M :=
  full_of_intersection_centralizes h
    (d.intersection_centralizes (d.residual_equality_of_index hi))

/-- Application to the parent task, using the actual commutator plane. -/
theorem ResidualInput.geometry_of_index {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B)
    (hi : Nat.Coprime 3 ((partnerSpan H Mc).subgroupOf Mc).index) :
    ChosenPlaneGeometry h H ⁅V,B⁆ := d.geometry_of_full (d.full_of_index hi)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
