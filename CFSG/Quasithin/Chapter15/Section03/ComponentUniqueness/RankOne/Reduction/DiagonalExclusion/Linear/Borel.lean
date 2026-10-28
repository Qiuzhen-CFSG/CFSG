module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Local
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.BorelPlacement.SylowInvariance

/-!
# The invariant linear Borel in the S₃ branch

Restrict the supplied Sylow two-subgroup to the relative component and map it
through the supplied equivalence L/O₂(L) ≃ PSL₃(F). Its full preimage is S ∩ L.
The solvable action of Y₊S contains the inner image of this Sylow. Intrinsic
PSL₃ geometry therefore makes Y₊S preserve it and its normalizer. The full
Borel preimage has characteristic two, so 15.3.33(1) places it in M ∩ I.

All coordinates and the full two-kernel are retained, including for central
two-covers of PSL₃(4). Only the general solvable-action transfer is reused from
`SylowInvariance`; none of its rank-two source wrappers is instantiated.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the paragraph
between 15.3.43(d) and (e), printed p.1139; compare pp.1135--1136.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
open Candidates.LinearCore Candidates.LinearCore.MatrixImage
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L : Subgroup G}

/-- The actual Sylow restricted to the relative component. -/
theorem LocalSetup.linear_component_sylow (h : LocalSetup Yplus S M I L) :
    ∃ Q : Sylow 2 L, (Q : Subgroup L) = S.subgroupOf L := by
  obtain ⟨P, hP⟩ := h.sylow
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_subnormal (L.subgroupOf I) h.component.1
  let eL := subgroupOfEquivOfLe h.component_le
  refine ⟨Q.mapSurjective (f := eL.toMonoidHom) eL.surjective, ?_⟩
  change (Q : Subgroup (L.subgroupOf I)).map eL.toMonoidHom = _
  rw [hQ, ← hP]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, ha, rfl⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨⟨a, ?_⟩, ha, ?_⟩
    · change (a : G) ∈ L
      change (a : G) = (x : G) at he
      exact he.symm ▸ x.property
    · exact Subtype.ext he

/-- The full two-core is retained in the preimage of the specified Sylow. -/
theorem LocalSetup.linear_sylow_preimage (h : LocalSetup Yplus S M I L)
    {F : Type*} [Field F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (P : Sylow 2 PSL(3,F))
    (hP : (P : Subgroup PSL(3,F)) = (S.subgroupOf L).map (quotientMap e)) :
    (P : Subgroup PSL(3,F)).comap (quotientMap e) = S.subgroupOf L := by
  obtain ⟨Q, hQ⟩ := h.linear_component_sylow
  rw [hP, comap_map_eq_self]
  rw [quotientMap_ker, ← hQ]
  exact fitting_pCore_le_sylow Q

/-- The projective Borel pulls back to the literal normalizer in L. -/
theorem LocalSetup.linear_borel_preimage (h : LocalSetup Yplus S M I L)
    {F : Type*} [Field F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (P : Sylow 2 PSL(3,F))
    (hP : (P : Subgroup PSL(3,F)) = (S.subgroupOf L).map (quotientMap e)) :
    ((normalizer (P : Set PSL(3,F))).comap (quotientMap e)).map L.subtype =
      L ⊓ normalizer (S ⊓ L : Subgroup G) := by
  change ((normalizer ((P : Subgroup PSL(3,F)) : Set PSL(3,F))).comap
    (quotientMap e)).map L.subtype = _
  rw [comap_normalizer_eq_of_surjective (P : Subgroup PSL(3,F))
    (quotientMap_surjective e), h.linear_sylow_preimage e P hP]
  have he : normalizer (S.subgroupOf L : Set L) =
      (normalizer (S ⊓ L : Subgroup G)).subgroupOf L := by
    rw [subgroupOf_normalizer_eq (inf_le_right : S ⊓ L ≤ L)]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩
  rw [he, subgroupOf_map_subtype, inf_comm]

/-- Construct the invariant characteristic-two Borel and place it using 15.3.33(1). -/
theorem LocalSetup.linear_borel (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S)
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (heven : Even n) (hcard : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F)) :
    Yplus ⊔ S ≤ normalizer (L ⊓ normalizer (S ⊓ L : Subgroup G) : Subgroup G) ∧
    generalizedFitting (L ⊓ normalizer (S ⊓ L : Subgroup G) : Subgroup G) =
      pCore 2 (L ⊓ normalizer (S ⊓ L : Subgroup G) : Subgroup G) ∧
    L ⊓ normalizer (S ⊓ L : Subgroup G) ≤ M ⊓ I := by
  obtain ⟨Q, hQ⟩ := h.sylow
  obtain ⟨P, hP⟩ := quotient_sylow h.component_le h.component.1 Q hQ e
  have hinv : Yplus ⊔ S ≤ normalizer (S ⊓ L : Subgroup G) :=
    sylow_preimage_invariant_of_solvable_overgroups h.join_solvable
      (h.join_normalizes horbit) le_sup_right e P hP (h.linear_sylow_preimage e P hP)
      (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer
        F hn heven hcard P)
  have hB := h.linear_borel_preimage e P hP
  have hchar : generalizedFitting (L ⊓ normalizer (S ⊓ L : Subgroup G) : Subgroup G) =
      pCore 2 (L ⊓ normalizer (S ⊓ L : Subgroup G) : Subgroup G) := by
    rw [← hB]
    apply Matrix.PSL3.LinearThree.BorelStructure.sylowNormalizer_preimage_image_characteristicTwo
      F hn hcard (quotientMap e) (quotientMap_surjective e) _ P L.subtype L.subtype_injective
    rw [quotientMap_ker]
    exact pCore_isPGroup
  have hnorm := le_normalizer_inf (h.join_normalizes horbit)
    (hinv.trans (normalizer ((S ⊓ L : Subgroup G) : Set G)).le_normalizer)
  exact ⟨hnorm, hchar, h.characteristic_two_containment _
    (inf_le_left.trans horbit.le) hnorm hchar⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
