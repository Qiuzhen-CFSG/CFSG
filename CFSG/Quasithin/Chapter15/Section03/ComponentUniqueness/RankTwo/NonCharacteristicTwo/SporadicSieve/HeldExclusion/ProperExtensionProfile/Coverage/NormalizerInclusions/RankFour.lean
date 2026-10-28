module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.Representatives
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.NormalizerInclusions.Middle.Data
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Row12.UpperBound
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders

/-!
# The full inner normalizer of the fourth outer Held row

The existing pure-Sylow conjugator sends catalogue row 12 to the literal
four-word row in `Coverage.Representatives`. Both inclusions are certified by
word identities on Held's faithful four-point base, using existing checked
permutation tables. Transporting the already proved row-12 normalizer bound
therefore bounds the FULL ambient normalizer by 9216.

Separate conjugation identities show that each of the two odd and four even
published pair generators normalizes the row. Their actual join has certified
order 9216, so the lower inclusion and upper bound give equality. No simplicity,
order, automorphism realization, or additional coverage premise is assumed.

Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
the unchanged ATLAS HeG1-p2058B0 words. The reproducible discovery calculation
is in `RankFour/source/discover.py`; every identity used here is kernel checked.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions.RankFour
open CoverageData
open Held.LocalPairs.PairCoverage.LocalActions
open RepresentativeImages.InnerImages

private abbrev Catalogue := Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ambient

private def genWord (i : Fin 4) : List ℤ := ((rowWords 3)[i.val]?).getD []
private def gen (i : Fin 4) : Held.He := word (genWord i)
private def perm (i : Fin 4) : Equiv.Perm (Fin 2058) := Middle.tableWord (genWord i)
private theorem perm_eq (i : Fin 4) : perm i = Held.representation (gen i) :=
  Middle.tableWord_eq _

private theorem heldRow_eq_closure : heldRow 3 = closure (Set.range gen) := by
  have hwords : rowWords 3 = List.ofFn genWord := by decide +kernel
  rw [heldRow, row, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    rw [hwords] at hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨word (genWord i), ⟨genWord i, by
      rw [hwords]; exact List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩, rfl⟩

private theorem gen_mem (i : Fin 4) : gen i ∈ heldRow 3 := by
  rw [heldRow_eq_closure]
  exact subset_closure (Set.mem_range_self i)

private def product (is : List (Fin 4)) : Held.He := (is.map gen).prod
private def permProduct (is : List (Fin 4)) : Equiv.Perm (Fin 2058) := (is.map perm).prod
private theorem permProduct_eq (is : List (Fin 4)) :
    permProduct is = Held.representation (product is) := by
  simp only [product, permProduct, map_list_prod, List.map_map, Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  exact perm_eq i
private theorem product_mem (is : List (Fin 4)) : product is ∈ heldRow 3 := by
  apply list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact gen_mem i

private def actor : Fin 6 → Held.He :=
  Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.pairGenerator false 0
private def actorPerm : Fin 6 → Equiv.Perm (Fin 2058)
  | 0 => RepresentativeImages.Pair00.odd0
  | 1 => RepresentativeImages.Pair00.odd1
  | 2 => Middle.tableGen 0
  | 3 => Middle.tableGen 1
  | 4 => Middle.tableGen 2
  | 5 => Middle.tableGen 3
private theorem actorPerm_eq (i : Fin 6) : actorPerm i = Held.representation (actor i) := by
  fin_cases i
  · exact RepresentativeImages.Pair00.odd0_eq
  · exact RepresentativeImages.Pair00.odd1_eq
  · exact Middle.tableGen_eq 0
  · exact Middle.tableGen_eq 1
  · exact Middle.tableGen_eq 2
  · exact Middle.tableGen_eq 3

private def conjugateWords (a : Fin 6) (i : Fin 4) : List (Fin 4) :=
  (([[[0, 2], [1, 3], [0], [1]], [[0, 1], [0], [2, 3], [2]],
    [[0, 1], [1], [2, 3], [3]], [[0, 1, 2, 3], [1, 3], [2, 3], [3]],
    [[0], [1], [2], [3]], [[0], [1], [2], [3]]] : List (List (List (Fin 4))))[a.val]?.getD [])[i.val]?.getD []

set_option maxRecDepth 8192 in
private theorem conjugation_check : ∀ a : Fin 6, ∀ i : Fin 4, ∀ x : Fin 4,
    (actorPerm a * perm i * (actorPerm a)⁻¹) ⟨x.val, by omega⟩ =
      permProduct (conjugateWords a i) ⟨x.val, by omega⟩ := by
  decide +kernel

private theorem conjugation (a : Fin 6) (i : Fin 4) :
    actor a * gen i * (actor a)⁻¹ = product (conjugateWords a i) := by
  apply Held.eq_of_four_point_images
  simpa only [actorPerm_eq, perm_eq, permProduct_eq, map_mul, map_inv] using
    conjugation_check a i

private theorem actor_normalizes (a : Fin 6) :
    actor a ∈ normalizer (heldRow 3 : Set Held.He) := by
  apply Subgroup.mem_normalizer_fintype
  change heldRow 3 ≤ (heldRow 3).comap (MulAut.conj (actor a)).toMonoidHom
  rw [heldRow_eq_closure, closure_le]
  rintro _ ⟨i, rfl⟩
  change actor a * gen i * (actor a)⁻¹ ∈ closure (Set.range gen)
  rw [conjugation]
  rw [← heldRow_eq_closure]
  exact product_mem _

private theorem innerLocal_le_normalizer : innerLocal true ≤ normalizer (heldRow 3 : Set Held.He) := by
  apply sup_le
  · apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact actor_normalizes 0
    · exact actor_normalizes 1
  · apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact actor_normalizes 2
    · exact actor_normalizes 3
    · exact actor_normalizes 4
    · exact actor_normalizes 5

private def catWord (i : Fin 4) : List ℤ :=
  ((Held.TwoLocalCandidates.MaximalNormalizerCatalogue.generatorWords 12)[i.val]?).getD []
private def catGen (i : Fin 4) : Held.He :=
  Held.TwoLocalCandidates.MaximalNormalizerCatalogue.word (catWord i)
private def conjugator : Held.He := transporter false 0

private theorem catalogue_eq_closure : Catalogue 12 = closure (Set.range catGen) := by
  have hwords : Held.TwoLocalCandidates.MaximalNormalizerCatalogue.generatorWords 12 =
      List.ofFn catWord := by decide +kernel
  rw [Catalogue, Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ambient,
    Held.TwoLocalCandidates.MaximalNormalizerCatalogue.entry, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    rw [hwords] at hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Held.TwoLocalCandidates.MaximalNormalizerCatalogue.word (catWord i),
      ⟨catWord i, by rw [hwords]; exact List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩, rfl⟩

private def imageTable (i : Fin 4) : Equiv.Perm (Fin 2058) :=
  evalPowers Middle.tableGen (forwardWord false 0 i)

private theorem imageTable_eq (i : Fin 4) : imageTable i =
    Held.representation (MulAut.conj conjugator
      (Held.LocalPairs.SylowGeometry.Calculations.generator i)) := by
  change _ = Held.representation (transporter false 0 * _ * (transporter false 0)⁻¹)
  rw [RepresentativeImages.InnerImages.Pair00.forward]
  simp only [imageTable, evalPowers, map_list_prod, List.map_map, Function.comp_def,
    map_zpow, Middle.tableGen_eq]
  rfl

attribute [local irreducible] conjugator

private def mappedWordTable (w : List ℤ) : Equiv.Perm (Fin 2058) :=
  (w.map (fun k => if k < 0 then (imageTable (Fin.ofNat 4 (k.natAbs - 1)))⁻¹
    else imageTable (Fin.ofNat 4 (k.natAbs - 1)))).prod

private theorem mappedWordTable_eq (w : List ℤ) : mappedWordTable w =
    Held.representation (MulAut.conj conjugator
      (Held.TwoLocalCandidates.MaximalNormalizerCatalogue.word w : Held.He)) := by
  change _ = (Held.representation.comp ((MulAut.conj conjugator).toMonoidHom.comp
    Held.LocalPairs.SylowGeometry.Calculations.representative.subtype))
      (Held.TwoLocalCandidates.MaximalNormalizerCatalogue.word w)
  simp only [mappedWordTable, Held.TwoLocalCandidates.MaximalNormalizerCatalogue.word,
    map_list_prod, List.map_map, Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro n _
  simp only [Held.TwoLocalCandidates.MaximalNormalizerCatalogue.letter]
  split_ifs <;> simp only [map_inv, MonoidHom.coe_comp, Function.comp_apply,
    imageTable_eq] <;> rfl

private def imagePerm (i : Fin 4) : Equiv.Perm (Fin 2058) := mappedWordTable (catWord i)
private theorem imagePerm_eq (i : Fin 4) : imagePerm i =
    Held.representation (MulAut.conj conjugator (catGen i)) := mappedWordTable_eq _

private def imageProduct (is : List (Fin 4)) : Held.He :=
  (is.map (fun i => MulAut.conj conjugator (catGen i))).prod
private def imagePermProduct (is : List (Fin 4)) : Equiv.Perm (Fin 2058) :=
  (is.map imagePerm).prod
private theorem imagePermProduct_eq (is : List (Fin 4)) :
    imagePermProduct is = Held.representation (imageProduct is) := by
  simp only [imageProduct, imagePermProduct, map_list_prod, List.map_map,
    Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  exact imagePerm_eq i

private def transportProducts : Fin 4 → List (Fin 4)
  | 0 => [0, 2]
  | 1 => [1, 2, 3]
  | 2 => [2]
  | 3 => [3]

set_option maxRecDepth 8192 in
private theorem forward_check : ∀ i x : Fin 4,
    imagePerm i ⟨x.val, by omega⟩ = permProduct (transportProducts i) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem backward_check : ∀ i x : Fin 4,
    perm i ⟨x.val, by omega⟩ = imagePermProduct (transportProducts i) ⟨x.val, by omega⟩ := by
  decide +kernel

private theorem forward (i : Fin 4) :
    MulAut.conj conjugator (catGen i) = product (transportProducts i) := by
  apply Held.eq_of_four_point_images
  rw [← imagePerm_eq, ← permProduct_eq]
  exact forward_check i

private theorem backward (i : Fin 4) : gen i = imageProduct (transportProducts i) := by
  apply Held.eq_of_four_point_images
  rw [← perm_eq, ← imagePermProduct_eq]
  exact backward_check i

/-- The literal outer row is the transported catalogue row 12. -/
private theorem heldRow_three_eq_map : heldRow 3 =
    (Catalogue 12).map (MulAut.conj conjugator).toMonoidHom := by
  apply le_antisymm
  · rw [heldRow_eq_closure, closure_le]
    rintro _ ⟨i, rfl⟩
    rw [backward]
    apply list_prod_mem
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    apply mem_map_of_mem
    rw [catalogue_eq_closure]
    exact subset_closure (Set.mem_range_self j)
  · rw [map_le_iff_le_comap, catalogue_eq_closure, closure_le]
    rintro _ ⟨i, rfl⟩
    change MulAut.conj conjugator (catGen i) ∈ heldRow 3
    rw [forward]
    exact product_mem _

private theorem normalizer_card_le : Nat.card (normalizer (heldRow 3 : Set Held.He)) ≤ 9216 := by
  rw [heldRow_three_eq_map, ← map_equiv_normalizer_eq,
    card_map_of_injective (f := (MulAut.conj conjugator).toMonoidHom)
      (MulAut.conj conjugator).injective]
  exact Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Row12.normalizer_card_le

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions.RankFour

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions
open CoverageData

/-- The full ambient inner normalizer of the fourth literal outer row is
exactly the join of the published pure odd and two-subgroup candidates. -/
public theorem heldRow_three_normalizer :
    normalizer (heldRow 3 : Set Held.He) = innerLocal true := by
  symm
  apply eq_of_le_of_card_ge RankFour.innerLocal_le_normalizer
  have hc : Nat.card (innerLocal true) = 9216 :=
    (Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.candidateOrders false 0).2.2
  rw [hc]
  exact RankFour.normalizer_card_le

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions
