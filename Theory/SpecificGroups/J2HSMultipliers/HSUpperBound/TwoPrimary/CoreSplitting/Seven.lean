module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreGeometry

/-!
# A concrete actor on the HS normalizer core

The seven-element word and packed permutations below are reused from
`HS/BlockNormalizer/Concrete/Action.lean` (whose witnesses are private).
The kernel checks its carrier membership and its action on the three
coordinates of the actual C₄³ core. The resulting three equations are used
by `CoreSplitting.Pairing` to kill the central-extension commutator pairing.

Source: GLS3 Table 5.3m and its faithful core action on printed p.306;
Aschbacher–Smith I.1.1–I.1.3(1), printed p.407. The coordinate identities
are independent model calculations and do not use covering conclusions.
-/

open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.CoreSplitting
open Sporadic.LeechRelated.HS EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData
open BlockNormalizer BlockNormalizer.CoreGeometry
set_option maxRecDepth 20000

private def aMap (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def aInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem aLeft : ∀ i, aInvMap (aMap i) = i := by
  apply allFin
  decide +kernel

private def aPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm aMap aInvMap aLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin aLeft)

private theorem aPerm_eq_generator : aPerm = generatorA := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def a : Carrier := ⟨aPerm, aPerm_eq_generator.symm ▸
  Subgroup.subset_closure (by simp)⟩

private def bMap (i : Fin 100) : Fin 100 :=
  ⟨(1584088533044622539624716012360915100311113938083754946662587072801676726706164344372852891441442777957300990173557581617101002762039959730741693432191260900145476108926406488416286385789713123784992907581461166 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def bInvMap (i : Fin 100) : Fin 100 :=
  ⟨(852881488533531112336995551220226122361210863663080587750664607485875722147280441807057556633165462885474069200795003754517913050689892735891088239319177696223676845175972313037682728934689958756512102884170325 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem bLeft : ∀ i, bInvMap (bMap i) = i := by
  apply allFin
  decide +kernel

private def bPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm bMap bInvMap bLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin bLeft)

private theorem bPerm_eq_generator : bPerm = generatorB := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def b : Carrier := ⟨bPerm, bPerm_eq_generator.symm ▸
  Subgroup.subset_closure (by simp)⟩

private def sevenMap (i : Fin 100) : Fin 100 :=
  ⟨(1136742900769022640185733578659955024891157537247565748203960254312220454731536736652853152609354060788253494270830305769461046276601535240770691501804434786843916798425948482847283264758968354154974714668253376 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def sevenInvMap (i : Fin 100) : Fin 100 :=
  ⟨(1603845743149177324658917020195331319918192695436596618294581098675217573189454653125713458098507917946884519913902583349450934598826787072159804240440370395088972910559834414883069951722061996889481449984458882 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem sevenLeft : ∀ i, sevenInvMap (sevenMap i) = i := by
  apply allFin
  decide +kernel

private def sevenPerm : Equiv.Perm (Fin 100) :=
  tablePerm sevenMap sevenInvMap sevenLeft (rightInverse_of_leftInverse_fin sevenLeft)

private def sevenWord : Carrier := b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a * b⁻¹ * a * (b ^ 2) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a * b⁻¹ * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b⁻¹ ^ 3) * a⁻¹ * b * a⁻¹ * (b ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 4) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2)

private theorem sevenPerm_eq_word : sevenPerm = (sevenWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def seven : Carrier := ⟨sevenPerm, by
  rw [sevenPerm_eq_word]
  exact sevenWord.property⟩

private theorem seven_conjugation (j : Fin 3) :
    seven * elementaryGenerator j * seven⁻¹ = small (![3, 6, 1] j) := by
  have h : ∀ (j : Fin 3) (x : Fin 100),
      ((seven * elementaryGenerator j * seven⁻¹ : Carrier) : Equiv.Perm (Fin 100)) x =
        (small (![3, 6, 1] j) : Equiv.Perm (Fin 100)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h j))

private theorem seven_mem : seven ∈ baseNormalizer := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rw [elementary, MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    change seven * elementaryGenerator j * seven⁻¹ ∈ elementary 2
    rw [seven_conjugation]
    exact small_mem_elementary _ 2 (![3, 6, 1] j : Fin 8).isLt
  · exact le_of_eq (Nat.card_congr ((MulAut.conj seven).subgroupMap
      baseElementary).toEquiv)


@[expose] public def axis (i : Fin 3) : Fin 3 → ZMod 4 := Pi.single i 1
@[expose] public def sevenAxis : Fin 3 → (Fin 3 → ZMod 4) :=
  ![3 • axis 0 + axis 1 + 2 • axis 2,
    2 • axis 0 + axis 1 + axis 2,
    3 • axis 0 + 2 • axis 1 + 2 • axis 2]

@[expose] public def coordinateInNormalizer :
    Multiplicative (Fin 3 → ZMod 4) →* baseNormalizer :=
  (pCore 2 baseNormalizer).subtype.comp coreCoordinates

public theorem exists_coordinate_actor : ∃ y : baseNormalizer,
    ∀ i : Fin 3, y * coordinateInNormalizer (.ofAdd (axis i)) * y⁻¹ =
      coordinateInNormalizer (.ofAdd (sevenAxis i)) := by
  refine ⟨⟨seven, seven_mem⟩, ?_⟩
  intro i
  apply Subtype.ext
  change seven * ((coreCoordinates (.ofAdd (axis i))).val : Carrier) * seven⁻¹ =
    ((coreCoordinates (.ofAdd (sevenAxis i))).val : Carrier)
  rw [coreCoordinates_apply, coreCoordinates_apply]
  have h : ∀ (j : Fin 3) (x : Fin 100),
      ((seven * (root 0 ^ (axis j 0).val * root 1 ^ (axis j 1).val *
        root 2 ^ (axis j 2).val) * seven⁻¹ : Carrier) : Equiv.Perm (Fin 100)) x =
      ((root 0 ^ (sevenAxis j 0).val * root 1 ^ (sevenAxis j 1).val *
        root 2 ^ (sevenAxis j 2).val : Carrier) : Equiv.Perm (Fin 100)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.CoreSplitting
