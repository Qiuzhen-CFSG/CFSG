module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base

/-!
# Generation of HS by a centralizer and the elementary-eight normalizer

In the exact degree-100 ATLAS carrier, the centralizer of the marked central
involution `e0`, together with the full normalizer of the marked elementary
eight, generates HS. Two explicit centralizer elements and a normalizing
word move `e0` to its conjugates by the two published generators. Each
published generator is therefore a product of a word in the join and an
element centralizing `e0`.

The packed permutations are identified with carrier words, and every required
commutation and conjugation identity is checked by kernel reduction. Neither
an order calculation nor a maximal-subgroup classification is used.
The discovery inputs and encoder are retained in `Generation/source/`.

Sources: the HS elimination in Aschbacher–Smith 2.3.9(7), printed p.526;
GLS3 Table 5.3m, printed p.274. ATLAS permutation provenance and the conversion
from right to left actions are documented in `AtlasCarriers/HS.lean`.
-/

namespace Sporadic.LeechRelated.HS.BlockNormalizer
open Subgroup Theory.GroupTheory EvenLocalCandidates
open EvenLocalCandidates.SylowCatalogueData
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false

private def a : Carrier := ⟨OrderCertificate.p0, by
  rw [OrderCertificate.a_eq_generator]
  exact generatorAElement.property⟩

private def b : Carrier := ⟨OrderCertificate.p1, by
  rw [OrderCertificate.b_eq_generator]
  exact generatorBElement.property⟩

private theorem a_eq : a = generatorAElement :=
  Subtype.ext OrderCertificate.a_eq_generator

private theorem b_eq : b = generatorBElement :=
  Subtype.ext OrderCertificate.b_eq_generator

private def c0Map (i : Fin 100) : Fin 100 :=
  ⟨(1527093459979768493890273050263251592437359106748504311864534754527623100157298598851218696018306956554096626892261018996445942967530962859797361388525383683901676472988854680347942506729652033720118546182775384 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c0InvMap (i : Fin 100) : Fin 100 :=
  ⟨(3519569464150162303331143261066782706797622646139427103087596992177512701103148338807714205778782095182460597434540411832164985894065250695542948731511632513350697241558305871318633254520367060669459528269826340 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c0Left : ∀ i, c0InvMap (c0Map i) = i := by
  apply allFin
  decide +kernel

private def c0Perm : Equiv.Perm (Fin 100) :=
  tablePerm c0Map c0InvMap c0Left (rightInverse_of_leftInverse_fin c0Left)

private def c0Word : Carrier := b⁻¹ * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b⁻¹ ^ 2) * a * b * a * b⁻¹ * a * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a * (b ^ 2) * a⁻¹ * b

private theorem c0Perm_eq_word : c0Perm = (c0Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def c0 : Carrier := ⟨c0Perm, by
  rw [c0Perm_eq_word]
  exact c0Word.property⟩

private def c1Map (i : Fin 100) : Fin 100 :=
  ⟨(3044663710698516376686038490896303522122021688738673715846006801609651329922826161913084128727622152051223504205838889471486140363035407100912681173188402637290060221140688892195315732929424006007682022236819505 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c1InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1241884833762428710133866724830187075839724245603165749773856029090813974251398620698606029827739978925910901046632116249271775835162740149443773665746254844572613088679377678218371028896768116442981235887379249 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c1Left : ∀ i, c1InvMap (c1Map i) = i := by
  apply allFin
  decide +kernel

private def c1Perm : Equiv.Perm (Fin 100) :=
  tablePerm c1Map c1InvMap c1Left (rightInverse_of_leftInverse_fin c1Left)

private def c1Word : Carrier := a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b * a * (b⁻¹ ^ 4) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 3) * a⁻¹ * b * a⁻¹ * b * a⁻¹

private theorem c1Perm_eq_word : c1Perm = (c1Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def c1 : Carrier := ⟨c1Perm, by
  rw [c1Perm_eq_word]
  exact c1Word.property⟩

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

private abbrev joined : Subgroup Carrier := centralizer ({e0} : Set Carrier) ⊔ baseNormalizer

private theorem seven_mem_joined : seven ∈ joined := (le_sup_right : baseNormalizer ≤ joined) seven_mem

private theorem c0_centralizes : c0 * e0 = e0 * c0 := by
  have h : ∀ x : Fin 100,
      (c0 * e0 : Equiv.Perm (Fin 100)) x = (e0 * c0 : Equiv.Perm (Fin 100)) x := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext h)

private theorem c0_mem_joined : c0 ∈ joined :=
  (le_sup_left : centralizer ({e0} : Set Carrier) ≤ joined) (mem_centralizer_singleton_iff.mpr c0_centralizes)

private theorem c1_centralizes : c1 * e0 = e0 * c1 := by
  have h : ∀ x : Fin 100,
      (c1 * e0 : Equiv.Perm (Fin 100)) x = (e0 * c1 : Equiv.Perm (Fin 100)) x := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext h)

private theorem c1_mem_joined : c1 ∈ joined :=
  (le_sup_left : centralizer ({e0} : Set Carrier) ≤ joined) (mem_centralizer_singleton_iff.mpr c1_centralizes)

private def recoveryA : Carrier := c1⁻¹ * seven * c1 * seven⁻¹ * c1⁻¹ * seven⁻¹ * c0⁻¹ * seven

private theorem recoveryA_mem : recoveryA ∈ joined := by
  unfold recoveryA
  repeat first | apply joined.mul_mem | apply joined.inv_mem |
    exact c0_mem_joined | exact c1_mem_joined | exact seven_mem_joined

private theorem correctionA_centralizes :
    (recoveryA⁻¹ * a) * e0 = e0 * (recoveryA⁻¹ * a) := by
  have h : ∀ x : Fin 100,
      ((recoveryA⁻¹ * a) * e0 : Equiv.Perm (Fin 100)) x =
        (e0 * (recoveryA⁻¹ * a) : Equiv.Perm (Fin 100)) x := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext h)

private theorem a_mem_joined : a ∈ joined := by
  have hc : recoveryA⁻¹ * a ∈ joined :=
    (le_sup_left : centralizer ({e0} : Set Carrier) ≤ joined) (mem_centralizer_singleton_iff.mpr correctionA_centralizes)
  simpa only [mul_inv_cancel_left] using joined.mul_mem recoveryA_mem hc

private def recoveryB : Carrier := c0⁻¹ * c1⁻¹ * seven * c0⁻¹ * seven⁻¹ * c0 * seven⁻¹

private theorem recoveryB_mem : recoveryB ∈ joined := by
  unfold recoveryB
  repeat first | apply joined.mul_mem | apply joined.inv_mem |
    exact c0_mem_joined | exact c1_mem_joined | exact seven_mem_joined

private theorem correctionB_centralizes :
    (recoveryB⁻¹ * b) * e0 = e0 * (recoveryB⁻¹ * b) := by
  have h : ∀ x : Fin 100,
      ((recoveryB⁻¹ * b) * e0 : Equiv.Perm (Fin 100)) x =
        (e0 * (recoveryB⁻¹ * b) : Equiv.Perm (Fin 100)) x := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext h)

private theorem b_mem_joined : b ∈ joined := by
  have hc : recoveryB⁻¹ * b ∈ joined :=
    (le_sup_left : centralizer ({e0} : Set Carrier) ≤ joined) (mem_centralizer_singleton_iff.mpr correctionB_centralizes)
  simpa only [mul_inv_cancel_left] using joined.mul_mem recoveryB_mem hc

/-- The centralizer of the marked involution and the full elementary-eight
normalizer generate the exact degree-100 HS carrier. -/
public theorem centralizer_sup_baseNormalizer_eq_top :
    centralizer ({e0} : Set Carrier) ⊔ baseNormalizer = ⊤ := by
  apply eq_top_of_generators_mem
  · exact a_eq ▸ a_mem_joined
  · exact b_eq ▸ b_mem_joined

end Sporadic.LeechRelated.HS.BlockNormalizer

