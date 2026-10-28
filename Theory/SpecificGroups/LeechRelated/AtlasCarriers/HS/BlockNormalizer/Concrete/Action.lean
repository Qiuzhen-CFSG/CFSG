module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.QuotientReduction

/-!
# The full action of the HS elementary-eight normalizer

An explicit word in the degree-100 ATLAS generators normalizes the marked
subgroup `EvenLocalCandidates.elementary 2`. Together with two marked Sylow
generators, it supplies 168 distinct conjugation actions. A kernel-checked
left inverse distinguishes these actions by their values on the three
specified elementary generators, evaluated at one permutation letter.
Since the actual automorphism group has order 168, the action is surjective.

The packed permutations are proved equal to carrier words. All finite checks
use kernel reduction; the discovery data and reproducible certificate encoder
are retained in `Action/source/`. No HS simplicity or additional normalizer
structure is assumed.

Sources: GLS3, Table 5.3m, printed p.274, and the faithful action on
`Omega_1(4^3)` on p.306; the HS case in the proof of Aschbacher–Smith
2.3.9(7), printed p.526.
-/

open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.HS.BlockNormalizer
open EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false

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

private def actionGenerator : Fin 3 → baseNormalizer :=
  ![⟨s0, baseSylow_le_normalizer (subset_closure ⟨0, rfl⟩)⟩,
    ⟨s1, baseSylow_le_normalizer (subset_closure ⟨1, rfl⟩)⟩,
    ⟨seven, seven_mem⟩]

private def decodeActionWord : Nat → Nat → List (Fin 3)
  | 0, _ => []
  | k + 1, n => if n = 0 then [] else
      ⟨(n % 4 - 1) % 3, Nat.mod_lt _ (by decide)⟩ :: decodeActionWord k (n / 4)

-- Two bits per letter, nine letters per word; zero terminates a word.
private def actionWordData : Nat := 8868647768228992495467043012958592511544244293015406163339089481176357006357975607062331342135761103507187429118077614361487208094864977336772589031611506810599261922220445801488472073657727695016097624994224225236438787175932656645981009240535717327782889543628403862179291285281380759346469830647826242721570977789101487666373303857406480191927496256152188763774061455340878655030371090610241527844887867613709026475083228307543548403876534809163864955866914271864397245561087728425702611911529770850800926810450927279459708832605004847585427732246722037075236661007285200276178343322440434325586778499071576093653628306913907404544063549092398886432273225302079948915807579156924923682975879804682524698996326717804121186841598497389931407426313400805282642864323556715973015344525464916418437007928247439513035713215815662387723877636314001200844147460075349039366250572542397221255233872487727541004795904

private def actionWord (i : Fin 168) : List (Fin 3) :=
  decodeActionWord 9 ((actionWordData >>> (18 * i.val)) % 262144)

private def actionRepresentative (i : Fin 168) : baseNormalizer :=
  evalWord actionGenerator (actionWord i)

private def elementaryBasis (j : Fin 3) : baseElementary :=
  ⟨elementaryGenerator j, subset_closure ⟨j, Fin.le_last j, rfl⟩⟩

-- Decode the eight distinct images of permutation letter 1 under `small`.
private def pointIndex (i : Fin 100) : Nat :=
  (191010976159253244208126498362013485282649311002648371905856322597835629975675403981816832 >>> (3 * i.val)) % 8

private def actionSignature (φ : MulAut baseElementary) : Nat :=
  pointIndex ((φ (elementaryBasis 0)).val.val 1) +
  8 * pointIndex ((φ (elementaryBasis 1)).val.val 1) +
  64 * pointIndex ((φ (elementaryBasis 2)).val.val 1)

-- Eight bits per entry, indexed by the three binary elementary coordinates.
private def actionDecode (s : Nat) : Nat :=
  (420033746108499062537932281228821766155637344722835247591337779519289554974803990598308375152944369767318763244572894594968744439370128745177845225642428791135762155458923074750424211211992934784400327008579461789354929623505783347664527169228844079038395733131402428667410684662376371017023486680050398927689800689985674912096601382910850650604754539606352231747685967119044917370995626048282722721056147139039941088204605804919791077512506602477842325216684084838645695570601444449206786221290726084318235652201609017844823849292614834166147437400662165971538361147291503609525671525193091113505661968151180245768699359526938934253473628348379763110640246408866173953495928400025721687388864417340456538860552559668176857450553559377672560694721174787991203824483156790182014354769350929825540161855451384699456791136527687397026345840659861407121589513053708897834515908420060643135190040367397272549364822407370908768590816277895166522933881722859978316964160424470113157164411596907748292356433222857506949149209403798322727092707574755454947073066513140385220883490712269970261197511796296853021074191824694785014658888933401710927794072769116446813302363805708026920016108906870057351305221737984032768 >>> (8 * s)) % 256

private theorem action_decode : ∀ i : Fin 168,
    actionDecode (actionSignature
      (baseElementary.normalizerMonoidHom (actionRepresentative i))) = i.val := by
  apply allFin
  decide +kernel

private theorem action_injective : Function.Injective
    (fun i : Fin 168 => baseElementary.normalizerMonoidHom (actionRepresentative i)) := by
  intro i j h
  apply Fin.ext
  rw [← action_decode i, ← action_decode j]
  exact congrArg (fun φ => actionDecode (actionSignature φ)) h

/-- Every automorphism of the concrete characteristic elementary eight is induced
by conjugation in its full HS normalizer. -/
public theorem baseNormalizer_action_surjective :
    Function.Surjective (baseElementary.normalizerMonoidHom : baseNormalizer →* MulAut baseElementary) := by
  have hc : Nat.card (MulAut baseElementary) = 168 :=
    (Nat.card_congr baseAutomorphismEquiv.toEquiv).trans Matrix.PSL3Two.card_SL
  have hsurj := (action_injective.bijective_of_nat_card_le (by
    rw [hc, Nat.card_fin])).surjective
  intro φ
  obtain ⟨i, hi⟩ := hsurj φ
  exact ⟨actionRepresentative i, hi⟩

end Sporadic.LeechRelated.HS.BlockNormalizer
