module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreSections
public import Theory.GroupAction.SimpleSeventeenSmallSection
public import Theory.GroupAction.SymmetricSixSmallSection
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# The actual point-carrier lift cannot normalize the original core

The characteristic section Phi(Q)/Z(Q) is an actual marked dual-natural
three-space. A two-group extension of a simple group whose order is divisible
by five has only two-group images on a section of order eight. Its perfect
original component would therefore act trivially if the carrier lift
normalized Q, contradicting the marked action.

This is a normalization obstruction for the literal point-carrier preimage,
not a finite-carrier exclusion. In particular Q need not be characteristic
in the point kernel, and the small section is not identified with a section
of that kernel's Frattini quotient.

Source: Aschbacher--Smith15.3.23, pp.1128--1129, with the original
characteristic sections of MS93(4.5)(v), p.895.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
universe u v
variable {G : Type u} [Group G] [Finite G]

private theorem marked_dual_normalization_obstruction
    (L D E A : Subgroup G) [Group.IsPerfect L]
    {K : Type v} [Group K] [Finite K] [IsSimpleGroup K]
    (q : A →* K) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hfive : 5 ∣ Nat.card K) (hLA : L ≤ A)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hs : HasSectionModel L D E (linearThreeActor e) BinaryLinearThree.W.dual)
    (hAD : A ≤ normalizer D) (hAE : A ≤ normalizer E) : False := by
  obtain ⟨hED,hLD,hLE,hn,ev,hev⟩ := hs
  let := hn
  let V := D ⧸ E.subgroupOf D
  have hcard : Nat.card V = 8 := by
    rw [Nat.card_congr ev.toEquiv]
    change Nat.card (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 8
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Subspace.dual_finrank_eq,
      Module.finrank_pi,Fintype.card_fin,Nat.card_zmod]
    norm_num
  have hV : IsPGroup 2 V := IsPGroup.of_card (n := 3) hcard
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action A D E hAD hAE hn
  have hp : IsPGroup 2 a.range := MonoidHom.isPGroup_range_of_simple_quotient
    q hq hk a 5 hfive (MulAut.not_five_dvd_card_of_twoGroup_card_le_eight hV hcard.le)
  let f := a.rangeRestrict.comp (inclusion hLA)
  have hf := pResidual_le_ker_of_isPGroup 2 f hp
  rw [pResidual_eq_top_of_isPerfect] at hf
  have htriv (l : L) : a (inclusion hLA l) = 1 := by
    exact congrArg Subtype.val (hf (mem_top l))
  have hactor (l : L) : linearThreeActor e l = 1 := by
    apply BinaryLinearThree.dual_injective
    apply LinearMap.ext
    intro v
    obtain ⟨x,hx⟩ := ev.surjective (Multiplicative.ofAdd v)
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf D) x
    let d' : D := ⟨l*d*(l:G)⁻¹,(mem_normalizer_iff.mp (hLD l.property) d).mp d.property⟩
    have hfix : QuotientGroup.mk' (E.subgroupOf D) d' =
        QuotientGroup.mk' (E.subgroupOf D) d := by
      have hh := ha (inclusion hLA l) d
      rw [htriv] at hh
      exact hh.symm
    have he := hev l d d' rfl
    rw [hfix] at he
    have hx' : (ev (QuotientGroup.mk' (E.subgroupOf D) d)).toAdd = v :=
      congrArg Multiplicative.toAdd hx
    rw [hx'] at he
    rw [map_one]
    exact he.symm
  have ho : Function.Surjective (linearThreeActor e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
  have ht : Subsingleton Matrix.PSL3Two.SL := ⟨by
    intro x y
    obtain ⟨l,rfl⟩ := ho x
    obtain ⟨m,rfl⟩ := ho y
    exact (hactor l).trans (hactor m).symm⟩
  let : Subsingleton Matrix.PSL3Two.SL := ht
  have hc : Nat.card Matrix.PSL3Two.SL = 1 := Nat.card_unique
  rw [Matrix.PSL3Two.card_SL] at hc
  omega

/-- The literal preimage of a five-divisible simple point carrier cannot
normalize a core whose characteristic eight-section has the actual marked
component action. No characteristicity in the point kernel is required. -/
theorem binary_three_point_core_not_normalized
    (L Q C : Subgroup G) [Group.IsPerfect L] (hLC : L ≤ C)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hs : HasSectionModel L (frattiniIn Q)
      (CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q)
      (linearThreeActor e) BinaryLinearThree.W.dual)
    (K : Subgroup (C ⧸ pCore 2 C)) [IsSimpleGroup K]
    (hBK : (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) ≤ K)
    (hfive : 5 ∣ Nat.card K) :
    ¬ ((K.comap (QuotientGroup.mk' (pCore 2 C))).map C.subtype) ≤ normalizer Q := by
  let q := QuotientGroup.mk' (pCore 2 C)
  let A₀ := K.comap q
  let A := A₀.map C.subtype
  let i : A ≃* A₀ := (A₀.equivMapOfInjective C.subtype C.subtype_injective).symm
  let f : A →* K := (q.subgroupComap K).comp i.toMonoidHom
  have hf : Function.Surjective f :=
    (q.subgroupComap_surjective_of_surjective K (QuotientGroup.mk'_surjective _)).comp i.surjective
  let k : f.ker →* pCore 2 C := {
    toFun x := ⟨i x,by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val x.property⟩
    map_one' := by
      apply Subtype.ext
      exact congrArg (fun y : A₀ => (y : C)) i.map_one
    map_mul' x y := by
      apply Subtype.ext
      exact congrArg (fun y : A₀ => (y : C)) (i.map_mul x y) }
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.of_injective k (by
    intro x y he
    apply Subtype.ext
    apply i.injective
    exact Subtype.ext (congrArg (fun z : pCore 2 C => (z : C)) he))
  have hLA : L ≤ A := by
    intro l hl
    exact ⟨⟨l,hLC hl⟩,hBK (mem_map_of_mem q hl),rfl⟩
  intro hn
  exact marked_dual_normalization_obstruction L (frattiniIn Q)
    (CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q)
    A f hf hk hfive hLA e hs
    (hn.trans (normalizer_le_normalizer_characteristic_image Q (frattini Q)))
    (hn.trans (normalizer_le_normalizer_characteristic_image Q (center Q)))

open LinearThree ChapterC BinaryMS.MS93

/-- The full original large-distance source supplies the normalizer
obstruction at the unchanged point and unchanged quotient preimage. -/
theorem binary_three_source_point_core_not_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [IsSimpleGroup K]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hfive : 5 ∣ Nat.card K) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    ¬ ((K.comap q).map C.subtype) ≤ normalizer (LinearThree.commutatorCore c.L) := by
  obtain ⟨e',hs,_,_⟩ := binary_three_large_distance_original_core_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  let J := c.L ⊔ d.S
  let : Group.IsPerfect (c.L.subgroupOf J) := b.component.perfect
  let i := subgroupOfEquivOfLe (show c.L ≤ J from le_sup_left)
  let : Group.IsPerfect c.L := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
  exact binary_three_point_core_not_normalized c.L (LinearThree.commutatorCore c.L)
    (centralizer ({z} : Set G)) (le_sup_left.trans hLS) e' hs K hBK hfive

/-- In the actual A7 or A8 carrier rows, the point-carrier lift fails to
normalize the original core with no extra divisibility premise. -/
theorem binary_three_source_alternating_core_not_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (n : ℕ) (hn : n = 7 ∨ n = 8) (a : K ≃* alternatingGroup (Fin n)) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    ¬ ((K.comap q).map C.subtype) ≤ normalizer (LinearThree.commutatorCore c.L) := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by
    simpa only [Nat.card_fin] using (show 5 ≤ n by omega))
  let : IsSimpleGroup K := a.isSimpleGroup
  have hfive : 5 ∣ Nat.card K := by
    rw [Nat.card_congr a.toEquiv]
    rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;>
      norm_num [Nat.card_fin,Nat.factorial]
  exact binary_three_source_point_core_not_normalized
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS K hBK hfive

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
