module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagRank

/-!
# The small Baumann images on the original first action core

A trivial Baumann image makes J(R₁) centralize V, so B.2.10 makes
Baum(R₁) normal in LT. For a transposition image, adjoin O₂(LT) to the
Baumann subgroup and apply the augmentation version of C.1.24(c).
Baumann heredity and maximal two-local uniqueness give the required
normalizer bound or a short block. Characteristic two is established
from the original ambient hypothesis, without identifying C_LT(V) with
O₂(LT). Thus the full covered action kernel is retained.

The covered-row consumer excludes shortness using the actual quotient
centers. These proofs settle the two small images on the literal R₁;
the full point-radical image and the covered 13.3.9 residual classification
remain obligations of the fixed-core assembly.
Source: Aschbacher--Smith 13.2.2(7), pp.877--878,
C.1.24(c) and C.1.37, pp.130--131,142--143.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The two small Baumann images give the source normalizer/short
alternative without identifying the full action kernel with O₂(LT). -/
theorem firstFlagCore_small_baumann
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (hLq : (L.subgroupOf (L ⊔ (T : Subgroup G))).map q = alternatingGroup (Fin 6))
    (hsmall : let X := L ⊔ (T : Subgroup G)
      let R := firstFlagCore h structural D m
      ((ChapterB.baumann R).subgroupOf X).map q = ⊥ ∨
        ∃ r : Equiv.Perm (Fin 6), r.IsSwap ∧
          ((ChapterB.baumann R).subgroupOf X).map q = zpowers r) :
    normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L := by
  let X := L ⊔ (T : Subgroup G)
  let R := firstFlagCore h structural D m
  let Li := L.subgroupOf X
  let U := V.subgroupOf X
  let Ri := R.subgroupOf X
  let B := ChapterB.baumann Ri
  have hLX : L ≤ X := le_sup_left
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hRT : R ≤ T := map_subtype_le _
  have hRX : R ≤ X := hRT.trans le_sup_right
  have hXV := sup_le D.normalizes ((structural G T L h).2.2 V D).1
  let : Li.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXV
  let := D.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVX
  let ek : Li ≃* L := subgroupOfEquivOfLe hLX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
  have hker := ChapterB.Offenders.SixCorePoint.kernel_centralizer U q e he
  have hcmp : Li.IsCComponent := h.maximal_faithful.1.1.1
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple (Li ⧸ pCore 2 Li) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)).symm
  have hfL : generalizedFitting Li = pCore 2 Li := by
    apply map_injective (f := ek.toMonoidHom) ek.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso]
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
        (h.simpleQTKE.evenCharacteristic T) h.maximal_faithful.1.1)
  have hf : generalizedFitting X = pCore 2 X :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
        (h.simpleQTKE.evenCharacteristic T)
        ⟨h.maximal_faithful.1.1.2.2,show (T : Subgroup G) ≤ X from le_sup_right⟩))
  obtain ⟨hQR,hRC⟩ := firstFlagCore_kernel h structural D m
  have hQRi : pCore 2 X ≤ Ri := fun x hx => hQR (mem_map_of_mem X.subtype hx)
  have hRiT : Ri ≤ (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right) : Subgroup X) := by
    rw [Sylow.coe_subtype]
    exact comap_mono hRT
  have hVR : U ≤ Ri := comap_mono (D.le_core.trans hQR)
  have hQker : pCore 2 X ≤ q.ker := by
    rw [hker]
    intro x hx v hv
    exact Subtype.ext (D.core_centralizes (mem_map_of_mem X.subtype hx) v.val hv)
  have hcore : pCore 2 X = Ri ⊓ centralizer (U : Set X) := by
    symm
    apply map_injective X.subtype_injective
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hVX]
    exact hRC
  have hprod (x : X) : ∃ l ∈ Li, ∃ t ∈
      (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right) : Subgroup X), l*t=x := by
    apply mem_sup_of_normal_left.mp
    rw [Sylow.coe_subtype,←subgroupOf_sup hLX (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
    exact mem_top x
  have hm : ⁅U,Li⁆ ≠ ⊥ := by
    intro hb
    have hh := congrArg (map X.subtype) hb
    rw [map_commutator,map_subgroupOf_eq_of_le hVX,map_subgroupOf_eq_of_le hLX,Subgroup.map_bot] at hh
    exact D.ne_bot (D.eq_commutator.trans hh)
  have hBm : B.map X.subtype = ChapterB.baumann R := by
    rw [ChapterC.RankOne.SymmetricSix.baumann_map X X.subtype X.subtype_injective Ri,
      map_subgroupOf_eq_of_le hRX]
  have hBi : B = (ChapterB.baumann R).subgroupOf X := by
    rw [←hBm]
    ext x
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hs : B.map q = ⊥ ∨ ∃ r : Equiv.Perm (Fin 6), r.IsSwap ∧ B.map q = zpowers r := by
    rw [hBi]
    exact hsmall
  have halt : (∃ C : Subgroup B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map B.subtype).Normal) ∨ ChapterC.IsBlock Li := by
    rcases hs with hz | ⟨r,hr,hB⟩
    · left
      have hJ : ChapterB.thompsonJ Ri 0 ≤ centralizer (U : Set X) := by
        rw [ChapterB.thompsonJ_zero,←hker]
        exact (ChapterB.elementaryAbelianMaxJ_le_baumann Ri).trans
          ((Subgroup.map_eq_bot_iff _).mp hz)
      have hn := (ChapterB.lemma_B_2_10_centralizing U Ri hVR hQRi hcore hJ).2.2.2
      have hRne : Ri ≠ ⊥ := by
        intro hr
        exact hm (by rw [le_bot_iff.mp (hVR.trans_eq hr),commutator_bot_left])
      let : Nontrivial B := (nontrivial_iff_ne_bot _).mpr
        (ChapterC.RankOne.SymmetricSix.baumann_ne_bot Ri ((T.subtype le_sup_right).isPGroup'.to_le hRiT) hRne)
      exact ⟨⊤,inferInstance,top_ne_bot,by
        simpa only [←MonoidHom.range_eq_map,range_subtype] using hn⟩
    · let R0 := B ⊔ pCore 2 X
      have hR0 : R0 ≤ Ri := sup_le inf_le_left hQRi
      have hb : ChapterB.baumann R0 = B := baumann_eq_of_intermediate Ri R0 le_sup_left hR0
      have hi : R0.map q = zpowers r := by
        rw [Subgroup.map_sup,hB,(Subgroup.map_eq_bot_iff _).mpr hQker,sup_bot_eq]
      have hh := ChapterC.RankOne.SymmetricSix.normal_characteristic_or_block_of_core_six
        Li U R0 hcmp hf hfL (T.subtype le_sup_right) le_sup_right
        (hR0.trans hRiT) hprod q hLq e he hm r hr hi
      rw [hb] at hh
      exact hh
  rcases halt with ⟨C,hC,hCn,hCN⟩ | hb
  · left
    let := hC
    let N := (C.map B.subtype).map X.subtype
    have hn : N ≠ ⊥ := by
      intro hh
      exact hCn ((C.map_eq_bot_iff_of_injective B.subtype_injective).mp
        (((C.map B.subtype).map_eq_bot_iff_of_injective X.subtype_injective).mp hh))
    have hp : IsPGroup 2 N := ((((T.isPGroup'.to_le hRT).comap_subtype).to_le
      (show B ≤ Ri from inf_le_left)).to_subgroup C).map B.subtype |>.map X.subtype
    have hXN : X ≤ normalizer (N : Set G) := by
      apply le_normalizer_iff.mpr
      intro x hx n hn
      obtain ⟨v,hv,rfl⟩ := hn
      exact mem_map_of_mem X.subtype (hCN.conj_mem v hv ⟨x,hx⟩)
    have hNM : normalizer (N : Set G) ≤ normalizer (L : Set G) :=
      normalizer_le_of_unique_maximalTwoLocal
        (h.source_normalizer_maximal_unique structural
          (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
          (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 hp hn hXN
    rw [←hBm]
    exact (normalizer_le_normalizer_characteristic_map X.subtype X.subtype_injective B C).trans hNM
  · exact Or.inr (hb.short.of_mulEquiv ek)

/-- In the covered source row, the two small images give the literal
Baumann-normalizer bound. The short alternative is impossible because the
original five-dimensional marking would make the full quotient ordinary. -/
theorem covered_firstFlagCore_small_baumann_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (hLq : (L.subgroupOf (L ⊔ (T : Subgroup G))).map q = alternatingGroup (Fin 6))
    (hsmall : let X := L ⊔ (T : Subgroup G)
      let R := firstFlagCore h structural D m
      ((ChapterB.baumann R).subgroupOf X).map q = ⊥ ∨
        ∃ r : Equiv.Perm (Fin 6), r.IsSwap ∧
          ((ChapterB.baumann R).subgroupOf X).map q = zpowers r) :
    normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) := by
  apply (firstFlagCore_small_baumann h structural D m q hq hLq hsmall).resolve_right
  intro hb
  obtain ⟨e⟩ := ordinary_of_short_core_marking D m hb
  have hh := Nat.card_congr (centerCongr e).toEquiv
  rw [hc.2.1,alternatingGroup.center_eq_bot (by simp),card_bot] at hh
  omega
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
