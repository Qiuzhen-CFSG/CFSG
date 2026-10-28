module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5PointComparison
public import Theory.SpecificGroups.SL2.BinaryThreeSection
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.SpecificGroups.Held.TwoPartDivisibility
public import CFSG.Quasithin.MainConverse.SporadicLocal.He
public import CFSG.Quasithin.MainConverse.MathieuLocal.M23Even
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.TripleSolvable
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# Actual native placements of the remaining binary-three component

A normalized local PSL₃(2) section in Held is a literal conjugate of max5,
contains the original full Sylow, and is self-normalizing. In M₂₃ its
entire normalizer lies in an actual heptad stabilizer after conjugating
that same full Sylow to the fixed native marking.

Both arguments first derive nontrivial two-core from even characteristic
and the order336 automorphism group of PSL₃(2). Native maximal two-local
coverage and factor seven exclude the other candidates. The max5
perfectness calculation then identifies the original smaller subgroup.
No quasisimplicity of B or extra sporadic placement premise is assumed.
These are genuine placements; full carrier exclusion requires additional
original opposite-core geometry.
Source: GLS3 Tables5.3d,5.3p and Aschbacher--Smith A.3.12,15.3.23,
printed pp.47--48 and1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- A literal Held max5 local carrier cannot strictly enlarge the original
binary-three component. The quotient premise is the actual B/O₂(B) section.
The proof delegates only the native max5 order and perfectness calculation.
-/
private theorem binary_three_max5_local_eq_top
    (S : Sylow 2 (Held.TwoLocalCandidates.subgroup 2))
    {B : Subgroup (Held.TwoLocalCandidates.subgroup 2)}
    (hSB : (S : Subgroup (Held.TwoLocalCandidates.subgroup 2)) ≤
      normalizer (B : Set (Held.TwoLocalCandidates.subgroup 2)))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) : B = ⊤ := by
  have h168 : 168 ∣ Nat.card B := by
    have hq : Nat.card (B ⧸ pCore 2 B) = 168 :=
      (Nat.card_congr (eB.trans Matrix.PSL3Two.equiv.symm).toEquiv).trans
        Matrix.PSL3Two.card_SL
    exact (show 168 ∣ Nat.card (B ⧸ pCore 2 B) by rw [hq])
      |>.trans (card_quotient_dvd_card (pCore 2 B))
  exact Held.TwoLocalCandidates.max5_normalized_subgroup_top S B hSB h168

private theorem binary_three_card_dvd {G : Type*} [Group G] {B : Subgroup G}
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) : 168 ∣ Nat.card B := by
  have hq : Nat.card (B ⧸ pCore 2 B) = 168 :=
    (Nat.card_congr (eB.trans Matrix.PSL3Two.equiv.symm).toEquiv).trans Matrix.PSL3Two.card_SL
  exact hq ▸ card_quotient_dvd_card (pCore 2 B)

private theorem binary_three_core_ne_bot_of_even
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ localCComponents S) (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hE : IsEvenCharacteristicAt S) (h32 : 32 ∣ Nat.card G) : pCore 2 B ≠ ⊥ := by
  intro hc
  let e : B ≃* PSL(3,ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans eB
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup B := e.isSimpleGroup
  let : Group.IsPerfect B := by
    let := hB.perfect
    let a := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)
    exact Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hB hSB
  let f := B.normalizerMonoidHom.comp (inclusion hSB)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hf]
    refine ⟨x.property,?_⟩
    change inclusion hSB x ∈ B.normalizerMonoidHom.ker at hx
    rwa [normalizerMonoidHom_ker] at hx
  have hd := card_dvd_of_injective f hi
  rw [Nat.card_congr (MulAut.congr e).toEquiv,Matrix.PSL3Two.Automorphisms.card_aut] at hd
  exact (by decide : ¬32 ∣ 336) ((S.pow_dvd_card_of_pow_dvd_card (n := 5) h32).trans hd)

private theorem maximal_overgroup_of_core {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {B : Subgroup G}
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (hc : pCore 2 B ≠ ⊥) :
    ∃ N : Subgroup G, IsMaximalTwoLocal N ∧ normalizer (B : Set G) ≤ N ∧
      (S : Subgroup G) ≤ N := by
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun he => hc ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hl : IsTwoLocal (normalizer (U : Set G)) := ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩
  obtain ⟨N,hUN,hN⟩ := Finite.exists_le_maximal hl
  have hBN : normalizer (B : Set G) ≤ N :=
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B)).trans hUN
  exact ⟨N,hN,hBN,hSB.trans hBN⟩

private theorem held_max34_seven_free (i : Bool) :
    ¬ 7 ∣ Nat.card (Held.LocalPairs.PairCoverage.localOvergroup i) := by
  open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner in
  let f := SixPoint.quotientAction i
  have hk : ¬ 7 ∣ Nat.card f.ker := fun h => (by decide : ¬7 ∣ 3)
    (h.trans (Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i))
  have hi : ¬ 7 ∣ Nat.card f.range := by
    intro h
    have hh := h.trans f.range.card_subgroup_dvd_card
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at hh
  have hq : ¬7 ∣ Nat.card (Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.LocalQuotient i) := by
    rw [←f.ker.card_mul_index,index_ker]
    exact fun h => ((by decide : Nat.Prime 7).dvd_mul.mp h).elim hk hi
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2)
    (G := Held.LocalPairs.PairCoverage.localOvergroup i)).exists_card_eq
  rw [←(pCore 2 (Held.LocalPairs.PairCoverage.localOvergroup i)).card_mul_index,index_eq_card,hn]
  intro h
  rcases (by decide : Nat.Prime 7).dvd_mul.mp h with h | h
  · exact (by decide : ¬7 ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow h)
  · exact hq h

private theorem map_conj_product {G : Type*} [Group G] (V : Subgroup G) (g h : G) :
    V.map (MulAut.conj (g*h)).toMonoidHom =
      (V.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_inv_rev,mul_assoc]

/-- The original normalized local binary-three subgroup in Held is an
actual conjugate of max5, contains the full Sylow and is self-normalizing. -/
theorem binary_three_held_actual_max5
    (S : Sylow 2 Held.He) (B : Subgroup Held.He)
    (hB : B ∈ localCComponents S) (hSB : (S : Subgroup Held.He) ≤ normalizer (B : Set Held.He))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) :
    (∃ g : Held.He, B.map (MulAut.conj g).toMonoidHom = Held.TwoLocalCandidates.subgroup 2) ∧
      (S : Subgroup Held.He) ≤ B ∧ normalizer (B : Set Held.He) = B := by
  have hc := binary_three_core_ne_bot_of_even S hB hSB eB
    (MainConverse.SporadicLocal.he_evenCharacteristic S)
    ((by decide : 32 ∣ 2^10).trans Held.two_pow_ten_dvd_card)
  obtain ⟨N,hN,hBN,hSN⟩ := maximal_overgroup_of_core S hSB hc
  have hBN' : B ≤ N := B.le_normalizer.trans hBN
  obtain ⟨T,hcatalogue⟩ := Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq Held.He S T
  let a := MulAut.conj h
  have hTN : (T : Subgroup Held.He) ≤ N.map a.toMonoidHom := by
    have hu := map_mono (f := a.toMonoidHom) hSN
    change ((h • S : Sylow 2 Held.He) : Subgroup Held.He) ≤ _ at hu
    rwa [hh] at hu
  have hNmap := Theory.Quasithin.isMaximalTwoLocal_map a hN
  obtain ⟨R,hR,hRn,hRe,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hNmap hTN
  obtain ⟨i,g,hg⟩ := hcatalogue R hR hRn hRe (hNR ▸ hNmap)
  have hN' : N.map a.toMonoidHom =
      (Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom := hNR.trans hg
  have hi : i = 2 := by
    have hd : 7 ∣ Nat.card (Held.TwoLocalCandidates.subgroup i) := by
      have hd := ((by decide : 7 ∣ 168).trans (binary_three_card_dvd eB)).trans
        (card_dvd_of_le hBN')
      have hm : Nat.card (N.map a.toMonoidHom) = Nat.card N := card_map_of_injective a.injective
      rw [hN',card_map_of_injective (MulAut.conj g).injective] at hm
      rwa [hm]
    fin_cases i
    · exact (held_max34_seven_free false hd).elim
    · exact (held_max34_seven_free true hd).elim
    · rfl
  subst i
  let e : N ≃* Held.TwoLocalCandidates.subgroup 2 :=
    (a.subgroupMap N).trans ((MulEquiv.subgroupCongr hN').trans
      ((MulAut.conj g).subgroupMap _).symm)
  let A := B.subgroupOf N
  let P := S.subtype hSN
  have hn : (P : Subgroup N) ≤ normalizer (A : Set N) := by
    rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hBN']
    exact comap_mono hSB
  let b := subgroupOfEquivOfLe hBN'
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let c := e.subgroupMap A
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  have ht := binary_three_max5_local_eq_top (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    ((map_mono (f := e.toMonoidHom) hn).trans (A.le_normalizer_map e.toMonoidHom))
    (cq.symm.trans (bq.trans eB))
  have hA : A = ⊤ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [ht,map_top_of_surjective _ e.surjective]
  have he : B = N := le_antisymm hBN' (subgroupOf_eq_top.mp hA)
  refine ⟨⟨g⁻¹*h,?_⟩,he.symm ▸ hSN,
    le_antisymm (hBN.trans_eq he.symm) B.le_normalizer⟩
  rw [he,map_conj_product,hN',←map_conj_product,inv_mul_cancel,map_one]
  exact map_id _

/-- The same actual Held subgroup has central two-core center, transported
from its native max5 recognition through the original conjugation. -/
theorem binary_three_held_core_center_central
    (S : Sylow 2 Held.He) (B : Subgroup Held.He)
    (hB : B ∈ localCComponents S) (hSB : (S : Subgroup Held.He) ≤ normalizer (B : Set Held.He))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) :
    (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  obtain ⟨⟨g,hg⟩,_,_⟩ := binary_three_held_actual_max5 S B hB hSB eB
  let e : B ≃* Held.TwoLocalCandidates.subgroup 2 :=
    ((MulAut.conj g).subgroupMap B).trans (MulEquiv.subgroupCongr hg)
  have hm : ((center (pCore 2 B)).map (pCore 2 B).subtype).map e.toMonoidHom =
      (center (pCore 2 (Held.TwoLocalCandidates.subgroup 2))).map
        (pCore 2 (Held.TwoLocalCandidates.subgroup 2)).subtype := by
    rw [map_map,←map_center_image_of_injective _ _ e.injective,pCore_map_iso]
  intro x hx
  have hz := Held.TwoLocalCandidates.max5_core_center_central
    (hm ▸ mem_map_of_mem e.toMonoidHom hx)
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using mem_center_iff.mp hz (e y)


open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry Sporadic.Mathieu.M23Geometry.SylowTwoLocals
private theorem triple_seven_free : ¬ 7 ∣ Nat.card tripleStabilizer := by
  open TripleSolvable in
  have hmark : ¬ 7 ∣ Nat.card markedStabilizer := by
    let K := markedPointStabilizer
    have hc : Nat.card K = 1920 := by
      rw [←Nat.card_congr firstEquivMarkedPoint.toEquiv]
      exact m22PairStabilizer_card
    have hi : K.index ≤ 3 := by
      rw [MulAction.index_stabilizer]
      have ho : MulAction.orbit markedStabilizer (9 : Fin 23) ⊆
          (markedTriple : Set (Fin 23)) := by
        intro x hx
        obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hx
        have hm : (9 : Fin 23) ∈ markedTriple := by simp [m22M23AugmentedBlock]
        have hg := Finset.smul_mem_smul_finset (a := g.val) hm
        rwa [show g.val • markedTriple = markedTriple from g.property] at hg
      have hh := Set.ncard_le_ncard ho
      have ht : markedTriple.card = 3 := by decide +kernel
      simpa only [Set.ncard_coe_finset,ht] using hh
    have hp : 0 < K.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
    intro hd
    rw [←K.card_mul_index,hc] at hd
    rcases (by decide : Nat.Prime 7).dvd_mul.mp hd with hd | hd
    · norm_num at hd
    · have hh := Nat.le_of_dvd hp hd
      omega
  obtain ⟨g,hg⟩ := TripleSolvable.exists_triple_transport
  let e : tripleStabilizer ≃* TripleSolvable.markedStabilizer :=
    MulAction.stabilizerEquivStabilizer hg.symm
  rwa [Nat.card_congr e.toEquiv]

private theorem aligned_m23_normalizer_le_heptad (B : Subgroup M23)
    (hB : B ∈ localCComponents FusionCertificate.sylow)
    (hSB : FusionCertificate.subgroup ≤ normalizer (B : Set M23))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) :
    normalizer (B : Set M23) ≤ MulAction.stabilizer M23 FourNormalizers.fixedSet := by
  have hc := binary_three_core_ne_bot_of_even FusionCertificate.sylow hB hSB eB
    (MainConverse.m23_evenCharacteristic _) (by rw [m23_order]; decide)
  obtain ⟨N,hN,hBN,hSN⟩ := maximal_overgroup_of_core FusionCertificate.sylow hSB hc
  obtain ⟨R,hR,_,he,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le
    FusionCertificate.sylow hN hSN
  let A := R.map (FusionCertificate.sylow : Subgroup M23).subtype
  have hAS : A ≤ FusionCertificate.subgroup := map_subtype_le R
  have hAN : FusionCertificate.subgroup ≤ normalizer (A : Set M23) := hNR ▸ hSN
  have hA : A ≠ ⊥ := fun h => hR ((map_eq_bot_iff_of_injective R
    (FusionCertificate.sylow : Subgroup M23).subtype_injective).mp h)
  let := he
  have hEA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  rcases SylowTwoLocals.Coverage.normal_elementary_normalizer_coverage A hAS hAN hA hEA
    with hh | ht
  · exact hBN.trans (hNR ▸ hh)
  · have hBT : B ≤ MulAction.stabilizer M23 SylowTwoLocals.Coverage.fixedTriple :=
      (B.le_normalizer.trans hBN).trans (hNR ▸ ht)
    have h7 := ((by decide : 7 ∣ 168).trans (binary_three_card_dvd eB)).trans
      (card_dvd_of_le hBT)
    obtain ⟨g,hg⟩ := SylowTwoLocals.Coverage.triple_stabilizer_conjugate
      SylowTwoLocals.Coverage.fixedTriple (by decide +kernel)
    rw [hg,card_map_of_injective (MulAut.conj g).injective] at h7
    exact (triple_seven_free h7).elim

/-- Conjugating the original full Sylow to the native marking places the
entire normalizer of the same binary-three subgroup in the fixed heptad
stabilizer. The original subgroup, Sylow and conjugation are retained. -/
theorem binary_three_mathieuTwentyThree_heptad_placement
    (S : Sylow 2 M23) (B : Subgroup M23) (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup M23) ≤ normalizer (B : Set M23))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) :
    ∃ g : M23, (S : Subgroup M23).map (MulAut.conj g).toMonoidHom = FusionCertificate.subgroup ∧
      (normalizer (B : Set M23)).map (MulAut.conj g).toMonoidHom ≤
        MulAction.stabilizer M23 FourNormalizers.fixedSet := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 S FusionCertificate.sylow
  let a := MulAut.conj g
  have hS : (S : Subgroup M23).map a.toMonoidHom = FusionCertificate.subgroup :=
    congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot a.injective]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom
  have hn := (map_mono (f := a.toMonoidHom) hSB).trans (B.le_normalizer_map a.toMonoidHom)
  rw [hS] at hl hn
  let b := a.subgroupMap B
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  refine ⟨g,hS,?_⟩
  rw [map_normalizer_eq_of_bijective B a.bijective]
  exact aligned_m23_normalizer_le_heptad _ hl hn (bq.symm.trans eB)

private theorem core_center_central_of_equiv
    {A H : Type*} [Group A] [Group H] (e : A ≃* H)
    (hh : (center (pCore 2 H)).map (pCore 2 H).subtype ≤ center H) :
    (center (pCore 2 A)).map (pCore 2 A).subtype ≤ center A := by
  have hm : ((center (pCore 2 A)).map (pCore 2 A).subtype).map e.toMonoidHom =
      (center (pCore 2 H)).map (pCore 2 H).subtype := by
    rw [map_map,←map_center_image_of_injective _ _ e.injective,pCore_map_iso]
  intro x hx
  have hz := hh (hm ▸ mem_map_of_mem e.toMonoidHom hx)
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using mem_center_iff.mp hz (e y)

/-- The Held placement applies to the original B≤K inside X. Restriction
keeps the full original Sylow intersection and the actual two-core quotient.
No normality of K or quasisimplicity of B is assumed. -/
theorem binary_three_containing_held_placement
    {X : Type*} [Group X] [Finite X] (T : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup X) ≤ normalizer (B : Set X))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) (eK : K ≃* Held.He) :
    Nonempty (B ≃* Held.TwoLocalCandidates.subgroup 2) ∧
      (T : Subgroup X) ⊓ K ≤ B ∧ normalizer (B : Set X) ⊓ K = B ∧
      (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  obtain ⟨S,hS,hl,hn⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK hTB
  let A := B.subgroupOf K
  let a := subgroupOfEquivOfLe hBK
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let c := eK.subgroupMap A
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let : Group.IsSolvable eK.toMonoidHom.ker := by
    rw [eK.toMonoidHom.ker_eq_bot eK.injective]
    infer_instance
  let P := S.mapSurjective (f := eK.toMonoidHom) eK.surjective
  let D := A.map eK.toMonoidHom
  have hlD : D ∈ localCComponents P :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl eK.toMonoidHom
  have hnD : (P : Subgroup Held.He) ≤ normalizer (D : Set Held.He) :=
    (map_mono (f := eK.toMonoidHom) hn).trans (A.le_normalizer_map eK.toMonoidHom)
  let eD := cq.symm.trans (aq.trans eB)
  obtain ⟨⟨g,hg⟩,hPD,hND⟩ := binary_three_held_actual_max5 P D hlD hnD eD
  let d : B ≃* Held.TwoLocalCandidates.subgroup 2 :=
    a.symm.trans (c.trans (((MulAut.conj g).subgroupMap D).trans (MulEquiv.subgroupCongr hg)))
  have hSA : (S : Subgroup K) ≤ A := (map_le_map_iff_of_injective eK.injective).mp hPD
  have hNA : normalizer (A : Set K) = A := by
    apply map_injective (f := eK.toMonoidHom) eK.injective
    rw [map_normalizer_eq_of_bijective A eK.bijective]
    exact hND
  refine ⟨⟨d⟩,?_,?_,core_center_central_of_equiv d Held.TwoLocalCandidates.max5_core_center_central⟩
  · have hm := map_mono (f := K.subtype) hSA
    simpa only [hS,A,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hBK] using hm
  · have hm := congrArg (Subgroup.map K.subtype) hNA
    rw [←subgroupOf_normalizer_eq hBK,subgroupOf_map_subtype,
      map_subgroupOf_eq_of_le hBK] at hm
    exact hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

