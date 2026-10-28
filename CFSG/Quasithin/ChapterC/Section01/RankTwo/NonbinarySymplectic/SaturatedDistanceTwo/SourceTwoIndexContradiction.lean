module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoFixedCoreIndex

/-!
# The fixed-core index contradiction and midpoint containment

Let T₁ = T₀D′ and P = U′D′. Fixed-vector lifting through the original
central cover identifies the fixed preimage in U′ with its actual
centralizer under D. Since [T₀,D] = 1, the image of T₁ ∩ P is fixed
modulo D′. The displacement index q² therefore gives [P : T₁ ∩ P] ≥ q².
The cubic radical quotient and the order-q T₀ image also give
[T : T₁P] ≥ q². The upper bound [T : T₁] ≤ q⁴ forces equality throughout.

Consequently the full displacement C = [Z′,D] lies in T₁ ∩ D. It has
order q² and is disjoint from D′, while [D : D ∩ T₁] ≥ q³. Thus
[D : D ∩ D′] ≥ q⁵, contradicting its proved upper bound q⁴.
This excludes large movement. The previously proved small-movement
argument now yields [Z′,Q] ≤ Z_t without any extra index hypothesis.

Both complete fixed cores, the literal critical path and the genuine
saturation premise remain unchanged.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.7)(2), printed pp.873--874.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative commutatorElement

private theorem cover_commutatorPreimage_le_fixed
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A D : Subgroup G) (j : Multiplicative W →* G) (_hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hUD : U ≤ normalizer (D : Set G))
    (hker : ∀ w, p w=0 ↔ j (Multiplicative.ofAdd w) ∈ D) :
    commutatorPreimage U A D ≤ centralizer (A : Set G) := by
  intro x hx a ha
  have hxU := commutatorPreimage_le U A D hx
  obtain ⟨w,rfl⟩ := (hjr.symm ▸ hxU : x ∈ j.range)
  have hm : j (Multiplicative.ofAdd (σ (β ⟨a,ha⟩) w.toAdd-w.toAdd)) ∈ D := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    change ⁅a,j w⁆ ∈ D
    apply commutator_commutatorPreimage_le U A D hUD
    rw [commutator_comm]
    exact commutator_mem_commutator ha hx
  have hf : σ (β ⟨a,ha⟩) w.toAdd-w.toAdd ∈ fixed σ := by
    rw [cover_fixed_kernel p hp]
    exact (hker _).mpr hm
  have he := congrArg (fun v => j (Multiplicative.ofAdd v))
    (cover_displacement_fixed p hp (β ⟨a,ha⟩) w.toAdd hf)
  rw [hact,ofAdd_toAdd,mul_inv_eq_iff_eq_mul] at he
  exact he

private theorem relative_sup_index {G : Type*} [Group G]
    (T A N : Subgroup G) (hAT : A ≤ T) (hNT : N ≤ T)
    (hn : T ≤ normalizer (N : Set G)) : N.relIndex (A ⊔ N)=N.relIndex A := by
  let : (N.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hn
  rw [←relIndex_subgroupOf (sup_le hAT hNT),subgroupOf_sup hAT hNT,
    relIndex_sup_right,relIndex_subgroupOf hAT]

private theorem source_index_contradiction
    {G : Type*} [Group G] (T B D E Q U C : Subgroup G) [Finite T]
    (q : ℕ) (hq : 1 < q)
    (hBT : B ≤ T) (hDT : D ≤ T) (hEQ : E ≤ Q) (hUQ : U ≤ Q) (hQT : Q ≤ T)
    (hBn : T ≤ normalizer (B : Set G)) (hDn : T ≤ normalizer (D : Set G))
    (hEn : T ≤ normalizer (E : Set G)) (hQn : T ≤ normalizer (Q : Set G))
    (hUn : T ≤ normalizer (U : Set G))
    (hBD : ⁅B,D⁆=⊥) (hCU : C ≤ U) (hCD : C ≤ D) (hCf : ⁅C,D⁆=⊥)
    (hCe : Disjoint C E) (hCc : Nat.card C=q^2)
    (hmove : (centralizer (D : Set G)).relIndex U=q^2)
    (hpre : commutatorPreimage U D E ≤ centralizer (D : Set G))
    (hQindex : Q.relIndex T=q^3) (hBimage : Q.relIndex B=q)
    (hDindex : E.relIndex D ≤ q^4)
    (hupper : (B ⊔ E).relIndex T ≤ q^4)
    (hpart : (B ⊔ D).relIndex T ≤ q) : False := by
  let J := B ⊔ E
  let P := U ⊔ E
  let N := commutatorPreimage P D E
  have hET := hEQ.trans hQT
  have hUT := hUQ.trans hQT
  have hJT : J ≤ T := sup_le hBT hET
  have hPT : P ≤ T := sup_le hUT hET
  have hPn : T ≤ normalizer (P : Set G) :=
    (le_inf hUn hEn).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJn : T ≤ normalizer (J : Set G) :=
    (le_inf hBn hEn).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hNP : N ≤ P := commutatorPreimage_le _ _ _
  have hNT : N ≤ T := hNP.trans hPT
  have hNn : T ≤ normalizer (N : Set G) :=
    commutatorPreimage_normalized P D E T (hPT.trans hEn) hPn hDn hEn
  have hEN : E ≤ N := le_commutatorPreimage le_sup_right
    (le_normalizer_iff_commutator_le_left.mp (hDT.trans hEn))
  have hJP : J ⊓ P ≤ N := by
    apply le_commutatorPreimage inf_le_right
    apply (commutator_mono inf_le_left le_rfl).trans
    exact commutator_sup_le_of_relative_normal T B E D E hEn hBT hET
      (hBD ▸ bot_le) (le_normalizer_iff_commutator_le_left.mp (hDT.trans hEn))
  let : Finite P := Finite.of_injective (inclusion hPT) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion hNT) (inclusion_injective _)
  let : Finite U := Finite.of_injective (inclusion hUT) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDT) (inclusion_injective _)
  have hNU : N ⊓ U ≤ centralizer (D : Set G) := by
    apply (le_commutatorPreimage (show N ⊓ U ≤ U from inf_le_right) ?_).trans hpre
    exact (commutator_mono inf_le_left le_rfl).trans
      (commutator_commutatorPreimage_le P D E (hPT.trans hEn))
  have hNindex : q^2 ≤ N.relIndex P := by
    have hPN : P ⊔ N=U ⊔ N := by
      apply le_antisymm
      · exact sup_le (sup_le le_sup_left (hEN.trans le_sup_right)) le_sup_right
      · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    have hh : N.relIndex P=N.relIndex U := by
      rw [←relative_sup_index T P N hPT hNT hNn,hPN,
        relative_sup_index T U N hUT hNT hNn]
    rw [hh,←inf_relIndex_right]
    exact hmove ▸ relIndex_le_of_le_left hNU index_ne_zero_of_finite
  have hJPlower : q^2 ≤ J.relIndex P := by
    have hh := relIndex_le_of_le_left (L := P) hJP index_ne_zero_of_finite
    rw [inf_relIndex_right] at hh
    exact hNindex.trans hh
  have hBQ : (B ⊔ Q).relIndex T=q^2 := by
    have hh := relIndex_mul_relIndex Q (B ⊔ Q) T le_sup_right (sup_le hBT hQT)
    rw [relative_sup_index T B Q hBT hQT hQn,hBimage,hQindex] at hh
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < q)
    nlinarith only [hh]
  have hjoinle : J ⊔ P ≤ B ⊔ Q :=
    sup_le (sup_le le_sup_left (hEQ.trans le_sup_right))
      (sup_le (hUQ.trans le_sup_right) (hEQ.trans le_sup_right))
  have hjoinlower : q^2 ≤ (J ⊔ P).relIndex T := by
    rw [←hBQ]
    exact relIndex_le_of_le_left hjoinle index_ne_zero_of_finite
  have hmul := relIndex_mul_relIndex J (J ⊔ P) T le_sup_left (sup_le hJT hPT)
  rw [sup_comm J P,relative_sup_index T P J hPT hJT hJn,sup_comm P J] at hmul
  have hJlower : q^4 ≤ J.relIndex T := by
    rw [←hmul]
    calc
      q^4 = q^2*q^2 := by ring
      _ ≤ J.relIndex P * (J ⊔ P).relIndex T := Nat.mul_le_mul hJPlower hjoinlower
  have hJeq : J.relIndex T=q^4 := le_antisymm hupper hJlower
  have hJPeq : J.relIndex P=q^2 := by
    apply le_antisymm ?_ hJPlower
    have hh := (Nat.mul_le_mul_left (J.relIndex P) hjoinlower).trans_eq hmul
    rw [hJeq] at hh
    have hh' : J.relIndex P*q^2 ≤ q^2*q^2 := by nlinarith only [hh]
    exact Nat.le_of_mul_le_mul_right hh' (by positivity)
  have hNJ : N ≤ J := by
    have hh := relIndex_mul_relIndex (J ⊓ P) N P hJP hNP
    rw [inf_relIndex_right,hJPeq] at hh
    have hlo := Nat.mul_le_mul_left ((J ⊓ P).relIndex N) hNindex
    have hle : (J ⊓ P).relIndex N ≤ 1 := by
      have hh' : (J ⊓ P).relIndex N * q^2 ≤ 1 * q^2 := by
        simpa only [one_mul] using hlo.trans_eq hh
      exact Nat.le_of_mul_le_mul_right hh' (by positivity)
    have hpos : 0 < (J ⊓ P).relIndex N := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hone : (J ⊓ P).relIndex N=1 := by omega
    exact (relIndex_eq_one.mp hone).trans inf_le_left
  have hCJ : C ≤ J := (le_commutatorPreimage (hCU.trans le_sup_left) (hCf ▸ bot_le)).trans hNJ
  have hCi : E.relIndex C=q^2 := by
    rw [←inf_relIndex_right,inf_comm,hCe.eq_bot,relIndex_bot_left,hCc]
  have hCDJ : q^2 ≤ E.relIndex (J ⊓ D) := by
    rw [←hCi]
    let : Finite (J ⊓ D : Subgroup G) := Finite.of_injective
      (inclusion (show J ⊓ D ≤ D from inf_le_right)) (inclusion_injective _)
    exact relIndex_le_of_le_right (le_inf hCJ hCD) index_ne_zero_of_finite
  have hDlow : q^3 ≤ J.relIndex D := by
    have hi : J.relIndex T ≤ (B ⊔ D).relIndex T * J.relIndex D := by
      have hbD := relIndex_mul_relIndex J (J ⊔ D) T le_sup_left (sup_le hJT hDT)
      rw [sup_comm J D,relative_sup_index T D J hDT hJT hJn,sup_comm D J] at hbD
      rw [←hbD]
      have hl : (J ⊔ D).relIndex T ≤ (B ⊔ D).relIndex T :=
        relIndex_le_of_le_left (sup_le (le_sup_left.trans le_sup_left) le_sup_right) index_ne_zero_of_finite
      exact (Nat.mul_le_mul_left _ hl).trans_eq (Nat.mul_comm _ _)
    rw [hJeq] at hi
    have hh := hi.trans (Nat.mul_le_mul_right _ hpart)
    have hh' : q * q^3 ≤ q * J.relIndex D := by nlinarith only [hh]
    exact Nat.le_of_mul_le_mul_left hh' (by omega)
  have hh := relIndex_inf_mul_relIndex E J D
  rw [inf_eq_left.mpr (show E ≤ J from le_sup_right)] at hh
  have hbad := (Nat.mul_le_mul hCDJ hDlow).trans (hh.trans_le hDindex)
  have hp : q^4 < q^5 := Nat.pow_lt_pow_right hq (by decide)
  apply hp.not_ge
  nlinarith only [hbad]

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The fixed-core index squeeze excludes the large-movement branch with
both full fixed attachments and the actual point-radical cover retained. -/
theorem source_two_large_movement_false
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) : False := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  obtain ⟨pc⟩ := source_two_large_radical_point_cover h d g hb hsat path hat hzt c c' hlarge
  have hUQ : U d.radical z ≤ Q d.radical z := (U_le_Z z).trans
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _))
  have hDT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  have hUT : U d.radical z ≤ Q d.radical t := hUQ.trans c'.core_le_edge
  let β := pc.actor.comp (inclusion hDT)
  have hker (w : s.space.toSubmodule) : MovedSection.coverProjection s pc.equiv w=0 ↔
      pc.embedding (Multiplicative.ofAdd w) ∈ fixedCore d.radical z := by
    rw [pc.kernel w]
    exact ⟨fun hw => ⟨hUQ (pc.range_eq ▸ ⟨_,rfl⟩),hw⟩,fun hw => hw.2⟩
  have hpre := cover_commutatorPreimage_le_fixed
    (MovedSection.coverAction s pc.equiv) (MovedSection.coverProjection s pc.equiv) pc.cover
    (U d.radical z) (fixedCore d.radical a) (fixedCore d.radical z)
    pc.embedding pc.injective pc.range_eq β
    (fun x => pc.actor_conjugation (inclusion hDT x)) (hUT.trans c'.fixedCore_normalized) hker
  have hBD : ⁅componentRadical d a t,fixedCore d.radical a⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply (show componentRadical d a t ≤ Ltilde d.radical a from inf_le_right).trans
    exact le_centralizer_iff.mpr (show fixedCore d.radical a ≤
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) from inf_le_right)
  let C := ⁅Z d.radical z,fixedCore d.radical a⁆
  have hCU : C ≤ U d.radical z := by
    rw [show C=⁅U d.radical z,fixedCore d.radical a⁆ from
      fixedCore_displacement_eq_moving h d g hb path hat hzt c c']
    exact le_normalizer_iff_commutator_le_left.mp
      (hDT.trans (c'.edge_le.trans (U_normalized z)))
  have hZzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b d.radical
    omega
  have hCD : C ≤ fixedCore d.radical a :=
    le_normalizer_iff_commutator_le_right.mp (hZzT.trans c.fixedCore_normalized)
  have hCf : ⁅C,fixedCore d.radical a⁆=⊥ :=
    source_two_fixedCore_quadratic h d g hb hsat path hat hzt c c'
  have hCe := (source_two_large_displacement_disjoint_opposite_fixedCore
    h d g hb hsat path hat hzt c c' hlarge).1
  have hCc := (source_two_large_fixed_attachment_displacement_card
    h d g hb hsat path hat hzt c c' hlarge).2.2.1
  exact source_index_contradiction (Q d.radical t) (componentRadical d a t)
    (fixedCore d.radical a) (fixedCore d.radical z) (Q d.radical z) (U d.radical z) C
    (2^n) (one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega))
    inf_le_left hDT inf_le_left hUQ c'.core_le_edge
    c.componentRadical_normalized c.fixedCore_normalized c'.fixedCore_normalized
    (c'.edge_le.trans (Q_normalized d.radical z)) (c'.edge_le.trans (U_normalized z))
    hBD hCU hCD hCf hCe hCc
    (source_two_large_fixedCore_movement_eq_square h d g hb hsat path hat hzt c c' hlarge)
    hpre (source_two_large_full_radical_card h d g hb hsat path hat hzt c c' hlarge)
    (source_two_large_movement_images h d g hb hsat path hat hzt c c' hlarge).1
    (source_two_large_fixedCore_overlap_index_le h d g hb hsat path hat hzt c c' hlarge).2
    (source_two_large_component_fixedCore_index_upper h d g hb hsat path hat hzt c c' hlarge).2
    (componentRadical_fixedCore_relIndex h d g hb path.start_color c).2

/-- The midpoint containment of MS93 (3.7)(2), with no extra movement bound. -/
theorem source_two_midpoint_containment
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    ⁅Z d.radical z,Q d.radical a⁆ ≤ Z d.radical t := by
  apply source_two_of_small_core_movement h d g hb hsat path hat hzt c c'
  exact le_of_not_gt (source_two_large_movement_false h d g hb hsat path hat hzt c c')

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
