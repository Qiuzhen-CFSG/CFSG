module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallNormalizer
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.FourGroupDisplacement

/-!
# The small critical line under the first-edge normalizer

When a critical endpoint has relative seed index less than four, its
commutator line has order two. The literal first-edge normalizer has
centralizer index at most two on that line. Its orbit span in the starting
moving layer therefore has order at most four, and the whole normalizer acts
quadratically on the span. If it moves the critical line, the span has order
exactly four and its displacement is a fixed line of order two. This
dichotomy holds at every original component vertex. The base-edge statements
identify the acting group with the restricted original Sylow subgroup under
the actual graph embedding.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5)--(5.8), pp.917--920, and the small-line argument following
(5.11), pp.923--924. These selected-line estimates do not bound the whole
point core or exclude the terminal branches.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowMovingLine
open SylowSmallNormalizer
universe u

private theorem card_sup_le_mul {G : Type*} [Group G]
    (A B : Subgroup G) [Finite A] [Finite B]
    (hn : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  let m : A × B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem_sup p.1.property p.2.property⟩
  have hs : Function.Surjective m := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A B hn]
      exact x.property
    obtain ⟨a,ha,b,hb,he⟩ := hx
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),Subtype.ext he⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective m hs

private theorem line_orbit_data {G : Type*} [Group G]
    (D T V : Subgroup G) [Finite T] [Finite V] [IsElementaryAbelian 2 V]
    (hDV : D ≤ V) (hTV : T ≤ normalizer (V : Set G))
    (hD : Nat.card D = 2)
    (hi : (centralizer (D : Set G)).relIndex T ≤ 2) :
    let W := componentOrbit D T
    W ≤ V ∧ Nat.card W ≤ 4 ∧
      T ⊓ centralizer (D : Set G) = T ⊓ centralizer (W : Set G) ∧
      ⁅⁅W,T⁆,T⁆ = ⊥ := by
  let C := centralizer (D : Set G)
  let W := componentOrbit D T
  change C.relIndex T ≤ 2 at hi
  change W ≤ V ∧ Nat.card W ≤ 4 ∧
    T ⊓ C = T ⊓ centralizer (W : Set G) ∧ ⁅⁅W,T⁆,T⁆ = ⊥
  have hWV : W ≤ V := by
    apply iSup_le
    intro t
    exact (map_mono hDV).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hTV t.property))
  let : Finite W := Finite.of_injective (inclusion hWV) (inclusion_injective hWV)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  have hpos : 0 < C.relIndex T := Nat.pos_of_ne_zero (C.subgroupOf T).index_ne_zero_of_finite
  have he : C.relIndex T = 1 ∨ C.relIndex T = 2 := by omega
  have hWT : T ≤ normalizer (W : Set G) := le_normalizer_componentOrbit D T
  rcases he with he | he
  · have hTC : T ≤ C := relIndex_eq_one.mp he
    have hWD : W = D := by
      apply le_antisymm ?_ (le_componentOrbit D T)
      apply iSup_le
      intro t
      exact (mem_normalizer_iff_map_conj_eq.mp
        (centralizer_le_normalizer (D : Set G) (hTC t.property))).le
    rw [hWD]
    refine ⟨hDV, by omega, rfl, ?_⟩
    have hz : ⁅D,T⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hTC
    rw [hz,commutator_bot_left]
  · have hn : (C.subgroupOf T).Normal := normal_of_index_eq_two he
    have hCQ : T ≤ normalizer ((T ⊓ C : Subgroup G) : Set G) := by
      apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
      simpa only [inf_subgroupOf_left] using hn
    have hQW : T ⊓ C ≤ centralizer (W : Set G) := by
      rw [le_centralizer_iff]
      apply iSup_le
      intro t x hx q hq
      obtain ⟨d,hd,rfl⟩ := hx
      have hqc : (t : G)⁻¹ * q * t ∈ C := by
        have hh := (mem_normalizer_iff.mp (hCQ (T.inv_mem t.property)) q).mp hq
        exact (by simpa only [inv_inv] using hh :
          (t : G)⁻¹ * q * t ∈ T ⊓ C).2
      have hc : d * ((t : G)⁻¹ * q * t) = ((t : G)⁻¹ * q * t) * d := hqc d hd
      symm
      change (t : G) * d * (t : G)⁻¹ * q = q * ((t : G) * d * (t : G)⁻¹)
      calc
        _ = (t : G) * (d * ((t : G)⁻¹ * q * t)) * (t : G)⁻¹ := by group
        _ = (t : G) * (((t : G)⁻¹ * q * t) * d) * (t : G)⁻¹ := by rw [hc]
        _ = _ := by group
    have hce : T ⊓ C = T ⊓ centralizer (W : Set G) :=
      le_antisymm (le_inf inf_le_left hQW)
        (inf_le_inf_left T (centralizer_le (le_componentOrbit D T)))
    have hcard : Nat.card W ≤ 4 := by
      have hnt : ¬ T ≤ C := by
        intro ht
        have hh := relIndex_eq_one.mpr ht
        omega
      obtain ⟨t,ht,hnt⟩ := Set.not_subset.mp hnt
      have hw := componentOrbit_eq_sup_of_index_two D T C he
        (inf_le_right.trans (centralizer_le_normalizer (D : Set G))) ht hnt
      let D' := D.map (MulAut.conj t).toMonoidHom
      have hD'V : D' ≤ V := (map_mono hDV).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (hTV ht))
      let : Finite D := Nat.finite_of_card_ne_zero (by omega)
      let : Finite D' := Finite.of_injective (inclusion hD'V) (inclusion_injective hD'V)
      have hD'n : D' ≤ normalizer (D : Set G) := by
        apply le_trans ?_ (centralizer_le_normalizer (D : Set G))
        intro x hx y hy
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := V)).comm ⟨y,hDV hy⟩ ⟨x,hD'V hx⟩)
      have hh := card_sup_le_mul D D' hD'n
      rw [card_map_of_injective (MulAut.conj t).injective,hD] at hh
      change Nat.card (componentOrbit D T) ≤ 4
      rw [hw]
      exact hh
    refine ⟨hWV,hcard,hce,?_⟩
    exact commutator_commutator_eq_bot_of_centralizing_index_two W (T ⊓ C) T
      hWT inf_le_left hQW (by rwa [inf_relIndex_left])

private theorem moving_line_orbit_four {G : Type*} [Group G]
    (D T V : Subgroup G) [Finite V]
    (hDV : D ≤ V) (hTV : T ≤ normalizer (V : Set G))
    (hD : Nat.card D = 2) (hcard : Nat.card (componentOrbit D T) ≤ 4)
    (hmove : ¬ T ≤ centralizer (D : Set G)) :
    Nat.card (componentOrbit D T) = 4 := by
  let W := componentOrbit D T
  have hWV : W ≤ V := by
    apply iSup_le
    intro t
    exact (map_mono hDV).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hTV t.property))
  let : Finite W := Finite.of_injective (inclusion hWV) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDV) (inclusion_injective _)
  have hDW : D ≤ W := le_componentOrbit D T
  have hlow : 2 ≤ Nat.card W := by simpa only [hD] using card_le_of_le hDW
  have hdvd : 2 ∣ Nat.card W := by simpa only [hD] using card_dvd_of_le hDW
  have hne : Nat.card W ≠ 2 := by
    intro he
    have heq : D = W := eq_of_le_of_card_ge hDW (by rw [hD,he])
    apply hmove
    rw [heq]
    exact (le_normalizer_componentOrbit D T).trans
      (normalizer_le_centralizer_of_card_two _ he)
  change Nat.card W ≤ 4 at hcard
  change Nat.card W = 4
  omega

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The critical-line orbit for the literal first-edge relative normalizer. -/
theorem small_critical_line_orbit_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let W := componentOrbit D T
    W ≤ U d.radical a ∧ Nat.card W ≤ 4 ∧
      T ⊓ centralizer (D : Set (FreeAmalgam d.radical)) =
        T ⊓ centralizer (W : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅W,T⁆,T⁆ = ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical a
  have hDcard : Nat.card D = 2 := small_critical_commutator_card s hc p hsmall
  have hDU : D ≤ U d.radical a :=
    (critical_Z_commutator_le_moving (h := h) p).trans inf_le_left
  have hTU : T ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (U_normalized a)
  let : Finite (Z d.radical a) := finite_Z d.radical a
  let : IsElementaryAbelian 2 (Z d.radical a) :=
    (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (U d.radical a) :=
    IsElementaryAbelian.of_le (DistanceEight.U_le_Z d.radical a)
  let : Finite (stabilizer d.radical a) := finite_stabilizer d.radical a
  let : Finite T := Finite.of_injective
    (inclusion (show T ≤ stabilizer d.radical a from inf_le_right)) (inclusion_injective _)
  have hi := small_line_relative_centralizer_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  exact line_orbit_data D T (U d.radical a) hDU hTU hDcard hi

include e hz hn in
/-- The orbit bound with the original restricted Sylow at the actual base edge. -/
theorem small_base_critical_line_orbit_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex
      (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let D := ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let W := componentOrbit D T
    W ≤ U d.radical (alpha d.radical) ∧ Nat.card W ≤ 4 ∧
      T ⊓ centralizer (D : Set (FreeAmalgam d.radical)) =
        T ⊓ centralizer (W : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅W,T⁆,T⁆ = ⊥ := by
  have hd := small_critical_line_orbit_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hd ⊢
  rw [hfirst,four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb] at hd
  exact hd

include e hz hn in
private theorem first_edge_normalizer_isPGroup
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    IsPGroup 2 ↥(normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a) := by
  obtain ⟨he,⟨P,hP⟩,_⟩ := four_lt_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have ht : IsPGroup 2 ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) :=
    hP.trans he ▸ P.isPGroup'
  have hp := ht.map (embedM d.radical)
  rw [←four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb] at hp
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g, hg | hg⟩ :=
    (adjacent_iff_exists_common d.radical a (p.walk.getVert 1)).mp hat
  · have hbase : act d.radical g⁻¹ a = alpha d.radical := by
      rw [hg.1, act_mVertex, mul_inv_cancel]
      rfl
    have hfirst : act d.radical g⁻¹ (p.walk.getVert 1) = beta d.radical := by
      rw [hg.2, act_hVertex, mul_inv_cancel]
      rfl
    have hrestore (v : Vertex d.radical) :
        act d.radical g (act d.radical g⁻¹ v) = v := by
      rw [← act_mul, inv_mul_cancel, act_one]
    have hh := hp.map (MulAut.conj g⁻¹).toMonoidHom
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      ←Q_act,←stabilizer_act,←hbase,←hfirst,hrestore,hrestore] at hh
    exact hh
  · have ha := p.start_color
    rw [hg.1] at ha
    cases ha

include e hz hn in
/-- At every original component vertex the first-edge normalizer either fixes
the critical line or has a four-group orbit with a fixed displacement line. -/
theorem small_critical_line_dichotomy_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let W := componentOrbit D T
    T ≤ centralizer (D : Set (FreeAmalgam d.radical)) ∨
      (Nat.card W = 4 ∧ Nat.card (⁅W,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
        ⁅W,T⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical))) := by
  classical
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical a
  let W := componentOrbit D T
  change T ≤ centralizer (D : Set _) ∨
    (Nat.card W = 4 ∧ Nat.card (⁅W,T⁆ : Subgroup _) = 2 ∧
      ⁅W,T⁆ ≤ centralizer (T : Set _))
  by_cases hfix : T ≤ centralizer (D : Set _)
  · exact Or.inl hfix
  apply Or.inr
  have hdata := small_critical_line_orbit_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  have hWV : W ≤ U d.radical a := hdata.1
  have hcard : Nat.card W ≤ 4 := hdata.2.1
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hDcard : Nat.card D = 2 := small_critical_commutator_card s hc p hsmall
  have hDV : D ≤ U d.radical a :=
    (critical_Z_commutator_le_moving (h := h) p).trans inf_le_left
  have hTV : T ≤ normalizer (U d.radical a : Set _) :=
    inf_le_right.trans (U_normalized a)
  let : Finite (Z d.radical a) := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hWV) (inclusion_injective _)
  have hfour : Nat.card W = 4 := moving_line_orbit_four D T
    (U d.radical a) hDV hTV hDcard hcard hfix
  have hp : IsPGroup 2 T := first_edge_normalizer_isPGroup
    (e := e) (hz := hz) (hn := hn) hb p
  have hnW : T ≤ normalizer (W : Set _) := le_normalizer_componentOrbit D T
  have hne : ⁅W,T⁆ ≠ ⊥ := by
    intro he
    apply hfix
    have ht : T ≤ centralizer (W : Set _) :=
      commutator_eq_bot_iff_le_centralizer.mp (commutator_comm W T ▸ he)
    exact ht.trans (centralizer_le (le_componentOrbit D T))
  exact ⟨hfour,commutator_four_card_of_ne_bot W T hnW hp hfour hne,
    commutator_four_le_centralizer W T hnW hp hfour⟩

include e hz hn in
/-- The dichotomy for the restricted original Sylow at the actual base edge. -/
theorem small_base_line_dichotomy_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex
      (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let D := ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let W := componentOrbit D T
    T ≤ centralizer (D : Set (FreeAmalgam d.radical)) ∨
      (Nat.card W = 4 ∧ Nat.card (⁅W,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
        ⁅W,T⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical))) := by
  have hd := small_critical_line_dichotomy_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hd ⊢
  rw [hfirst,four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb] at hd
  exact hd

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowMovingLine
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
