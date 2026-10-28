module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCrossCommutator
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCriticalPlane
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCrossCommutator
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusGeometry

/-!
# Derived action and seed growth on the retained paired paths

For the two critical paths a--v--c--t--z and b--v'--c'--t'--z, put
I = (Z_z intersect Q_a) intersect (Z_z intersect Q_b),
P = [Z_a,Z_z] join [Z_b,Z_z], and D₀ = [Z_a,Z_b]. The reciprocal
critical-line actions make P a four-group without a nonzero fixed point
under Z_a join Z_b. The three-subgroups lemma shows that D₀ acts
nontrivially on P. An invariant proper nonzero subgroup of P would have
order two and hence be fixed. Thus D₀ moves all of P and fixes none of it.

Counting the two distinct full critical kernels gives Z_z = I times P,
with trivial intersection. Consequently C_{Z_z}(D₀) = I and [Z_z,D₀] = P.
This calculation retains the entire fixed subgroup, including its central
attachment; it does not identify that attachment with a critical line.

For the retained radii Y and Y', the full endpoint seed normalizes both,
and hence W = [Y,Y']. Since D₀ lies in W, the equality [Z_z,D₀] = P
places P inside W intersect Z_z. This intersection is normalized by Y,
whereas the earlier paired comparison says Y does not normalize P.
Therefore P is a proper subgroup of W intersect Z_z, whose order is at
least eight. The original paths, conjugator and generating edge are kept.

Whole-core and literal C.1.32 applications retain the actual cubic projection
with kernel E, its nontrivial odd E/Q, the proper odd-index radical, and
both moving covers of orders sixteen and thirty-two. This is a strengthened
paired commutator obstruction. The shifted comparison and terminal
contradiction, remaining branches, and both core exhaustions are still needed.
Internal imports reuse checked local calculations without widening their APIs.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), paired comparisons toward (5.12), printed pp.924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement

private theorem four_invariant_dichotomy {J : Type*} [Group J]
    (P A K : Subgroup J) (hcard : Nat.card P = 4)
    (hfixed : P ⊓ centralizer (A : Set J) = ⊥)
    (hKP : K ≤ P) (hn : A ≤ normalizer (K : Set J)) : K = ⊥ ∨ K = P := by
  let : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Finite K := Finite.of_injective (inclusion hKP) (inclusion_injective _)
  have hd := card_dvd_of_le hKP
  rw [hcard] at hd
  have hc : Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 4 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
    by_contra hn
    have hx : Nat.card K = 0 ∨ Nat.card K = 3 := by omega
    rcases hx with hx | hx <;> rw [hx] at hd <;> norm_num at hd
  rcases hc with hc | hc | hc
  · exact Or.inl (eq_bot_of_card_le _ hc.le)
  · left
    apply le_bot_iff.mp
    exact (le_inf hKP (le_centralizer_iff.mp
      (hn.trans (normalizer_le_centralizer_of_card_two K hc)))).trans_eq hfixed
  · exact Or.inr (eq_of_le_of_card_ge hKP (by omega))

private theorem normalizes_commutator {J : Type*} [Group J]
    (A B C : Subgroup J) (hB : A ≤ normalizer (B : Set J))
    (hC : A ≤ normalizer (C : Set J)) :
    A ≤ normalizer ((⁅B,C⁆ : Subgroup J) : Set J) := by
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hB ha),
    mem_normalizer_iff_map_conj_eq.mp (hC ha)]

private theorem four_derived_action {J : Type*} [Group J]
    (A B T U : Subgroup J)
    (hcard : Nat.card (T ⊔ U : Subgroup J) = 4)
    (hT : T ≠ ⊥) (hTA : ⁅T,A⁆ = ⊥)
    (hBT : ⁅B,T⁆ = U) (hUA : ⁅U,A⁆ = T)
    (hN : A ⊔ B ≤ normalizer ((T ⊔ U : Subgroup J) : Set J))
    (hF : (T ⊔ U) ⊓ centralizer ((A ⊔ B : Subgroup J) : Set J) = ⊥) :
    ⁅T ⊔ U,⁅A,B⁆⁆ = T ⊔ U ∧
      (T ⊔ U) ⊓ centralizer ((⁅A,B⁆ : Subgroup J) : Set J) = ⊥ := by
  let P := T ⊔ U
  let W := ⁅A,B⁆
  have hWN : A ⊔ B ≤ normalizer (W : Set J) :=
    sup_le (normalizer_commutator_ge_left _ _) (normalizer_commutator_ge_right _ _)
  have hWP : W ≤ normalizer (P : Set J) := (commutator_le_sup (H₁ := A) (H₂ := B)).trans hN
  have hnon : ⁅P,W⁆ ≠ ⊥ := by
    intro he
    have hWT : ⁅W,T⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
        (centralizer_le (show T ≤ P from le_sup_left)))
    have hh : ⁅⁅B,T⁆,A⁆ = ⊥ :=
      commutator_commutator_eq_bot_of_rotate
        (by rw [hTA,commutator_bot_left]) hWT
    rw [hBT,hUA] at hh
    exact hT hh
  have hmove : ⁅P,W⁆ = P :=
    (four_invariant_dichotomy P (A ⊔ B) ⁅P,W⁆ hcard hF
      (le_normalizer_iff_commutator_le_left.mp hWP)
      (normalizes_commutator _ _ _ hN hWN)).resolve_left hnon
  have hCF : A ⊔ B ≤ normalizer
      ((P ⊓ centralizer (W : Set J) : Subgroup J) : Set J) := by
    apply (le_inf hN ?_).trans inf_normalizer_le_normalizer_inf
    exact hWN.trans (normalizer_le_normalizer_centralizer W)
  have hfixed := four_invariant_dichotomy P (A ⊔ B)
    (P ⊓ centralizer (W : Set J)) hcard hF inf_le_left hCF
  refine ⟨hmove,hfixed.resolve_right ?_⟩
  intro he
  exact hnon (commutator_eq_bot_iff_le_centralizer.mpr (he ▸ inf_le_right))

open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The commutator of the two starting seeds has exactly the critical plane
as moved subgroup and the common full kernel as fixed subgroup. -/
theorem plane_reciprocal_seed_derived_action
    {a b z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) b z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg z).relIndex (Z Rg b) < 4)
    (hcross : ⁅Z Rg a,⁅Z Rg b,Z Rg z⁆⁆ = ⁅Z Rg a,Z Rg z⁆)
    (hcross' : ⁅Z Rg b,⁅Z Rg a,Z Rg z⁆⁆ = ⁅Z Rg b,Z Rg z⁆) :
    let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
    let P := ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg b,Z Rg z⁆
    let D₀ := ⁅Z Rg a,Z Rg b⁆
    Nat.card P = 4 ∧ I ⊔ P = Z Rg z ∧ I ⊓ P = ⊥ ∧
      Z Rg z ⊓ centralizer (D₀ : Set (FreeAmalgam Rg)) = I ∧
      ⁅Z Rg z,D₀⁆ = P := by
  let A := Z Rg a
  let B₀ := Z Rg b
  let Z₀ := Z Rg z
  let T := ⁅A,Z₀⁆
  let T' := ⁅B₀,Z₀⁆
  let P := T ⊔ T'
  let F := Z₀ ⊓ Q Rg a
  let F' := Z₀ ⊓ Q Rg b
  let I := F ⊓ F'
  let D₀ := ⁅A,B₀⁆
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) b q.start_color
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hTle := critical_commutator_le_seed h p
  have hT'le := critical_commutator_le_seed h q
  have hTcard : Nat.card T = 2 := small_critical_commutator_card h e hz hk p hp
  have hT'card : Nat.card T' = 2 := small_critical_commutator_card h e hz hk q hq
  have hTA : T ≤ centralizer (A : Set (FreeAmalgam Rg)) :=
    (hTle.trans inf_le_left).trans (le_centralizer (H := A))
  have hT'B : T' ≤ centralizer (B₀ : Set (FreeAmalgam Rg)) :=
    (hT'le.trans inf_le_left).trans (le_centralizer (H := B₀))
  obtain ⟨_,hPcard,hPN,_,_,hPF,_⟩ := reciprocal_lines_plane Z₀ A B₀ T T'
    (hTle.trans inf_le_right) (hT'le.trans inf_le_right) hTcard hT'card hTA hT'B hcross hcross'
  have hTne : T ≠ ⊥ := by intro he; rw [he,card_bot] at hTcard; omega
  have hT'ne : T' ≠ ⊥ := by intro he; rw [he,card_bot] at hT'card; omega
  have hderived := four_derived_action A B₀ T T' hPcard hTne
    (commutator_eq_bot_iff_le_centralizer.mpr hTA) hcross'
    ((commutator_comm T' A).trans hcross) hPN hPF
  have fixed {v : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) v z) :
      Z₀ ⊓ centralizer (Z Rg v : Set (FreeAmalgam Rg)) = Z₀ ⊓ Q Rg v := by
    apply critical_seed_centralizer_intersection h e
      (CriticalPath.ofPair (geometry := sourceGeometry h) r.end_color
        (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
          v r.start_color (by
            rw [(sourceGeometry h).distance_constant _ r.start_color]
            exact sourceDistance_pos h) z r.end_color r.critical))
  have hFA := fixed p
  have hFB := fixed q
  have hIC : I ≤ centralizer ((A ⊔ B₀ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp
      (inf_le_left.trans (hFA.symm.le.trans inf_le_right)))
      (le_centralizer_iff.mp (inf_le_right.trans (hFB.symm.le.trans inf_le_right)))
  have hPZ : P ≤ Z₀ := sup_le (hTle.trans inf_le_right) (hT'le.trans inf_le_right)
  have hIZ : I ≤ Z₀ := inf_le_left.trans inf_le_left
  have hdis : I ⊓ P = ⊥ := le_bot_iff.mp
    ((le_inf inf_le_right (inf_le_left.trans hIC)).trans_eq hPF)
  have hne : F ≠ F' := by
    intro he
    have hTF : T ≤ F := le_inf (hTle.trans inf_le_right)
      ((hTle.trans inf_le_left).trans ((Z_le_VBall Rg _ 2).trans
        ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)))
    have hTB : T ≤ centralizer (B₀ : Set (FreeAmalgam Rg)) :=
      (hTF.trans_eq he).trans (hFB.symm.le.trans inf_le_right)
    exact hT'ne (hcross'.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hTB)))
  let := finite_Z Rg z
  have hidx : I.relIndex Z₀ = 4 := intersection_index_four Z₀ F F'
    inf_le_left inf_le_left
    (by rw [show F = Z₀ ⊓ Q Rg a from rfl,inf_relIndex_left]
        exact (small_critical_indices h e hz hk p hp).2)
    (by rw [show F' = Z₀ ⊓ Q Rg b from rfl,inf_relIndex_left]
        exact (small_critical_indices h e hz hk q hq).2) hne
  let := finite_Z Rg z
  let : Finite I := Finite.of_injective (inclusion hIZ) (inclusion_injective _)
  let : Finite P := Finite.of_injective (inclusion hPZ) (inclusion_injective _)
  let : Finite (I ⊔ P : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion (sup_le hIZ hPZ)) (inclusion_injective _)
  have hPI : P ≤ normalizer (I : Set (FreeAmalgam Rg)) :=
    ((hPZ.trans (le_centralizer (H := Z₀))).trans (centralizer_le hIZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hIP : I ≤ normalizer (P : Set (FreeAmalgam Rg)) :=
    ((hIZ.trans (le_centralizer (H := Z₀))).trans (centralizer_le hPZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hsplit : I ⊔ P = Z₀ := by
    apply eq_of_le_of_card_ge (sup_le hIZ hPZ)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint I P hPI (disjoint_iff.mpr hdis),hPcard]
    have hh := relIndex_mul_card_of_le hIZ
    rw [hidx] at hh
    omega
  have hID : I ≤ centralizer (D₀ : Set (FreeAmalgam Rg)) :=
    hIC.trans (centralizer_le (commutator_le_sup (H₁ := A) (H₂ := B₀)))
  have hfixed : Z₀ ⊓ centralizer (D₀ : Set (FreeAmalgam Rg)) = I := by
    rw [←hsplit,inf_centralizer_sup_of_centralizing I P D₀ hIP hID,
      hderived.2,sup_bot_eq]
  have hmove : ⁅Z₀,D₀⁆ = P := by
    rw [←hsplit,sup_comm I P,commutator_sup_of_central_attachment P I D₀ hIP hID]
    exact hderived.1
  exact ⟨hPcard,hsplit,hdis,hfixed,hmove⟩


include h in
private theorem endpoint_seed_normalizes_radius
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    Z Rg z ≤ normalizer
      ((V Rg a ⊓ Q Rg (p.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  have hG : Z Rg z ≤ stabilizer Rg a ⊓ stabilizer Rg z := le_inf
    (critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical) (Z_le_stabilizer Rg z)
  have hc := hG.trans (stabilizes_shortest_vertices Rg p.walk p.shortest 2)
  exact (le_inf (hG.trans inf_le_left |>.trans (DistanceEight.V_normalized Rg a))
    (hc.trans (Q_normalized Rg (p.walk.getVert 2)))).trans
      inf_normalizer_le_normalizer_inf

include h e hz hk in
/-- On the original paired paths, the seed commutator fixes precisely the
common full kernel. The radius commutator contains its entire moved plane
and strictly more of the full endpoint seed, giving a subgroup of order at
least eight there. -/
theorem plane_small_four_paired_derived_seed_growth
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let b := act Rg g⁻¹ a
            let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
            let P := ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg b,Z Rg z⁆
            let D₀ := ⁅Z Rg a,Z Rg b⁆
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
            let W := ⁅Y,Y'⁆
            Nat.card P = 4 ∧ I ⊔ P = Z Rg z ∧ I ⊓ P = ⊥ ∧
              Z Rg z ⊓ centralizer (D₀ : Set (FreeAmalgam Rg)) = I ∧
              ⁅Z Rg z,D₀⁆ = P ∧ P < W ⊓ Z Rg z ∧
              8 ≤ Nat.card (W ⊓ Z Rg z : Subgroup (FreeAmalgam Rg)) := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hcross,hcross',_,_,_,_,_,_,_,_,
    hnY,_,_,_,hgeom⟩ :=
    plane_small_four_paired_critical_plane h e hz hk u hR hb4 hsmall
  let b := act Rg g⁻¹ a
  let P := ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg b,Z Rg z⁆
  let D₀ := ⁅Z Rg a,Z Rg b⁆
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
  let W := ⁅Y,Y'⁆
  obtain ⟨hcard,hsplit,hdis,hfixed,hmove⟩ :=
    plane_reciprocal_seed_derived_action h e hz hk p q (hsmall _ _ p)
      (hsmall _ _ q) hcross hcross'
  change Nat.card P = 4 at hcard
  change ¬ Y ≤ normalizer (P : Set (FreeAmalgam Rg)) at hnY
  have hpR := four_radius_at_endpoint h hb4 p
  have hqR := four_radius_at_endpoint h hb4 q
  have hDW : D₀ ≤ W := commutator_mono hpR.2 hqR.2
  have hZN : Z Rg z ≤ normalizer (W : Set (FreeAmalgam Rg)) :=
    normalizes_commutator _ _ _ (endpoint_seed_normalizes_radius h p)
      (endpoint_seed_normalizes_radius h q)
  have hPW : P ≤ W := hmove.symm.le.trans
    ((commutator_mono le_rfl hDW).trans
      (le_normalizer_iff_commutator_le_right.mp hZN))
  have hPZ : P ≤ Z Rg z :=
    sup_le ((critical_commutator_le_seed h p).trans inf_le_right)
      ((critical_commutator_le_seed h q).trans inf_le_right)
  have hYN : Y ≤ normalizer
      ((W ⊓ Z Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
    (le_inf (normalizer_commutator_ge_left Y Y') (hpR.1.trans (Z_normalized Rg z))).trans
      inf_normalizer_le_normalizer_inf
  have hstrict : P < W ⊓ Z Rg z := lt_of_le_of_ne (le_inf hPW hPZ)
    (by
      intro he
      apply hnY
      rw [he]
      exact hYN)
  let := finite_Z Rg z
  let : Finite P := Finite.of_injective (inclusion hPZ) (inclusion_injective _)
  let : Finite (W ⊓ Z Rg z : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
  have hd := card_dvd_of_le hstrict.le
  have hlo : 4 < Nat.card (W ⊓ Z Rg z : Subgroup (FreeAmalgam Rg)) := by
    by_contra! hh
    exact hstrict.ne (eq_of_le_of_card_ge hstrict.le (by omega))
  rw [hcard] at hd
  have hbound : 8 ≤ Nat.card (W ⊓ Z Rg z : Subgroup (FreeAmalgam Rg)) := by omega
  exact ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hsplit,hdis,hfixed,hmove,
    hstrict,hbound⟩

omit hk in
include h e hz in
/-- Whole-core application of the paired derived-seed action and growth,
retaining the original projection and both moving covers. -/
theorem coreExhaustion_or_cubic_paired_derived_seed_growth :
    CoreExhaustion L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let b := act Rg g⁻¹ a
            let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
            let P := ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg b,Z Rg z⁆
            let D₀ := ⁅Z Rg a,Z Rg b⁆
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
            let W := ⁅Y,Y'⁆
            Nat.card P = 4 ∧ I ⊔ P = Z Rg z ∧ I ⊓ P = ⊥ ∧
              Z Rg z ⊓ centralizer (D₀ : Set (FreeAmalgam Rg)) = I ∧
              ⁅Z Rg z,D₀⁆ = P ∧ P < W ⊓ Z Rg z ∧
              8 ≤ Nat.card (W ⊓ Z Rg z : Subgroup (FreeAmalgam Rg)))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_paired_derived_seed_growth h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the original odd-index radical, odd
extension kernel quotient, full fixed subgroup and both moving covers. -/
theorem rankTwo_or_cubic_paired_derived_seed_growth :
    RankTwoAlternatives L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let b := act Rg g⁻¹ a
            let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
            let P := ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Z Rg b,Z Rg z⁆
            let D₀ := ⁅Z Rg a,Z Rg b⁆
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
            let W := ⁅Y,Y'⁆
            Nat.card P = 4 ∧ I ⊔ P = Z Rg z ∧ I ⊓ P = ⊥ ∧
              Z Rg z ⊓ centralizer (D₀ : Set (FreeAmalgam Rg)) = I ∧
              ⁅Z Rg z,D₀⁆ = P ∧ P < W ⊓ Z Rg z ∧
              8 ≤ Nat.card (W ⊓ Z Rg z : Subgroup (FreeAmalgam Rg)))) :=
  (coreExhaustion_or_cubic_paired_derived_seed_growth h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
