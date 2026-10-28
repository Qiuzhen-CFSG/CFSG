module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCommonKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusGeometry

/-!
# Cross-commutator escape from the common full kernel

Retain the paired paths a--v--c--t--z and b--v'--c'--t'--z selected in
`CubicPlaneCommonKernel`. Write F = Z_z intersect Q_a, F' = Z_z intersect
Q_b and I = F intersect F'. Their distinct index-two full kernels span
Z_z. The critical line [Z_b,Z_z] lies in F' and is disjoint from I.
Consequently Z_b cannot normalize F: since F' centralizes Z_b, such
normalization would put the same nonzero critical line in I.

Let Y = V_a intersect Q_c. The accepted radius displacement gives
F = I join I^y for an actual y in Y. If [Z_b,Y] normalized I, then Z_b
would normalize I^y as well as I, hence F, contradicting the preceding
comparison. The same argument on the opposite retained path proves that
[Z_a,Y'] does not normalize I. Thus [Y,Y'] does not normalize I either.

The common kernel fixes both ends of each path, hence every vertex of each
path. It therefore normalizes Y and Y', and so normalizes W = [Y,Y'].
This gives [W,I] inside W intersect Z_z, but not inside Q_a intersect Q_b.
The result keeps the literal full kernels and central attachments. It
excludes normalization by these cross-commutators; it does not assert a
contradiction from their mere existence. The terminal geometric exclusion,
other image/distance/Borel branches, both core exhaustions and unconditional
reconstruction remain required.

The whole-core and literal C.1.32 applications retain the selected paths,
exact cross-distances, original generating edge and conjugator, original
proper odd-index radical, cubic projection with kernel E and odd nontrivial
E/Q, and both moving covers of orders sixteen and thirty-two. Internal
imports reuse the existing conjugation and tree-path calculations without
changing public boundaries.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), paired commutator comparisons toward (5.12)(1),(3), printed
pp.924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

private theorem conjugate_normalization_of_cross_commutator {J : Type*} [Group J]
    (A B I : Subgroup J) (hA : A ≤ normalizer (I : Set J))
    (hc : ⁅A,B⁆ ≤ normalizer (I : Set J)) (b : J) (hb : b ∈ B) :
    A ≤ normalizer (I.map (MulAut.conj b).toMonoidHom : Set J) := by
  intro a ha
  apply I.le_normalizer_map (MulAut.conj b).toMonoidHom
  refine ⟨b⁻¹*a*b,?_,?_⟩
  · have hba : ⁅b⁻¹,a⁆ ∈ normalizer (I : Set J) := by
      apply hc
      rw [commutator_comm]
      exact commutator_mem_commutator (B.inv_mem hb) ha
    have he : ⁅b⁻¹,a⁆ * a = b⁻¹*a*b := by group
    rw [←he]
    exact (normalizer (I : Set J)).mul_mem hba (hA ha)
  · change b * (b⁻¹*a*b) * b⁻¹ = a
    group

private theorem cross_commutator_not_normalizes {J : Type*} [Group J]
    (A B I F : Subgroup J) (hA : A ≤ normalizer (I : Set J))
    (hF : ¬ A ≤ normalizer (F : Set J))
    (hb : ∃ b ∈ B, I ⊔ I.map (MulAut.conj b).toMonoidHom = F) :
    ¬ ⁅A,B⁆ ≤ normalizer (I : Set J) := by
  intro hc
  obtain ⟨b,hb,he⟩ := hb
  apply hF
  rw [←he]
  exact (le_inf hA (conjugate_normalization_of_cross_commutator A B I hA hc b hb)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

include h e hz hk in
/-- If two distinct full critical kernels span the endpoint seed, its second
starting seed cannot normalize the first kernel. The opposite critical
line is retained literally, including its disjointness from the common kernel. -/
theorem plane_seed_not_normalizes_opposite_kernel
    {a b z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) b z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (hqsmall : (Q Rg z).relIndex (Z Rg b) < 4)
    (hne : Z Rg z ⊓ Q Rg a ≠ Z Rg z ⊓ Q Rg b)
    (hdis : ⁅Z Rg b,Z Rg z⁆ ⊓ ((Z Rg z ⊓ Q Rg b) ⊓ (Z Rg z ⊓ Q Rg a)) = ⊥) :
    ¬ Z Rg b ≤ normalizer ((Z Rg z ⊓ Q Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z ⊓ Q Rg b
  let T := ⁅Z Rg b,Z Rg z⁆
  let := finite_Z Rg z
  let : Finite F := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite F' := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hFi : F.relIndex (Z Rg z) = 2 := by
    rw [show F = Z Rg z ⊓ Q Rg a from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk p hsmall).2
  have hF'i : F'.relIndex (Z Rg z) = 2 := by
    rw [show F' = Z Rg z ⊓ Q Rg b from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk q hqsmall).2
  have hFnot : ¬ F' ≤ F := by
    intro hh
    have hm := relIndex_mul_relIndex F' F (Z Rg z) hh inf_le_left
    rw [hFi,hF'i] at hm
    have hi : F'.relIndex F = 1 := by omega
    exact hne (le_antisymm (relIndex_eq_one.mp hi) hh)
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hFnot
  have hjoin : F ⊔ F' = Z Rg z := by
    have hs := sup_zpowers_eq_of_relIndex_prime (show F ≤ Z Rg z from inf_le_left)
      Nat.prime_two hFi hx.1 hxn
    exact le_antisymm (sup_le inf_le_left inf_le_left)
      (hs.symm.le.trans (sup_le_sup_left (zpowers_le.mpr hx) _))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hN : F' ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
    ((show F' ≤ Z Rg z from inf_le_left).trans (le_centralizer (H := Z Rg z))).trans
      ((centralizer_le (show F ≤ Z Rg z from inf_le_left)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hC : F' ≤ centralizer (Z Rg b : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg b q.start_color)).trans (centralizer_le inf_le_right))
  have hTZ : T ≤ Z Rg z := le_normalizer_iff_commutator_le_right.mp
    ((Z_le_stabilizer_of_dist_le b _ q.critical.1.le).trans (Z_normalized Rg z))
  have hTb : T ≤ Z Rg b := le_normalizer_iff_commutator_le_left.mp
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) b q.start_color
      (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
      q.critical).trans (Z_normalized Rg b))
  have hTF' : T ≤ F' := le_inf hTZ (hTb.trans ((Z_le_VBall Rg _ 2).trans
    ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) b q.start_color)))
  intro hn
  have hTF : T ≤ F := by
    change ⁅Z Rg b,Z Rg z⁆ ≤ F
    rw [commutator_comm,←hjoin,
      commutator_sup_of_central_attachment F F' (Z Rg b) hN hC]
    exact le_normalizer_iff_commutator_le_left.mp hn
  have he : T = ⊥ := le_bot_iff.mp ((le_inf le_rfl (le_inf hTF' hTF)).trans_eq hdis)
  have hc := small_critical_commutator_card h e hz hk q hqsmall
  change Nat.card T = 2 at hc
  rw [he,card_bot] at hc
  omega

include h in
private theorem full_kernel_normalizes_midpoint_radius
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    Z Rg z ⊓ Q Rg a ≤ normalizer
      ((V Rg a ⊓ Q Rg (p.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  have hG : Z Rg z ⊓ Q Rg a ≤ stabilizer Rg a ⊓ stabilizer Rg z :=
    le_inf (fun _ hx => hx.2.1) (inf_le_left.trans (Z_le_stabilizer Rg z))
  have hc := hG.trans (stabilizes_shortest_vertices Rg p.walk p.shortest 2)
  exact (le_inf (hG.trans inf_le_left |>.trans (DistanceEight.V_normalized Rg a))
    (hc.trans (Q_normalized Rg (p.walk.getVert 2)))).trans
      inf_normalizer_le_normalizer_inf

include h in
private theorem four_radius_at_endpoint
    (hb4 : sourceDistance h = 4) {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z) :
    V Rg a ⊓ Q Rg (p.walk.getVert 2) ≤ stabilizer Rg z ∧
      Z Rg a ≤ V Rg a ⊓ Q Rg (p.walk.getVert 2) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  refine ⟨(inf_le_right.trans (Q_le_adjacent_h Rg ht hct)).trans
    (fun _ hx => hx.2 _ (adjacent_symm Rg hzt)), le_inf (Z_le_VBall Rg _ 2) ?_⟩
  apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
  rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
  change 2 < sourceDistance h
  omega

include h e hz hk in
/-- A radius displacement of the common kernel forces the opposite
seed--radius commutator to move that kernel out of itself. -/
theorem plane_cross_commutator_not_normalizes_common_kernel
    {a b z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) b z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg z).relIndex (Z Rg b) < 4)
    (hne : Z Rg z ⊓ Q Rg a ≠ Z Rg z ⊓ Q Rg b)
    (hdis : ⁅Z Rg b,Z Rg z⁆ ⊓ ((Z Rg z ⊓ Q Rg b) ⊓ (Z Rg z ⊓ Q Rg a)) = ⊥)
    (Y : Subgroup (FreeAmalgam Rg))
    (hmove : ∃ y ∈ Y,
      ((Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)) ⊔
        ((Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)).map (MulAut.conj y).toMonoidHom =
          Z Rg z ⊓ Q Rg a) :
    ¬ ⁅Z Rg b,Y⁆ ≤ normalizer
      (((Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b) : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  apply cross_commutator_not_normalizes (Z Rg b) Y
    ((Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)) (Z Rg z ⊓ Q Rg a)
  · exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg b q.start_color)).trans
      (centralizer_le (inf_le_right.trans inf_le_right))).trans
        (Subgroup.centralizer_le_normalizer _)
  · exact plane_seed_not_normalizes_opposite_kernel h e hz hk p q hp hq hne hdis
  · exact hmove

include h e hz hk in
/-- On the original retained pair, both cross-commutators fail to normalize
the common full kernel. The commutator of the two radii is normalized by
that kernel, but its reverse commutator escapes the intersection of the
original two-cores while remaining in the full endpoint seed. -/
theorem plane_small_four_paired_cross_commutator_escape
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
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
            let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
            let W := ⁅Y,Y'⁆
            I.relIndex (Z Rg z) = 4 ∧
              ¬ ⁅Z Rg b,Y⁆ ≤ normalizer (I : Set (FreeAmalgam Rg)) ∧
              ¬ ⁅Z Rg a,Y'⁆ ≤ normalizer (I : Set (FreeAmalgam Rg)) ∧
              ¬ W ≤ normalizer (I : Set (FreeAmalgam Rg)) ∧
              I ≤ normalizer (W : Set (FreeAmalgam Rg)) ∧
              ⁅W,I⁆ ≤ W ⊓ Z Rg z ∧ ¬ ⁅W,I⁆ ≤ Q Rg a ⊓ Q Rg b := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,_,_,_,_,cp,cq⟩ :=
    plane_small_four_paired_common_kernel_control h e hz hk u hR hb4 hsmall
  let b := act Rg g⁻¹ a
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z ⊓ Q Rg b
  let I := F ⊓ F'
  let W := ⁅Y,Y'⁆
  obtain ⟨⟨_,hdisP,hIF,hIZ,_,_,_,_,_,_,_,_⟩,y,hy,_,hjoin,_⟩ := cp
  obtain ⟨⟨_,hdisQ,_,_,_,_,_,_,_,_,_,_⟩,y',hy',_,hjoin',_⟩ := cq
  have hne : F ≠ F' := by
    intro he
    have hi : I = F := by dsimp only [I]; rw [←he,inf_idem]
    change I.relIndex F = 2 at hIF
    rw [hi,relIndex_self] at hIF
    omega
  have hn : ¬ ⁅Z Rg b,Y⁆ ≤ normalizer (I : Set (FreeAmalgam Rg)) :=
    plane_cross_commutator_not_normalizes_common_kernel h e hz hk p q
      (hsmall _ _ p) (hsmall _ _ q) hne hdisQ Y ⟨y,hy,hjoin⟩
  have hn' : ¬ ⁅Z Rg a,Y'⁆ ≤ normalizer (I : Set (FreeAmalgam Rg)) := by
    have hh := plane_cross_commutator_not_normalizes_common_kernel h e hz hk q p
      (hsmall _ _ q) (hsmall _ _ p) (Ne.symm hne) hdisP Y' ⟨y',hy',hjoin'⟩
    change ¬ ⁅Z Rg a,Y'⁆ ≤ normalizer ((F' ⊓ F : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) at hh
    simpa only [inf_comm F' F] using hh
  have hpR := four_radius_at_endpoint h hb4 p
  have hqR := four_radius_at_endpoint h hb4 q
  have hWN : ¬ W ≤ normalizer (I : Set (FreeAmalgam Rg)) := by
    intro hnW
    apply hn
    exact (commutator_mono hqR.2 le_rfl).trans
      ((commutator_comm Y' Y).le.trans hnW)
  have hIN : I ≤ normalizer (W : Set (FreeAmalgam Rg)) := by
    have hIp : I ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
      inf_le_left.trans (full_kernel_normalizes_midpoint_radius h p)
    have hIq : I ≤ normalizer (Y' : Set (FreeAmalgam Rg)) :=
      inf_le_right.trans (full_kernel_normalizes_midpoint_radius h q)
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hIp hx),
      mem_normalizer_iff_map_conj_eq.mp (hIq hx)]
  have hWG : W ≤ stabilizer Rg z :=
    (commutator_le_sup (H₁ := Y) (H₂ := Y')).trans (sup_le hpR.1 hqR.1)
  have hJZ : ⁅W,I⁆ ≤ Z Rg z :=
    (commutator_mono le_rfl (show I ≤ Z Rg z from inf_le_left.trans inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp (hWG.trans (Z_normalized Rg z)))
  have hnot : ¬ ⁅W,I⁆ ≤ Q Rg a ⊓ Q Rg b := by
    intro hh
    apply hWN
    apply le_normalizer_iff_commutator_le_right.mpr
    exact le_inf (le_inf hJZ (hh.trans inf_le_left)) (le_inf hJZ (hh.trans inf_le_right))
  exact ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hIZ,hn,hn',hWN,hIN,
    le_inf (le_normalizer_iff_commutator_le_left.mp hIN) hJZ,hnot⟩

omit hk in
include h e hz in
/-- Whole-core application of the paired cross-commutator escape, with the
actual cubic projection and both full moving covers. -/
theorem coreExhaustion_or_cubic_paired_cross_commutator_escape :
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
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
            let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
            let W := ⁅Y,Y'⁆
            I.relIndex (Z Rg z) = 4 ∧
              ¬ ⁅Z Rg b,Y⁆ ≤ normalizer (I : Set (FreeAmalgam Rg)) ∧
              ¬ ⁅Z Rg a,Y'⁆ ≤ normalizer (I : Set (FreeAmalgam Rg)) ∧
              ¬ W ≤ normalizer (I : Set (FreeAmalgam Rg)) ∧
              I ≤ normalizer (W : Set (FreeAmalgam Rg)) ∧
              ⁅W,I⁆ ≤ W ⊓ Z Rg z ∧ ¬ ⁅W,I⁆ ≤ Q Rg a ⊓ Q Rg b)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_paired_cross_commutator_escape h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, retaining the original radical, extension
kernel, central attachments and paired cross-commutator escape. -/
theorem rankTwo_or_cubic_paired_cross_commutator_escape :
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
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
            let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
            let W := ⁅Y,Y'⁆
            I.relIndex (Z Rg z) = 4 ∧
              ¬ ⁅Z Rg b,Y⁆ ≤ normalizer (I : Set (FreeAmalgam Rg)) ∧
              ¬ ⁅Z Rg a,Y'⁆ ≤ normalizer (I : Set (FreeAmalgam Rg)) ∧
              ¬ W ≤ normalizer (I : Set (FreeAmalgam Rg)) ∧
              I ≤ normalizer (W : Set (FreeAmalgam Rg)) ∧
              ⁅W,I⁆ ≤ W ⊓ Z Rg z ∧ ¬ ⁅W,I⁆ ≤ Q Rg a ⊓ Q Rg b)) :=
  (coreExhaustion_or_cubic_paired_cross_commutator_escape h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
