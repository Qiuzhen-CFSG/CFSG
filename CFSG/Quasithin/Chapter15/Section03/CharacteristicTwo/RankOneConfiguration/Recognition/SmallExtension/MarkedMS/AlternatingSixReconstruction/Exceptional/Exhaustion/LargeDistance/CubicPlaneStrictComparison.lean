module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneStrictPaths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels

/-!
# Strict rotations: full-kernel intersections and separated critical lines

Keep the original cubic critical path a--c--z and its full reverse kernel
F = Z_z intersect Q_a. A midpoint-residual displacer produces the literal
conjugate F' at z'. If [F,F'] is nontrivial, the checked four-edge rotation
is critical and [F,F'] is its full critical commutator of order two.

The original and rotated critical kernels in Z_z are distinct. Both have
index two, so their intersection has index four. The last-edge seed lies
in both and already has that index; hence F intersect Q_z' is exactly the
last-edge seed. All statements concern the full seeds, with their central
attachments retained.

The rotated critical line is disjoint from the original critical line
joined with the center of G_z. Otherwise the full-cover aligned-actor
lemma makes Z_z' fix the original moving kernel. The full-kernel/moving-
kernel commutator identity would then give [F,F'] = 1. For an escaping
radius, its retained order-two line has the original critical line's image
modulo this same center. Thus the rotated line is also disjoint from that
radius line joined with the center; in particular those two lines differ.

The applications use both original displaced paths and retain their
opposite-edge conjugator, exact cross-distances, generating condition and
larger endpoint commutator. Whole-core and literal C.1.32 applications keep
the original radical, projection kernel E, nontrivial odd E/Q and both
covers of orders sixteen and thirty-two. The internal imports reuse the
checked aligned-actor and index-intersection lemmas without altering their
existing visibility.

This separates the nonabelian rotation line from the retained radius line;
it does not exclude either the elementary or nonabelian rotation branch.
The original paired comparison, terminal contradiction, remaining cases
and both core exhaustions are still required.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii) and the comparisons toward (5.12)(1),(3), printed
pp.866--867,924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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

include h e hz hk in
/-- A nonabelian strict rotation cuts the original full kernel exactly in
the last-edge seed. Its critical line is disjoint from the original critical
line even after adjoining the endpoint center. -/
theorem plane_strict_kernel_rotation_separation
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (k : FreeAmalgam Rg) (hkm : k ∈ Ltilde Rg (p.walk.getVert 2))
    (hmove : ¬ (Z Rg z ⊓ Q Rg a).map (MulAut.conj k).toMonoidHom ≤
      (Z Rg z ⊓ Q Rg a) ⊔ Z Rg (p.walk.getVert 2))
    (hne : ⁅Z Rg z ⊓ Q Rg a,
      Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a)⁆ ≠ ⊥) :
    let F := Z Rg z ⊓ Q Rg a
    let z' := act Rg k⁻¹ z
    let F' := Z Rg z' ⊓ Q Rg (act Rg k⁻¹ a)
    let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    F ⊓ Q Rg z' = Z Rg (p.walk.getVert 3) ∧
      (F ⊓ Q Rg z').relIndex (Z Rg z) = 4 ∧
      F ≠ Z Rg z ⊓ Q Rg z' ∧
      ⁅F,F'⁆ ⊓ (⁅Z Rg a,Z Rg z⁆ ⊔ C) = ⊥ := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let z' := act Rg k⁻¹ z
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z' ⊓ Q Rg (act Rg k⁻¹ a)
  let T := ⁅Z Rg a,Z Rg z⁆
  let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  let J := ⁅F,F'⁆
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg c t :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hAt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    change 3 < sourceDistance h
    omega
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
        z p.end_color p.critical⟩
  have hfixed : F = Z Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e pr).symm
  have htF : Z Rg t ≤ F := by
    rw [hfixed]
    refine le_inf (adjacent_Z_le Rg p.end_color hzt) ?_
    intro x hx y hy
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hAt hy)
  have hfix : act Rg k⁻¹ c = c := Ltilde_le_stabilizer c ((Ltilde Rg c).inv_mem hkm)
  have hzc : (cosetGraph Rg).dist z c = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_end,hl]
  have hz'c : (cosetGraph Rg).dist z' c = 2 := by
    rw [show z' = act Rg k⁻¹ z from rfl,←hfix,dist_act]
    exact hzc
  have hz' : color Rg z' = false := by rw [action_preserves_color,p.end_color]
  have hZ'Q : Z Rg z' ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hz')
    rw [(sourceGeometry h).distance_constant _ hz',hz'c]
    exact hb
  have hZQ' : Z Rg c ≤ Q Rg z' := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hc)
    rw [(sourceGeometry h).distance_constant _ hc,SimpleGraph.dist_comm,hz'c]
    exact hb
  have hd := plane_strict_kernel_displacer_commutator h e hz hk u hR hb4 hsmall p k hkm hmove
  obtain ⟨r,hr1,hr2,hr3,he,hcard⟩ := hd.2.2.resolve_left (by
    intro hel
    let := hel
    apply hne
    rw [←hd.1]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  have hneq : F ≠ Z Rg z ⊓ Q Rg z' := by
    intro hh
    apply hne
    apply le_bot_iff.mp
    have hFQ : F ≤ Q Rg z' := hh ▸ inf_le_right
    exact (commutator_mono hFQ inf_le_left).trans_eq
      ((commutator_comm (Q Rg z') (Z Rg z')).trans (Z_centralizes_Q Rg z' hz'))
  let := finite_Z Rg z
  have hidx : (F ⊓ (Z Rg z ⊓ Q Rg z')).relIndex (Z Rg z) = 4 :=
    intersection_index_four (Z Rg z) F (Z Rg z ⊓ Q Rg z') inf_le_left inf_le_left
      (by rw [inf_relIndex_left]; exact (small_critical_indices h e hz hk p (hsmall _ _ p)).2)
      (by rw [inf_relIndex_left]; exact (small_critical_indices h e hz hk r (hsmall _ _ r)).1) hneq
  have hmeet : F ⊓ (Z Rg z ⊓ Q Rg z') = F ⊓ Q Rg z' := by
    rw [←inf_assoc,inf_eq_left.mpr (show F ≤ Z Rg z from inf_le_left)]
  rw [hmeet] at hidx
  have htI : Z Rg t ≤ F ⊓ Q Rg z' :=
    le_inf htF ((adjacent_Z_le Rg hc hct).trans hZQ')
  have hprod := relIndex_mul_relIndex (Z Rg t) (F ⊓ Q Rg z') (Z Rg z)
    htI (inf_le_left.trans inf_le_left)
  rw [hidx,(plane_edge_full_seed_fixer h e hz hk u hR p.end_color hzt).2.1] at hprod
  have hI : F ⊓ Q Rg z' = Z Rg t :=
    le_antisymm (relIndex_eq_one.mp (by omega)) htI
  have hF'c : F' ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using (inf_le_left.trans hZ'Q : F' ≤ Q Rg c)
  have hstrip : ⁅U Rg z ⊓ Q Rg a,F'⁆ = J :=
    ((critical_kernel_predecessor_moving h e hz hb p).2.2 F' hF'c).symm
  have hJG : Z Rg z' ≤ stabilizer Rg z :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) z r.start_color
      (by rw [(sourceGeometry h).distance_constant _ r.start_color]; exact sourceDistance_pos h)
      r.critical
  have hnon : ¬ J ≤ T ⊔ C := by
    intro halign
    have hmoveU : ⁅U Rg z,Z Rg z'⁆ ≤ T ⊔ C := by
      rw [small_critical_moving_commutator_eq h e hz hk r (hsmall _ _ r),←he]
      exact halign
    have hzero := critical_aligned_actor_fixes_moving_kernel h e hz hk p
      (hsmall _ _ p) (Z Rg z') hJG hmoveU
    apply hne
    change J = ⊥
    rw [←hstrip]
    exact le_bot_iff.mp ((commutator_mono le_rfl inf_le_left).trans_eq hzero)
  let : Finite J := Nat.finite_of_card_ne_zero (by change Nat.card J = 2 at hcard; omega)
  let : Finite (J ⊓ (T ⊔ C) : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  refine ⟨hI,hidx,hneq,?_⟩
  by_contra hn
  have hlo := (one_lt_card_iff_ne_bot (J ⊓ (T ⊔ C))).mpr hn
  have heq := eq_of_le_of_card_ge (show J ⊓ (T ⊔ C) ≤ J from inf_le_left)
    (by change Nat.card J = 2 at hcard; omega)
  exact hnon (heq ▸ inf_le_right)

include h e hz hk in
/-- At an escaping radius, a strict rotation either has elementary join or
has a new derived line separated from the original radius line modulo the
literal endpoint center. The full-kernel intersection is exact. -/
theorem plane_strict_kernel_rotation_radius_separation
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (k : FreeAmalgam Rg) (hkm : k ∈ Ltilde Rg (p.walk.getVert 2))
    (hmove : ¬ (Z Rg z ⊓ Q Rg a).map (MulAut.conj k).toMonoidHom ≤
      (Z Rg z ⊓ Q Rg a) ⊔ Z Rg (p.walk.getVert 2)) :
    let c := p.walk.getVert 2
    let F := Z Rg z ⊓ Q Rg a
    let z' := act Rg k⁻¹ z
    let F' := Z Rg z' ⊓ Q Rg (act Rg k⁻¹ a)
    let W := (F ⊔ Z Rg c) ⊔ (F' ⊔ Z Rg c)
    let H := ⁅V Rg a ⊓ Q Rg c,F⁆
    let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    ⁅W,W⁆ = ⁅F,F'⁆ ∧
      (IsElementaryAbelian 2 W ∨
        (Nat.card (⁅F,F'⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          F ⊓ Q Rg z' = Z Rg (p.walk.getVert 3) ∧
          (F ⊓ Q Rg z').relIndex (Z Rg z) = 4 ∧
          ⁅F,F'⁆ ⊓ (H ⊔ C) = ⊥ ∧ ⁅F,F'⁆ ≠ H)) := by
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
  have hYt : V Rg a ⊓ Q Rg (p.walk.getVert 2) ≤
      Q Rg (p.walk.getVert (p.walk.length-1)) := by
    rw [hl]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hAY : Z Rg a ≤ V Rg a ⊓ Q Rg (p.walk.getVert 2) := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact distance_gt_two h e hz hk
  have halign := (plane_radius_kernel_alignment h e hz hk u hR p (hsmall _ _ p)
    (V Rg a ⊓ Q Rg (p.walk.getVert 2)) inf_le_left hYt hAY hescape).2.2.2.2.2
  have hd := plane_strict_kernel_displacer_commutator h e hz hk u hR hb4 hsmall p k hkm hmove
  refine ⟨hd.1,?_⟩
  rcases hd.2.2 with hel | ⟨r,_,_,_,he,hcard⟩
  · exact Or.inl hel
  · have hne : ⁅Z Rg z ⊓ Q Rg a,
        Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a)⁆ ≠ ⊥ := by
      intro hz
      rw [hz,card_bot] at hcard
      omega
    obtain ⟨hI,hi,_,hdis⟩ :=
      plane_strict_kernel_rotation_separation h e hz hk u hR hb4 hsmall p k hkm hmove hne
    rw [←halign] at hdis
    refine Or.inr ⟨hcard,hI,hi,hdis,?_⟩
    intro heq
    apply hne
    rw [heq,inf_eq_left.mpr le_sup_left] at hdis
    exact heq.trans hdis


include h e hz hk in
/-- Both retained displaced paths satisfy the literal kernel intersections
and the separation of rotation lines from their original radius lines. -/
theorem plane_small_four_separated_kernel_rotations
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
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let separated := fun b (r : CriticalPath Rg (sourceGeometry h) b z) =>
              ∀ k ∈ Ltilde Rg (r.walk.getVert 2),
                ¬ (Z Rg z ⊓ Q Rg b).map (MulAut.conj k).toMonoidHom ≤
                  (Z Rg z ⊓ Q Rg b) ⊔ Z Rg (r.walk.getVert 2) →
                let F₀ := Z Rg z ⊓ Q Rg b
                let F₁ := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ b)
                let W := (F₀ ⊔ Z Rg (r.walk.getVert 2)) ⊔
                  (F₁ ⊔ Z Rg (r.walk.getVert 2))
                let H₀ := ⁅V Rg b ⊓ Q Rg (r.walk.getVert 2),F₀⁆
                let Z₀ := stabilizer Rg z ⊓
                  centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
                ⁅W,W⁆ = ⁅F₀,F₁⁆ ∧
                  (IsElementaryAbelian 2 W ∨
                    (Nat.card (⁅F₀,F₁⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
                      F₀ ⊓ Q Rg (act Rg k⁻¹ z) = Z Rg (r.walk.getVert 3) ∧
                      (F₀ ⊓ Q Rg (act Rg k⁻¹ z)).relIndex (Z Rg z) = 4 ∧
                      ⁅F₀,F₁⁆ ⊓ (H₀ ⊔ Z₀) = ⊥ ∧ ⁅F₀,F₁⁆ ≠ H₀))
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              separated a p ∧ separated (act Rg g⁻¹ a) q := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    _,_,_,hopp,_,_,_,hcard,hstrict,hbig,hescape,_,_⟩ :=
    plane_small_four_full_kernel_comparison h e hz hk u hR hb4 hsmall
  have hZz : (Z Rg z).map (MulAut.conj g).toMonoidHom = Z Rg z := by
    simpa only [inv_inv,hfix] using (Z_act Rg g⁻¹ z).symm
  have hescape' : ¬ ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),Z Rg z⁆ ≤
      Z Rg (act Rg g⁻¹ a) := by
    intro hh
    apply hescape
    apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp
    rw [map_commutator,hZz,
      Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    simpa only [hverts 2,V_act,Q_act,Z_act,inv_inv] using hh
  exact ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,
    fun k hkm hmove => plane_strict_kernel_rotation_radius_separation h e hz hk u hR
      hb4 hsmall p hescape k hkm hmove,
    fun k hkm hmove => plane_strict_kernel_rotation_radius_separation h e hz hk u hR
      hb4 hsmall q hescape' k hkm hmove⟩

omit hk in
include h e hz in
/-- Whole-core application preserving the actual cubic projection and both
covers, with separated rotation lines on both original displaced paths. -/
theorem coreExhaustion_or_cubic_separated_kernel_rotations :
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
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let separated := fun b (r : CriticalPath Rg (sourceGeometry h) b z) =>
              ∀ k ∈ Ltilde Rg (r.walk.getVert 2),
                ¬ (Z Rg z ⊓ Q Rg b).map (MulAut.conj k).toMonoidHom ≤
                  (Z Rg z ⊓ Q Rg b) ⊔ Z Rg (r.walk.getVert 2) →
                let F₀ := Z Rg z ⊓ Q Rg b
                let F₁ := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ b)
                let W := (F₀ ⊔ Z Rg (r.walk.getVert 2)) ⊔
                  (F₁ ⊔ Z Rg (r.walk.getVert 2))
                let H₀ := ⁅V Rg b ⊓ Q Rg (r.walk.getVert 2),F₀⁆
                let Z₀ := stabilizer Rg z ⊓
                  centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
                ⁅W,W⁆ = ⁅F₀,F₁⁆ ∧
                  (IsElementaryAbelian 2 W ∨
                    (Nat.card (⁅F₀,F₁⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
                      F₀ ⊓ Q Rg (act Rg k⁻¹ z) = Z Rg (r.walk.getVert 3) ∧
                      (F₀ ⊓ Q Rg (act Rg k⁻¹ z)).relIndex (Z Rg z) = 4 ∧
                      ⁅F₀,F₁⁆ ⊓ (H₀ ⊔ Z₀) = ⊥ ∧ ⁅F₀,F₁⁆ ≠ H₀))
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              separated a p ∧ separated (act Rg g⁻¹ a) q)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_separated_kernel_rotations h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, retaining the original radical, the odd
extension-kernel quotient and the complete central attachments. -/
theorem rankTwo_or_cubic_separated_kernel_rotations :
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
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let separated := fun b (r : CriticalPath Rg (sourceGeometry h) b z) =>
              ∀ k ∈ Ltilde Rg (r.walk.getVert 2),
                ¬ (Z Rg z ⊓ Q Rg b).map (MulAut.conj k).toMonoidHom ≤
                  (Z Rg z ⊓ Q Rg b) ⊔ Z Rg (r.walk.getVert 2) →
                let F₀ := Z Rg z ⊓ Q Rg b
                let F₁ := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ b)
                let W := (F₀ ⊔ Z Rg (r.walk.getVert 2)) ⊔
                  (F₁ ⊔ Z Rg (r.walk.getVert 2))
                let H₀ := ⁅V Rg b ⊓ Q Rg (r.walk.getVert 2),F₀⁆
                let Z₀ := stabilizer Rg z ⊓
                  centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
                ⁅W,W⁆ = ⁅F₀,F₁⁆ ∧
                  (IsElementaryAbelian 2 W ∨
                    (Nat.card (⁅F₀,F₁⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
                      F₀ ⊓ Q Rg (act Rg k⁻¹ z) = Z Rg (r.walk.getVert 3) ∧
                      (F₀ ⊓ Q Rg (act Rg k⁻¹ z)).relIndex (Z Rg z) = 4 ∧
                      ⁅F₀,F₁⁆ ⊓ (H₀ ⊔ Z₀) = ⊥ ∧ ⁅F₀,F₁⁆ ≠ H₀))
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              separated a p ∧ separated (act Rg g⁻¹ a) q)) :=
  (coreExhaustion_or_cubic_separated_kernel_rotations h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
