module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.CentralIntersections
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels


/-!
# Stabilizer centrality on compatible distance-four Borel paths

Keep the original three paths d--a--c, a--c--z and c--z--y, with the
source generation identities and the backward transporter. In the failure
branch of MS93 (5.12)(1), distinct movers on a--c put the critical line in
that edge seed. The future endpoint y centralizes the line, so generation
makes it central in the whole stabilizer of c. Its full central attachment
then places the failure line in the right edge seed without a distinctness
assumption on the right movers.

For a small critical image on d--c and distinct backward movers, the failure
line cannot be central at c. Otherwise it lies in the a--c edge seed and
hence Z_a. The distinct-mover intersection puts it in the d--a edge seed;
generation makes it central at a. The actual backward transporter fixes
the line and carries centrality at c to centrality at d, contradicting the
reciprocal full-kernel calculation.

Combining the two comparisons shows that a compatible distinct-mover
failure has a nontrivial central attachment at z, acting nontrivially at c.
The actual natural quotient has kernel exactly this attachment, so the
order-sixteen cover cannot fail normalization. The remaining failure has
the full order-thirty-two cover. OriginalSylowExceptional applies the
results to the literal c.L,d.S graph, with both small-image conditions,
both generation identities and the same transporter explicit.

The compatible selections, equal-mover and large-image cases, and the
surviving order-thirty-two attachment argument still require completion.
These results do not assert the full (5.12) contradiction, CoreExhaustion
or exceptional block reconstruction. The projection kernel remains E,
including its odd quotient E/Q; no replacement graph is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(1), printed pp.924--925; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
open CFSG.Quasithin.ChapterB.Offenders.Six
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h in
private theorem seed_center_le_incident_edge
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    Z Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ≤ Z Rg t := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hZX := (sourceGeometry h).omega_bound a ha (by
    rw [(sourceGeometry h).distance_constant a ha]
    exact sourceDistance_pos h)
  intro x hx
  have hxX := mem_omegaCenter_iff.mp (hZX hx.1)
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr ⟨(Q_le_adjacent_h Rg ht hat) hxX.1,
    hxX.2.1,fun y hy => hx.2 y (hy.2 _ (adjacent_symm Rg hat))⟩

include h e hz hk in
/-- On the same three overlapping distance-four paths, the distinct left
movers make the critical line central in the whole middle stabilizer.
The future critical path supplies the missing generator. Consequently the
failure line lies in the right edge seed even when its two movers agree. -/
theorem borel_four_failure_middle_central
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1)) :
    ⁅Z Rg a,Z Rg z⁆ ≤ centralizer
        (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) ∧
      ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆ ≤
        Z Rg (p.walk.getVert 3) := by
  let c := p.walk.getVert 2
  let H := ⁅Z Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆
  let D := ⁅Z Rg a,Z Rg z⁆
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hrl : r.walk.length = 4 := r.length_eq_b.trans hb
  have hc : color Rg c = false := r.start_color
  have ht : color Rg (p.walk.getVert 1) = true := by
    have hh := p.vertex_color (by omega : 1 ≤ p.walk.length)
    cases he : color Rg (p.walk.getVert 1) <;> simp_all
  have hDz : D ≤ Z Rg z := by
    dsimp only [D]
    rw [commutator_comm]
    exact critical_seed_commutator_le h (CriticalPath.ofPair p.end_color (reverse_pair h e p))
  have hyQ : Z Rg y ≤ Q Rg z := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ r.end_color)
    have hd : (cosetGraph Rg).dist z y = 2 := by
      simpa only [hrz,hrl,Nat.reduceSub] using r.dist_end 2
    rw [SimpleGraph.dist_comm,hd,(sourceGeometry h).distance_constant _ r.end_color]
    exact distance_gt_two h e hz hk
  have hDy : D ≤ centralizer (Z Rg y : Set (FreeAmalgam Rg)) :=
    hDz.trans ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z p.end_color)).trans
      (centralizer_le hyQ))
  have hDt := (borel_four_failure_edge_lines h e hz hk u hR p q hqa hp hnorm).1 hne
  have hDc : D ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp (hDt.trans (terminal_edge_seed_central ht)))
      (le_centralizer_iff.mp hDy)
  refine ⟨hDc,?_⟩
  have hcontrol := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  have hxz := (hcontrol.2 hnorm z p.end_color).2
  have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp
    (fun hh => hnorm (hcontrol.1.mpr hh))
  have hct : Adjacent Rg c (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := (cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 3) (by omega))
    change Adjacent Rg (p.walk.getVert 3) (p.walk.getVert 4) at hh
    rw [←hl,SimpleGraph.Walk.getVert_length] at hh
    exact adjacent_symm Rg hh
  have hDseed : D ≤ Z Rg c := hDt.trans (adjacent_Z_le Rg hc (by
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))))
  have hDright : D ≤ Z Rg (p.walk.getVert 3) :=
    (le_inf hDseed hDc).trans (seed_center_le_incident_edge h hc hct)
  rw [hxz]
  exact hline.2.2.1.trans (sup_le hDright
    ((inf_le_inf_right _ (DistanceEight.U_le_Z Rg z)).trans
      (seed_center_le_incident_edge h p.end_color hzt)))

include h e hz hk in
/-- On a generating backward overlap with a small critical image and distinct
backward movers, the failure line is not central at the midpoint. Centrality
would transport through the actual backward conjugator to its other endpoint,
contradicting the full-cover reciprocal kernel calculation. -/
theorem borel_four_failure_not_central_middle
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (hne : edgeOffenderJoin a (q.walk.getVert 1) ≠
      edgeOffenderJoin d (q.walk.getVert 1)) :
    ¬ ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆ ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let H := ⁅Z Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆
  intro hHc
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hc : color Rg c = false := q.end_color
  have hcb : Adjacent Rg c (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hdt : Adjacent Rg d (q.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a (q.walk.getVert 1) := by
    have hh := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
    simpa only [hqa] using hh
  have ht : color Rg (q.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hdt
    rw [q.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hplace := borel_four_kernel_failure_midpoint h e hz hk u hR p q hqa hp hnorm
  have hHZc : H ≤ Z Rg c := hplace.trans inf_le_left |>.trans inf_le_right
  have hHZa : H ≤ Z Rg a := ((le_inf hHZc hHc).trans
    (seed_center_le_incident_edge h hc hcb)).trans (adjacent_Z_le Rg p.start_color hab)
  have hHt : H ≤ Z Rg (q.walk.getVert 1) := by
    rw [←borel_four_failure_seed_intersections h e hz hk u hR p q hqa hp hnorm
      p.start_color q.start_color hat hdt hne]
    exact le_inf hHZa (hplace.trans inf_le_left |>.trans inf_le_left)
  have hHZz : H ≤ Z Rg z := hplace.trans inf_le_right
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hHz : H ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    hHZz.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hHa : H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp (hHt.trans (terminal_edge_seed_central ht)))
      (le_centralizer_iff.mp hHz)
  have hHd : H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hHc).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [terminal_fixed_map H (stabilizer Rg a) hHa ((stabilizer Rg a).inv_mem hx)] at hh
    change H ≤ centralizer ((stabilizer Rg (p.walk.getVert 2)).map
      (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam Rg)) at hh
    rwa [←stabilizer_act,hxd] at hh
  have hcontrol := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  have hrecip := borel_four_kernel_failure_reciprocal h e hz hk u hR p q hqa hp hq
    (fun hh => hnorm (hcontrol.1.mpr hh))
  have hxz := (hcontrol.2 hnorm z p.end_color).2
  apply hrecip.1
  simpa only [H,hxz] using hHd

include h e hz hk in
/-- In the distinct-mover, small-image compatible configuration, failure
forces the full endpoint central attachment to act nontrivially at the middle
vertex. In particular the attachment cannot be dropped from the argument. -/
theorem borel_four_failure_attachment_not_central_middle
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = q.walk.getVert 1)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1)) :
    ¬ U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  intro hC
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hJa := remaining_edge_join_act h e hz hk u (Or.inr hR) p.start_color hab x
  have hJc := remaining_edge_join_act h e hz hk u (Or.inr hR) q.end_color hcb x
  rw [show act Rg x a = a from hx,hxt] at hJa
  rw [hxd,hxt] at hJc
  have hne' : edgeOffenderJoin a (q.walk.getVert 1) ≠
      edgeOffenderJoin d (q.walk.getVert 1) := by
    intro he
    apply hne
    exact (map_injective (MulAut.conj x⁻¹).injective)
      (hJa.symm.trans (he.trans hJc))
  have hcrit := (borel_four_failure_middle_central h e hz hk u hR
    p q hqa r hrz hgen hp hnorm hne).1
  have hcontrol := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp
    (fun hh => hnorm (hcontrol.1.mpr hh))
  apply borel_four_failure_not_central_middle h e hz hk u hR
    p q hqa hgen' x hx hxd hp hq hnorm hne'
  rw [(hcontrol.2 hnorm z p.end_color).2]
  exact hline.2.2.1.trans (sup_le hcrit hC)
include h e hz hk in
private theorem moving_attachment_eq_bot_or_card_thirty_two
    {a : Vertex Rg} (ha : color Rg a = false) :
    U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥ ∨
      Nat.card (U Rg a) = 32 := by
  rcases graph_U_card h e hz hk a ha with hc | hc
  · left
    obtain ⟨_,_,_,_,_,_,p,hp,hker,_⟩ := graph_cover h e hz hk a ha
    let := finite_Z Rg a
    let : Finite (U Rg a) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg a)) (inclusion_injective _)
    have hcard : Nat.card (Multiplicative (natural (Fin 6))) = 16 := by
      change Nat.card (natural (Fin 6)) = 16
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
        BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
      norm_num
    have hi := ((Nat.bijective_iff_surjective_and_card p).mpr
      ⟨hp,hc.trans hcard.symm⟩).1
    apply le_bot_iff.mp
    rintro x ⟨hx,hxc⟩
    have he : (⟨x,hx⟩ : U Rg a) ∈ p.ker := by rw [hker]; exact hxc
    have heq : (⟨x,hx⟩ : U Rg a) = 1 := hi (he.trans (map_one p).symm)
    exact congrArg Subtype.val heq
  · exact Or.inr hc

include h e hz hk in
/-- The compatible distinct-mover failure requires the full order-thirty-two
cover. The order-sixteen branch is excluded by its zero central attachment;
no attachment is removed in the surviving case. -/
theorem borel_four_failure_cover_thirty_two
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = q.walk.getVert 1)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1)) :
    Nat.card (U Rg z) = 32 := by
  have hn := borel_four_failure_attachment_not_central_middle h e hz hk u hR
    p q hqa r hrz hgen hgen' x hx hxd hxt hp hq hnorm hne
  exact (moving_attachment_eq_bot_or_card_thirty_two h e hz hk p.end_color).resolve_left
    (fun he => hn (he ▸ bot_le))

include h e hz hk in
/-- On the full sixteen-element moving cover, compatible distinct movers
and two small critical images give the full-omega normalization required
in MS93 (5.12)(1). Every source path and transporter is retained. -/
theorem borel_four_sixteen_kernel_normalized
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = q.walk.getVert 1)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hcard : Nat.card (U Rg z) = 16)
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1)) :
    X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _) := by
  by_contra hn
  have hh := borel_four_failure_cover_thirty_two h e hz hk u hR
    p q hqa r hrz hgen hgen' x hx hxd hxt hp hq hn hne
  omega

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
