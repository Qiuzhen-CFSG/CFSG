module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball

/-!
# The intersection and sharpening in MS93 (4.5.3)

The opposite first-hat layer centralizes the distant critical Z-actor by
radius clearance. Its intersection with Z_a consequently lies in the
intervening edge Z-layer, whose index is two. This proves the printed
intersection bound without assuming either final commutator estimate.

Conjugating the preliminary displacement estimate gives the second-layer
bound into the opposite first-hat layer. Intersecting it with Z_a Z_c
sharpens the estimate to Z_c. The literal reflected product of (4.5.1)(iv)
then supplies the whole Q_c actor. Only the preliminary bounds and the
first identity remain explicit in this local calculation; Path discharges
all geometry and product premises on the supplied source walk.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(ii), printed p.898.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem fixed_eq_edge (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t)
    {P : Subgroup (FreeAmalgam R)} (hP : P ≤ Q R t) (hn : ¬ P ≤ Q R a) :
    Z R a ⊓ centralizer (P : Set (FreeAmalgam R)) = Z R t := by
  have heq := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
    (LocalCommutator.moduleFacts common) a t ha hat
  have hNF : Z R t ≤ Z R a ⊓ centralizer (P : Set (FreeAmalgam R)) :=
    heq ▸ le_inf inf_le_left (inf_le_right.trans (centralizer_le hP))
  have hFU : Z R a ⊓ centralizer (P : Set (FreeAmalgam R)) ≤ Z R a := inf_le_left
  have hne : Z R a ⊓ centralizer (P : Set (FreeAmalgam R)) ≠ Z R a := by
    intro h
    apply hn
    rw [← common.centralizer a t ha hat]
    exact le_inf hP (le_centralizer_iff.mp (h.ge.trans inf_le_right))
  have hm := relIndex_mul_relIndex (Z R t)
    (Z R a ⊓ centralizer (P : Set (FreeAmalgam R))) (Z R a) hNF hFU
  rw [earlier.edge_Z_index a t ha hat] at hm
  have hdiv : (Z R a ⊓ centralizer (P : Set (FreeAmalgam R))).relIndex (Z R a) ∣ 2 :=
    ⟨(Z R t).relIndex (Z R a ⊓ centralizer (P : Set (FreeAmalgam R))), by simpa only [Nat.mul_comm] using hm.symm⟩
  have hi := ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
    (fun h => hne (le_antisymm hFU (relIndex_eq_one.mp h)))
  rw [hi] at hm
  exact le_antisymm (relIndex_eq_one.mp (by omega)) hNF

/-- The printed intersection step. The distant critical actor lies in Q_t,
while the opposite hat layer centralizes it by radius clearance. -/
theorem intersection_le (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c d f t : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : color R d = false) (hf : color R f = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hac : (cosetGraph R).dist a c = 2)
    (hcd : (cosetGraph R).dist c d = 2)
    (hdf : (cosetGraph R).dist d f = 4)
    (hft : Z R f ≤ Q R t) (hfn : ¬ Z R f ≤ Q R a) :
    (Z R a ⊔ Z R c) ⊓ hatV R d c ≤ Z R c := by
  have hZc : Z R c ≤ hatV R d c := Z_le_localZSpan R c d
  have hlocal : Z R a ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha, hac]
    change 2 < geometry.b R
    rw [earlier.distance]
    decide
  have hn : Z R a ≤ normalizer (Z R c : Set (FreeAmalgam R)) :=
    (hlocal.trans (fun _ hx => hx.1)).trans (Z_normalized R c)
  have hprod := coe_mul_of_left_le_normalizer_right (Z R a) (Z R c) hn
  have hcentral : hatV R d c ≤ centralizer (Z R f : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes f hf)).trans
      (centralizer_le ((hatV_le_radius R hcd.le).trans
        (V_le_Q_of_dist_add_two_lt R hd (by rw [hdf, earlier.distance]; decide))))
  intro x hx
  have hxprod : x ∈ (Z R a : Set (FreeAmalgam R)) * (Z R c : Set (FreeAmalgam R)) := by
    rw [← hprod]
    exact hx.1
  obtain ⟨z, hz, w, hw, rfl⟩ := hxprod
  have hzV : z ∈ hatV R d c := by
    have h := (hatV R d c).mul_mem hx.2 ((hatV R d c).inv_mem (hZc hw))
    simpa only [mul_inv_cancel_right] using h
  have hzedge : z ∈ Z R t := by
    rw [← fixed_eq_edge common earlier ha hat hft hfn]
    exact ⟨hz, hcentral hzV⟩
  exact (Z R c).mul_mem (Escape.EdgeTransfer.edge_Z_le c t hc hct hzedge) hw

/-- Conjugating the preliminary bound gives the intermediate second-layer
bound. Both conjugation and normalization use the literal local group. -/
theorem second_le_first {c d a : Vertex R}
    (hd : color R d = false) (hcd : (cosetGraph R).dist c d = 2)
    (hseed : hatV R c a ≤ Q R d)
    (hpre : ⁅hatV R c a, Q R d⁆ ≤ Z R c ⊔ Z R d) :
    ⁅hatW R d c a, Q R d⁆ ≤ hatV R d c := by
  rw [hatW, Escape.PairingControl.commutator_conjugatesIn _ _ _ hseed (Q_normalized R d)]
  apply iSup_le
  intro g
  have hZ : Z R c ⊔ Z R d ≤ hatV R d c :=
    sup_le (Z_le_localZSpan R c d) (Z_le_hatV hd (by rwa [SimpleGraph.dist_comm]))
  exact (map_mono (hpre.trans hZ)).trans
    (mem_normalizer_iff_map_conj_eq.mp
      (hatV_normalized R d c ((stabilizer R d).inv_mem g.property))).le

/-- The sharpening argument of (4.5.3)(ii), with just its two preliminary
bounds explicit. The opposite product is the actual reflected (4.5.1)(iv). -/
theorem sharpen (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c d f t : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : color R d = false) (hf : color R f = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hac : (cosetGraph R).dist a c = 2)
    (hcd : (cosetGraph R).dist c d = 2)
    (had : (cosetGraph R).dist a d = 4)
    (hdf : (cosetGraph R).dist d f = 4)
    (hft : Z R f ≤ Q R t) (hfn : ¬ Z R f ≤ Q R a)
    (hidentity : hatV R a c = Vcirc R a ⊔ Z R a)
    (hproduct : (hatW R d c a : Set (FreeAmalgam R)) * (Q R a : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)))
    (hpre : ⁅hatV R a c, Q R c⁆ ≤ Z R a ⊔ Z R c)
    (hpre' : ⁅hatV R c a, Q R d⁆ ≤ Z R c ⊔ Z R d) :
    ⁅hatV R a c, Q R c⁆ ≤ Z R c := by
  have hca : (cosetGraph R).dist c a = 2 := by rwa [SimpleGraph.dist_comm]
  have hVaQd : hatV R a c ≤ Q R d := (hatV_le_radius R hca.le).trans
    (V_le_Q_of_dist_add_two_lt R ha (by rw [had, earlier.distance]; decide))
  have hVcQd : hatV R c a ≤ Q R d := (hatV_le_radius R hac.le).trans
    (V_le_Q_of_dist_add_two_lt R hc (by rw [hcd, earlier.distance]; decide))
  have hWQc : hatW R d c a ≤ Q R c :=
    (hatW_le_radius R hcd.le hac.le).trans
      ((Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le c d 4 6
        (by rw [SimpleGraph.dist_comm, hcd])).trans
        (Escape.Propagation.RadiusFour.VBall_le_Q c hc 6 (by rw [earlier.distance]; decide)))
  have hWcomm : ⁅hatV R a c, hatW R d c a⁆ ≤ Z R c := by
    apply (le_inf ((commutator_mono le_rfl hWQc).trans hpre) ?_).trans
      (intersection_le common earlier ha hc hd hf hat hct hac hcd hdf hft hfn)
    rw [commutator_comm]
    exact (commutator_mono le_rfl hVaQd).trans (second_le_first hd hcd hVcQd hpre')
  have hQacomm : ⁅hatV R a c, Q R a⁆ ≤ Z R c := by
    have hH : H R a ≤ Z R c :=
      (H_le_edge_Z common earlier ha hat).trans (Escape.EdgeTransfer.edge_Z_le c t hc hct)
    have hZ : ⁅Z R a, Q R a⁆ ≤ H R a := (geometry.centralizes a ha).le.trans bot_le
    have hVQ : Vcirc R a ≤ Q R a :=
      (DistanceEight.Vcirc_le_V R a).trans (V_le_Q R ha common.large_distance)
    have hZQ : Z R a ≤ Q R a := (Z_le_VBall R a 2).trans (V_le_Q R ha common.large_distance)
    have hnH : Q R a ≤ normalizer (H R a : Set (FreeAmalgam R)) :=
      normalizer_commutator_ge_right (Vcirc R a) (Q R a)
    rw [hidentity]
    exact ((commutator_mono (sup_le (le_commutatorPreimage hVQ le_rfl)
      (le_commutatorPreimage hZQ hZ)) le_rfl).trans
        (commutator_commutatorPreimage_le _ _ _ hnH)).trans hH
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hQtZ : Q R t ≤ normalizer (Z R c : Set (FreeAmalgam R)) :=
    (show Q R t ≤ stabilizer R c from fun _ hx => hx.2 c (adjacent_symm R hct)).trans
      (Z_normalized R c)
  have hWQt : hatW R d c a ≤ Q R t := by
    intro x hx
    have h : x * 1 ∈ (hatW R d c a : Set (FreeAmalgam R)) * (Q R a : Set (FreeAmalgam R)) :=
      ⟨x, hx, 1, (Q R a).one_mem, rfl⟩
    simpa only [hproduct, mul_one, SetLike.mem_coe] using h
  have hQgen : Q R c ≤ hatW R d c a ⊔ Q R a := by
    intro x hx
    have hx' : x ∈ (hatW R d c a : Set (FreeAmalgam R)) * (Q R a : Set (FreeAmalgam R)) := by
      rw [hproduct]
      exact Q_le_adjacent_h R ht hct hx
    obtain ⟨w, hw, q, hq, rfl⟩ := hx'
    exact (hatW R d c a ⊔ Q R a).mul_mem (mem_sup_left hw) (mem_sup_right hq)
  rw [commutator_comm] at hWcomm hQacomm ⊢
  exact (commutator_mono (hQgen.trans
    (sup_le (le_commutatorPreimage hWQt hWcomm)
      (le_commutatorPreimage (Q_le_adjacent_h R ht hat) hQacomm))) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hQtZ)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
