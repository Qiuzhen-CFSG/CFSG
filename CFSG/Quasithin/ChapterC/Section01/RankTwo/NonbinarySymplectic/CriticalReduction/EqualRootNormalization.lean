module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootKernels

/-!
# All source generators normalize the equal-root fixed kernel

The second selected commutator is trivial or equals the first, which lies
in the ambient-fixed seed. In either case full-cover duality puts the
original whole-Z fixed kernel inside the conjugated fixed kernel. The
endpoint commutator calculation makes the same conjugated endpoint
normalize this kernel joined with the starting seed.

Together with the original individual small mover and endpoint, the actual
source generation identity makes this subgroup residual-normal. Its index
is less than q fourth, so the small-radius theorem puts it in B. Its U-index
at most q contradicts the retained original B-relative moving index.
EqualRootPaths applies this exclusion at the same selected neighbors.

Source: MS93 (5.7), printed p.919, refs/Pushing up weak BN-pairs of rank two.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- In both source alternatives for the second commutator, the conjugated
endpoint normalizes the original full fixed kernel joined with the seed.
The conjugator is the one relating the two actual neighboring vertices. -/
theorem Input.replacement_equal_root_conjugate_kernel_normalized
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hsmall' : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2)
    (htrap : Z d.radical (act d.radical x v) ≤
      Q d.radical (path.walk.getVert (path.walk.length-2)))
    (hcommon : let A := X d.radical z ⊓ Q d.radical a
      ⁅Z d.radical (act d.radical x v),A⁆=⊥ ∨
        (⁅Z d.radical (act d.radical x v),A⁆=⁅Z d.radical v,A⁆ ∧
          ⁅Z d.radical v,A⁆ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    let A := X d.radical z ⊓ Q d.radical a
    (Z d.radical z).map (MulAut.conj x).toMonoidHom ≤
      normalizer (((Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  dsimp only at hcommon ⊢
  let A := X d.radical z ⊓ Q d.radical a
  let f := (MulAut.conj x).toMonoidHom
  let w := act d.radical x v
  let Y := Z d.radical w ⊔ Z d.radical a
  have hxa : act d.radical x a=a := hx
  have haw : Adjacent d.radical a (act d.radical x t) := by
    rw [←hxa]
    exact (adjacent_act_iff d.radical x a t).mpr hat
  have hww := (adjacent_act_iff d.radical x v t).mpr hvt
  have hYV : Y ≤ V d.radical a := neighbor_seed_join_le_radius haw hww
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hwS : Z d.radical w ≤ stabilizer d.radical z :=
    (le_inf (le_sup_left.trans hYV) htrap).trans
      (truncated_radius_le_endpoint_stabilizer path (by omega))
  have haS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hYa : Z d.radical a ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)).trans
      (centralizer_le inf_le_right)
  have hbound := h.replacement_root_fixed_commutator_le_seed d path (by omega) hsmall'
    Y le_sup_right (sup_le hwS haS) hYQ
  have hD : (Z d.radical w ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔ Z d.radical a ≤
      Y ⊓ centralizer (A : Set (FreeAmalgam d.radical)) :=
    sup_le (inf_le_inf le_sup_left le_rfl) (le_inf le_sup_right hYa)
  have hbound' := map_mono (f := f) ((commutator_mono hD le_rfl).trans hbound)
  have hwmap : (Z d.radical w).map f=Z d.radical v := by
    simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using
      (Z_act d.radical x⁻¹ (act d.radical x v)).symm
  have hZmap : (Z d.radical a).map f=Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hx)
  have hQmap : (Q d.radical a).map f=Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  rw [map_commutator,Subgroup.map_sup,←map_inf_centralizer_of_injective f
    (MulAut.conj x).injective,hwmap,hZmap] at hbound'
  have hv : color d.radical v=false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hvt
    have ht : color d.radical t=true := by
      cases ht : color d.radical t
      · exact False.elim (h1 (path.start_color.trans ht.symm))
      · rfl
    cases hvv : color d.radical v
    · rfl
    · exact False.elim (h2 (hvv.trans ht.symm))
  have hQS := Q_le_stabilizer_of_dist_le_two a v path.start_color hv
    (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hat hvt)
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans hQS
  have hfAS : A.map f ≤ stabilizer d.radical v :=
    ((map_mono (f := f) (show A ≤ Q d.radical a from inf_le_right)).trans_eq hQmap).trans hQS
  have hcomm : ⁅Z d.radical v,A.map f⁆ ≤ ⁅Z d.radical v,A⁆ := by
    have hc : ⁅Z d.radical v,A.map f⁆=⁅Z d.radical w,A⁆.map f := by
      rw [map_commutator,hwmap]
    rw [hc]
    rcases hcommon with hzero | ⟨he,hfixed⟩
    · rw [hzero,Subgroup.map_bot]
      exact bot_le
    · rw [he]
      rintro y ⟨u,hu,rfl⟩
      change x*u*x⁻¹ ∈ _
      rw [hfixed hu x hx,mul_inv_cancel_right]
      exact hu
  have hfixed := h.replacement_root_neighbor_fixed_antitone_of_commutator_le d path hb
    hat hvt hsmall (A.map f) A hfAS hAS hcomm
  apply le_normalizer_iff_commutator_le_left.mpr
  exact ((commutator_mono (sup_le_sup hfixed le_rfl) le_rfl).trans hbound').trans le_sup_right

/-- Generation by the original individual mover and both selected endpoint
conjugates excludes trapping in the equal-mover root branch. -/
theorem Input.replacement_equal_root_trapped_excluded
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hgen : (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical t) (Nat.card F^2) ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v))
    (hcommon : let A := X d.radical z ⊓ Q d.radical a
      ⁅Z d.radical (act d.radical x v),A⁆=⊥ ∨
        (⁅Z d.radical (act d.radical x v),A⁆=⁅Z d.radical v,A⁆ ∧
          ⁅Z d.radical v,A⁆ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    ¬ (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      Z d.radical (act d.radical x v) ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) := by
  rintro ⟨htrap,htrapx⟩
  let A := X d.radical z ⊓ Q d.radical a
  let D := (Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔ Z d.radical a
  obtain ⟨hi,hJn,hZn⟩ := h.replacement_trapped_root_kernel_index_and_normalized d path hb hat hvt hn htrap
  have hYV := neighbor_seed_join_le_radius hat hvt
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hvS : Z d.radical v ≤ stabilizer d.radical z :=
    (le_inf (le_sup_left.trans hYV) htrap).trans
      (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hroot := (h.replacement_critical_indices_eq_field_of_seed_escape d path
    (by omega) (Z d.radical v) hvS (le_sup_left.trans hYQ) hn).1
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsmall' : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hroot]; nlinarith
  have hZxn := h.replacement_equal_root_conjugate_kernel_normalized d path hb hat hvt x hx
    hsmall hsmall' htrapx hcommon
  have hDn : Ltilde d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (Ltilde_le_stabilizer a).trans (hgen ▸ sup_le (sup_le hJn hZn) hZxn)
  have hDV : D ≤ V d.radical a := (sup_le_sup inf_le_left le_rfl).trans hYV
  have hidx := (neighbor_seed_join_index_le geometry (by omega) path.start_color hat hvt).trans
    (h.replacement_root_neighbor_seed_index_le_cube d path hb hat hvt hsmall)
  have hYfin : Z d.radical v ⊔ Z d.radical a ≤ stabilizer d.radical a :=
    hYQ.trans (fun _ hx => hx.1)
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hYfin) (inclusion_injective _)
  have hDi : (Z d.radical a).relIndex D < Nat.card F^4 :=
    lt_of_le_of_lt ((relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl)
      index_ne_zero_of_finite).trans hidx) ((pow_lt_pow_iff_right₀ hq).mpr (by decide))
  have hDB : D ≤ B d.radical a (geometry.Z_normal a) :=
    h.replacement_small_radius_le_B d geometry (by omega) path.start_color D hDV hDn hDi
  have hfixed : U d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical)) ≤
      B d.radical a (geometry.Z_normal a) :=
    ((inf_le_inf_right _ (U_le_Z v)).trans le_sup_left).trans hDB
  let := finite_Z d.radical v
  let : Finite (U d.radical v) := Finite.of_injective (inclusion (U_le_Z v)) (inclusion_injective _)
  have hidxB : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) ≤
      (U d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical v) :=
    relIndex_le_of_le_left hfixed index_ne_zero_of_finite
  rw [inf_relIndex_left] at hidxB
  exact (not_lt_of_ge (hidxB.trans hi)) hmove

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
