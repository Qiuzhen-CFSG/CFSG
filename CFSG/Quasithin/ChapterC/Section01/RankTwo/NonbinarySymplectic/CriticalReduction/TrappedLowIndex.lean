module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootKernels
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootTrappedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NaturalLower
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Kernel

/-!
# Exact commutators and full kernels in the trapped low-index branch

A nonnormal trapped neighboring seed has a nonzero commutator on the entire
critical X-intersection. The lower natural-subspace bound and the upper
hyperplane bound make its order exactly q. The root decomposition retains
all central attachments and identifies this with the commutator on the
neighbor's whole moving layer. Its full U- and Z-fixed indices are exactly q.
The literal source actor U_z intersect Q_a has the same commutator and full
fixed kernel as X_z intersect Q_a, so both exact indices hold for it too.

Individual residual generation then places the full fixed kernel joined
with the starting seed in B. The selected-path consumer keeps the same
conjugator, individual mover, whole-Z equalities and every overlap.
These are the trapped-branch calculations used in MS93 (5.7)--(5.8),
printed pp.919--920. The low-index twist contradiction, contained-image
selection and terminal distance exclusions remain necessary.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped commutatorElement IsMulCommutative Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
private theorem fixed_index_of_split {G : Type*} [Group G]
    (X U C E : Subgroup G) [IsMulCommutative X]
    (hUX : U ≤ X) (hsplit : X = U ⊔ C)
    (hCE : C ≤ centralizer (E : Set G)) :
    (centralizer (E : Set G)).relIndex X =
      (centralizer (E : Set G)).relIndex U := by
  let Y := X ⊓ centralizer (E : Set G)
  have hCX : C ≤ X := le_sup_right.trans_eq hsplit.symm
  have hjoin : U ⊔ Y = X := by
    apply le_antisymm (sup_le hUX inf_le_left)
    exact hsplit.le.trans (sup_le le_sup_left
      ((show C ≤ Y from le_inf hCX hCE).trans le_sup_right))
  let : CommGroup X := IsMulCommutative.instCommGroup
  have hh := relIndex_sup_right (U.subgroupOf X) (Y.subgroupOf X)
  rw [←subgroupOf_sup hUX (show Y ≤ X from inf_le_left),hjoin,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf hUX] at hh
  have he (V : Subgroup G) (hv : V ≤ X) :
      Y.subgroupOf V = (centralizer (E : Set G)).subgroupOf V := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hv x.property,hx⟩⟩
  change (Y.subgroupOf X).index = (Y.subgroupOf U).index at hh
  rwa [he X le_rfl,he U hUX] at hh


variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- On an actor in the actual endpoint stabilizer, the full X-intersection
and the source U-intersection have identical commutators and identical full
fixed subgroups. The ambient central attachment is retained in the proof. -/
theorem Input.replacement_root_intersection_fixed_and_commutator
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYS : Y ≤ stabilizer d.radical z) :
    ⁅Y,X d.radical z ⊓ Q d.radical a⁆ = ⁅Y,U d.radical z ⊓ Q d.radical a⁆ ∧
      Y ⊓ centralizer ((X d.radical z ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _) =
      Y ⊓ centralizer ((U d.radical z ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let A := X d.radical z ⊓ Q d.radical a
  let A₀ := U d.radical z ⊓ Q d.radical a
  let D := X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by
          rw [geometry.distance_constant a path.start_color]
          exact lt_of_lt_of_le (by decide : 0 < 4) hb)
        z path.end_color path.critical }
  have hsplit : X d.radical z=U d.radical z ⊔ D :=
    h.replacement_root_X_decomposition_center d rev hb hsmall
  have hDY : D ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hYS)
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hDT : D ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hAZ)
  have hZX : Z d.radical z ≤ X d.radical z := geometry.omega_bound z path.end_color
    (by rw [geometry.distance_constant z path.end_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  have hUX := (U_le_Z z).trans hZX
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hDU : D ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans ((centralizer_le ((U_le_Z z).trans (Z_le_stabilizer d.radical z))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hAjoin : A ≤ A₀ ⊔ D := by
    intro x hx
    have hx' : x ∈ (U d.radical z : Set (FreeAmalgam d.radical)) * (D : Set (FreeAmalgam d.radical)) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hDU,←hsplit]
      exact hx.1
    obtain ⟨u,hu,c,hc,rfl⟩ := hx'
    have huc : u*c ∈ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
      have hh := hx.2
      rw [←hCa] at hh
      exact hh.2
    have huT : u ∈ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
      have hh := (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).mul_mem
        huc ((centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).inv_mem (hDT hc))
      simpa only [mul_inv_cancel_right] using hh
    have huQ : u ∈ Q d.radical a := by
      rw [←hCa]
      exact ⟨hUS hu,huT⟩
    exact (A₀ ⊔ D).mul_mem (mem_sup_left ⟨hu,huQ⟩) (mem_sup_right hc)
  have hA₀A : A₀ ≤ A := inf_le_inf_right _ hUX
  have hcommU : ⁅A₀,Y⁆ ≤ U d.radical z :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hYS.trans (U_normalized z)))
  let := X_elementary d.radical z
  have hnorm : X d.radical z ≤ normalizer ((⁅A₀,Y⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    ((X d.radical z).le_centralizer.trans (centralizer_le (hcommU.trans hUX))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hupper : ⁅A₀ ⊔ D,Y⁆ ≤ ⁅A₀,Y⁆ := by
    apply commutator_sup_le_of_relative_normal (X d.radical z) A₀ D Y ⁅A₀,Y⁆
      hnorm (inf_le_left.trans hUX) inf_le_left le_rfl
    rw [commutator_eq_bot_iff_le_centralizer.mpr hDY]
    exact bot_le
  refine ⟨le_antisymm ?_ (commutator_mono le_rfl hA₀A),?_⟩
  · change ⁅Y,A⁆ ≤ ⁅Y,A₀⁆
    rw [commutator_comm Y A,commutator_comm Y A₀]
    exact (commutator_mono hAjoin le_rfl).trans hupper
  · apply le_antisymm (inf_le_inf_left _ (centralizer_le hA₀A))
    refine le_inf inf_le_left (le_centralizer_iff.mpr ?_)
    exact hAjoin.trans (sup_le (le_centralizer_iff.mp inf_le_right)
      (hDY.trans (centralizer_le inf_le_left)))

/-- Both full fixed indices and the literal trapped commutator have order q.
No lower bound on the B-relative moving index is assumed. -/
theorem Input.replacement_trapped_root_exact_indices
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    let A := X d.radical z ⊓ Q d.radical a
    ⁅Z d.radical v,A⁆ = ⁅U d.radical v,A⁆ ∧
      Nat.card (⁅Z d.radical v,A⁆ : Subgroup (FreeAmalgam d.radical)) = Nat.card F ∧
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical v) = Nat.card F ∧
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical v) = Nat.card F ∧
      ⁅Z d.radical v,A⁆ = ⁅Z d.radical v,U d.radical z ⊓ Q d.radical a⁆ ∧
      Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical)) =
        Z d.radical v ⊓ centralizer ((U d.radical z ⊓ Q d.radical a :
          Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      (centralizer ((U d.radical z ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex (U d.radical v) = Nat.card F ∧
      (centralizer ((U d.radical z ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex (Z d.radical v) = Nat.card F := by
  dsimp only
  let A := X d.radical z ⊓ Q d.radical a
  let Y := Z d.radical v
  have hYV : Y ≤ V d.radical a := le_sup_left.trans (neighbor_seed_join_le_radius hat hvt)
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hYS : Y ≤ stabilizer d.radical z :=
    (le_inf hYV htrap).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  obtain ⟨hi,hi'⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
    (by omega) Y hYS hYQ hn
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hs : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 := by
    rw [hi']; nlinarith
  have hs' : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hi]; nlinarith
  have hZA : Z d.radical z ⊓ Q d.radical a ≤ A :=
    inf_le_inf_right _ (geometry.omega_bound z path.end_color
      (by rw [geometry.distance_constant z path.end_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb))
  have hmove := h.replacement_seed_actor_centralizer_index_ge_field d path (by omega)
    Y hYS hYQ hn Y le_rfl hYS
  have hncomm : ⁅Y,A⁆ ≠ ⊥ := by
    intro he
    have hc : Z d.radical z ⊓ Q d.radical a ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
      hZA.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
    rw [relIndex_eq_one.mpr hc] at hmove
    omega
  have hcard : Nat.card (⁅Y,A⁆ : Subgroup (FreeAmalgam d.radical)) = Nat.card F :=
    le_antisymm (h.replacement_trapped_root_commutator_card_le_field d path hb hat hvt hn htrap)
      (h.replacement_root_intersection_commutator_card_ge_field d path hb hs' Y hYS hncomm)
  have hv : color d.radical v=false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hvt
    rw [path.start_color] at h1
    cases ht : color d.radical t <;> cases hv : color d.radical v <;> simp_all
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two a v path.start_color hv
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hat hvt))
  let D := Z d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))
  have hsplit : Y=U d.radical v ⊔ D :=
    h.replacement_root_neighbor_Z_decomposition d path hb hat hvt hs
  have hDA : D ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hAS)
  have hcomm : ⁅Y,A⁆=⁅U d.radical v,A⁆ := by
    have hUAn := hAS.trans (U_normalized v)
    have hcU : ⁅U d.radical v,A⁆ ≤ U d.radical v :=
      le_normalizer_iff_commutator_le_left.mp hUAn
    let : IsElementaryAbelian 2 Y := geometry.Z_elementary (by omega) v hv
    have hnorm : Y ≤ normalizer ((⁅U d.radical v,A⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      (Y.le_centralizer.trans (centralizer_le (hcU.trans (U_le_Z v)))).trans
        (Subgroup.centralizer_le_normalizer _)
    apply le_antisymm ?_ (commutator_mono (U_le_Z v) le_rfl)
    change ⁅Y,A⁆ ≤ ⁅U d.radical v,A⁆
    rw [hsplit]
    apply commutator_sup_le_of_relative_normal Y (U d.radical v) D A ⁅U d.radical v,A⁆
      hnorm (U_le_Z v) (le_sup_right.trans_eq hsplit.symm) le_rfl
    rw [commutator_eq_bot_iff_le_centralizer.mpr hDA]
    exact bot_le
  have hnotQ : ¬ A ≤ Q d.radical v := by
    intro hAQ
    have hh : Y ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes v hv)).trans
        (centralizer_le hAQ)
    exact hncomm (commutator_eq_bot_iff_le_centralizer.mpr hh)
  have hidx : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical v) = Nat.card F :=
    le_antisymm
      (h.replacement_trapped_root_kernel_index_and_normalized d path hb hat hvt hn htrap).1
      (h.replacement_natural_fixed_index_lower d geometry hb hv A hAS hnotQ)
  let : IsElementaryAbelian 2 Y := geometry.Z_elementary (by omega) v hv
  have hfull := fixed_index_of_split Y (U d.radical v) D A (U_le_Z v) hsplit hDA
  obtain ⟨hsource,hZfixed⟩ :=
    h.replacement_root_intersection_fixed_and_commutator d path hb hs' Y hYS
  have hUfixed := (h.replacement_root_intersection_fixed_and_commutator d path hb hs'
    (U d.radical v) ((U_le_Z v).trans hYS)).2
  refine ⟨hcomm,hcard,hidx,hfull.trans hidx,hsource,hZfixed,?_,?_⟩
  · rw [←inf_relIndex_left,←hUfixed,inf_relIndex_left]
    exact hidx
  · rw [←inf_relIndex_left,←hZfixed,inf_relIndex_left]
    exact hfull.trans hidx

/-- Individual generation puts the entire trapped fixed kernel in B.
The same moving layer has nontrivial B-index at most q, so this result
also retains the small-index branch excluded by the strict-index argument. -/
theorem Input.replacement_trapped_root_fixed_kernel_in_B
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hgen : Ltilde d.radical a ≤
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical t) (Nat.card F^2) ⊔ Z d.radical z)
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    let A := X d.radical z ⊓ Q d.radical a
    let D := (Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔ Z d.radical a
    D ≤ B d.radical a (geometry.Z_normal a) ∧
      1 < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) ≤ Nat.card F := by
  dsimp only
  let A := X d.radical z ⊓ Q d.radical a
  let D := (Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔ Z d.radical a
  obtain ⟨hi,hEn,hZn⟩ := h.replacement_trapped_root_kernel_index_and_normalized d path hb hat hvt hn htrap
  have hDn : Ltilde d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    hgen.trans (sup_le hEn hZn)
  have hDV : D ≤ V d.radical a :=
    (sup_le_sup inf_le_left le_rfl).trans (neighbor_seed_join_le_radius hat hvt)
  have hYV := neighbor_seed_join_le_radius hat hvt
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have haQ : Z d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    apply Z_le_Q_of_dist_lt _ a (geometry.exists_critical a path.start_color)
    rw [path.dist_start (Nat.sub_le _ _),geometry.distance_constant a path.start_color]
    have hh := path.length_eq_b
    change path.walk.length-2 < geometry.b d.radical
    omega
  have hYS : Z d.radical v ⊔ Z d.radical a ≤ stabilizer d.radical z :=
    (le_inf hYV (sup_le htrap haQ)).trans
      (truncated_radius_le_endpoint_stabilizer path (by omega))
  obtain ⟨_,hroot⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
    (by omega) (Z d.radical v) (le_sup_left.trans hYS) (le_sup_left.trans hYQ) hn
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 := by
    rw [hroot]; nlinarith
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
  have hfixed : (U d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ≤
      B d.radical a (geometry.Z_normal a) :=
    ((inf_le_inf_right _ (U_le_Z v)).trans le_sup_left).trans hDB
  let := finite_Z d.radical v
  let : Finite (U d.radical v) := Finite.of_injective (inclusion (U_le_Z v)) (inclusion_injective _)
  have hidxB : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) ≤
      (U d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical v) :=
    relIndex_le_of_le_left hfixed index_ne_zero_of_finite
  rw [inf_relIndex_left] at hidxB
  refine ⟨hDB,?_,hidxB.trans hi⟩
  have hv : color d.radical v=false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hvt
    rw [path.start_color] at h1
    cases ht : color d.radical t <;> cases hv : color d.radical v <;> simp_all
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two a v path.start_color hv
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hat hvt))
  have hnot : ¬ U d.radical v ≤ B d.radical a (geometry.Z_normal a) := by
    intro hUB
    have hsplit := h.replacement_root_neighbor_Z_decomposition d path hb hat hvt hsmall
    have hZB : Z d.radical v ≤ B d.radical a (geometry.Z_normal a) := by
      rw [hsplit]
      have hDC : Z d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)) ≤
          Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical)) :=
        inf_le_inf_left _ (centralizer_le hAS)
      exact sup_le hUB ((hDC.trans le_sup_left).trans hDB)
    have hnorm := StrictIndex.neighbor_join_normalized_of_le_B geometry (by omega)
      (h.replacement_residual_edge_generation d) path.start_color hat hvt hZB
    exact hn ((path.endpoint_Z_le_start_stabilizer (by omega)).trans hnorm)
  have hne : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) ≠ 1 :=
    fun he => hnot (relIndex_eq_one.mp he)
  have hpos : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) ≠ 0 :=
    index_ne_zero_of_finite
  omega

/-- The original unequal-mover selector supplies either its backward path
or the complete trapped commutator and B-kernel data at that same neighbor.
All earlier source generation, full-Z fixedness and image clauses persist. -/
theorem Input.replacement_unequal_root_low_index_alternative
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    ∃ g ∈ Ltilde d.radical a,
      let w := act d.radical g⁻¹ t
      let v := act d.radical g⁻¹ c
      let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2)
      let Ja := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2)
      let Ec := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      J.map (MulAut.conj g).toMonoidHom =
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Ltilde d.radical a ≤ Ec ⊔ Z d.radical z ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      Z d.radical t ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,Ja⁆,Ja⁆ = ⊥ ∧ ⁅⁅U d.radical v,Ec⁆,Ec⁆ = ⊥ ∧
      (centralizer (Ec : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F^3 ∧
      ¬ Q d.radical a ≤ Ec ∧ Nat.card F^2 < (Q d.radical a).relIndex Ec ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
      (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
        (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
        Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
          (Z d.radical z ⊓ Q d.radical a) ∧
        X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
        ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥ ∧
        (Z d.radical v ⊔ Z d.radical a) ⊓ centralizer
          ((X d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) =
          Z d.radical a ⊔ ((Z d.radical v ⊔ Z d.radical a) ⊓ Q d.radical z) ∧
        Z d.radical z ≤ normalizer (((Z d.radical v ⊓ centralizer
          ((X d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ⊔
          Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ⁅Z d.radical v,X d.radical z ⊓ Q d.radical a⁆ =
          ⁅U d.radical v,X d.radical z ⊓ Q d.radical a⁆ ∧
        Nat.card (⁅Z d.radical v,X d.radical z ⊓ Q d.radical a⁆ :
          Subgroup (FreeAmalgam d.radical)) = Nat.card F ∧
        (centralizer ((X d.radical z ⊓ Q d.radical a :
          Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex (U d.radical v) = Nat.card F ∧
        (centralizer ((X d.radical z ⊓ Q d.radical a :
          Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex (Z d.radical v) = Nat.card F ∧
        (Z d.radical v ⊓ centralizer ((X d.radical z ⊓ Q d.radical a :
          Subgroup (FreeAmalgam d.radical)) : Set _)) ⊔ Z d.radical a ≤
            B d.radical a (geometry.Z_normal a) ∧
        1 < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) ∧
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) ≤ Nat.card F ∧
        ⁅Z d.radical v,X d.radical z ⊓ Q d.radical a⁆ =
          ⁅Z d.radical v,U d.radical z ⊓ Q d.radical a⁆ ∧
        Z d.radical v ⊓ centralizer ((X d.radical z ⊓ Q d.radical a :
          Subgroup (FreeAmalgam d.radical)) : Set _) =
        Z d.radical v ⊓ centralizer ((U d.radical z ⊓ Q d.radical a :
          Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        (centralizer ((U d.radical z ⊓ Q d.radical a :
          Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex (U d.radical v) = Nat.card F ∧
        (centralizer ((U d.radical z ⊓ Q d.radical a :
          Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex (Z d.radical v) = Nat.card F)) := by
  obtain ⟨g,hg,haw,hvw,hindex,htransport,hgen,hres,hfixed,hindividual,
    hquadA,hquadC,hcube,hnot,hlarge,hn,hback⟩ :=
      h.replacement_unequal_root_fixed_kernel_at_neighbor d path hb hat hfirst hct
        hnormal hsmall hne
  refine ⟨g,hg,haw,hvw,hindex,htransport,hgen,hres,hfixed,hindividual,
    hquadA,hquadC,hcube,hnot,hlarge,hn,?_⟩
  rcases hback with hback | ⟨htrap,hi,hi',hmove,hnorm,hquad,hcent,hendpoint⟩
  · exact Or.inl hback
  · obtain ⟨hcomm,hcard,hU,hZ,hsource,hsourceFixed,hsourceU,hsourceZ⟩ :=
      h.replacement_trapped_root_exact_indices d path hb haw hvw hn htrap
    obtain ⟨hB,hpos,hbound⟩ :=
      h.replacement_trapped_root_fixed_kernel_in_B d path hb haw hvw hn hres htrap
    exact Or.inr ⟨htrap,hi,hi',hmove,hnorm,hquad,hcent,hendpoint,
      hcomm,hcard,hU,hZ,hB,hpos,hbound,hsource,hsourceFixed,hsourceU,hsourceZ⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
