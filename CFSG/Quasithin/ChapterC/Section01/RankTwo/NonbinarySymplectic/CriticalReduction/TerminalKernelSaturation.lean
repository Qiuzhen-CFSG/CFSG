module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalCenters
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalRefinement
public import Theory.Representation.SymplecticFourOrthogonalCover.InvariantRefinement

/-!
# Whole moving central kernels on the terminal critical paths

A critical actor at every original nonbinary degree preserves no quadratic
refinement. If the full moving-cover kernel escaped its commutator, the
universal cover would supply such a refinement. Thus both complete moving
fixed kernels belong to the full critical commutator. At distance at least
four its intersection with the full vertex center is exactly that entire
kernel. The literal natural projection gives its order as the critical
image order times the fixed-kernel order. Conjugacy of the moving kernels
at the two endpoints then identifies the two critical image orders.

On the actual large-mover terminal sequence, this saturates the previously
retained central intersections with the whole moving fixed kernels. The
prescribed residual shifts fix these kernels and identify them after two
backward steps. Every terminal commutator consequently has the same full
order q times the original fixed-kernel order. At distance six the third
shift ends at the original starting vertex; saturation and propagation
identify the two alternating kernels as well. All path choices, full
quotient kernels and central attachments are retained.

These are the kernel and order comparisons used in MS93 (5.10), printed
p.922, using (3.3), printed pp.866--867. The remaining unequal-contained
Lambda selectors, normalizer comparison, terminal exclusions (5.10)--(5.12)
and minimum-replacement distance-two witness are not asserted here. The
separate original-radical characteristic-control obligation is unchanged.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem critical_fixed_kernel_le
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical) :
    U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ≤
      ⁅Z d.radical a,Z d.radical z⁆ := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  obtain ⟨β,hβmark,hβno⟩ := h.replacement_refinement_free_inner_actor d
    (show Nat.card E.Carrier=Nat.card F by rw [E.card_eq,hE,h.field_card]) path hb
    s e he (h.replacement_component_image_structure d).2.2.2.2 j hj hjr κ hκQ hconj
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hact (x : Z d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (β x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (β x)) w))=_
    rw [hβmark x (hAS x.property)]
    exact hconj ⟨x.val,hAS x.property⟩ w
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j ≤ ⁅Z d.radical a,Z d.radical z⁆ := by
    by_contra hn
    obtain ⟨c,hc⟩ := embedded_cover_preserves_refinement_of_kernel_escape
      ⁅Z d.radical a,Z d.radical z⁆ (Z d.radical a) σ p he j β hact
      (by rw [hjr]; exact commutator_mono le_rfl (U_le_Z z)) hn
    apply hβno
    refine ⟨c,?_⟩
    rintro ⟨b,⟨x,rfl⟩⟩ v
    exact hc x v
  rintro x ⟨hx,hc⟩
  obtain ⟨w,rfl⟩ := (hjr.symm ▸ hx : x ∈ j.range)
  exact hk ⟨w,(hker w.toAdd).mpr hc,rfl⟩

/-- The complete fixed kernels at both ends belong to the full critical
commutator, at every original nonbinary degree. -/
theorem Input.replacement_critical_commutator_contains_fixed_kernels
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical) :
    (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) ⊔
      (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) ≤
        ⁅Z d.radical a,Z d.radical z⁆ := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨a,z,path⟩).reverse hedge hb
  have hr := critical_fixed_kernel_le h d rev.path hb
  change U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≤
    ⁅Z d.radical z,Z d.radical a⁆ at hr
  rw [commutator_comm] at hr
  exact sup_le hr (critical_fixed_kernel_le h d path hb)

/-- The full vertex-center intersection of a critical commutator is the
entire fixed subgroup of U, including its covering kernel. -/
theorem Input.replacement_critical_commutator_full_center_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    ⁅Z d.radical a,Z d.radical z⁆ ⊓ (stabilizer d.radical a ⊓
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) =
        U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have hD : ⁅Z d.radical a,Z d.radical z⁆ ≤ U d.radical a := by
    rw [h.replacement_Z_commutator_eq_U d geometry hb path.start_color
      (Z d.radical z) (path.endpoint_Z_le_start_stabilizer (by omega)),commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((path.endpoint_Z_le_start_stabilizer (by omega)).trans (U_normalized a))
  apply le_antisymm
  · exact le_inf (inf_le_left.trans hD) (inf_le_right.trans inf_le_right)
  · exact le_inf
      ((inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer a))).trans
        (le_sup_left.trans (h.replacement_critical_commutator_contains_fixed_kernels d path (by omega))))
      (le_inf (inf_le_left.trans ((U_le_Z a).trans (Z_le_stabilizer d.radical a))) inf_le_right)

/-- The exact order of the full critical commutator is its critical image
order times the order of the whole moving central kernel. -/
theorem Input.replacement_critical_commutator_card
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    Nat.card (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) =
      (Q d.radical z).relIndex (Z d.radical a) *
        Nat.card (U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) := by
  let D := ⁅Z d.radical a,Z d.radical z⁆
  let C := stabilizer d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  have hi := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) (D ⊓ C) D bot_le inf_le_left
  simp only [relIndex_bot_left,inf_relIndex_left] at hi
  rw [h.replacement_critical_commutator_full_center_kernel d path hb] at hi
  rw [h.replacement_critical_commutator_central_index d path hb] at hi
  exact hi.symm.trans (Nat.mul_comm _ _)

omit h d in
private theorem moving_center_kernel_act
    {M : Type*} [Group M] {R : Subgroup M} (y : FreeAmalgam R) (a : Vertex R) :
    U R (act R y a) ⊓ centralizer (stabilizer R (act R y a) : Set (FreeAmalgam R)) =
      (U R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R))).map
        (MulAut.conj y⁻¹).toMonoidHom := by
  rw [U_act,stabilizer_act,map_inf _ _ _ (MulAut.conj y⁻¹).injective,
    Theory.GroupTheory.map_centralizer_equiv]
  simp only [coe_map,MulEquiv.coe_toMonoidHom]

omit h d in
private theorem moving_center_kernel_card_eq
    {M : Type*} [Group M] {R : Subgroup M} {a c : Vertex R}
    (ha : color R a=false) (hc : color R c=false) :
    Nat.card (U R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) : Subgroup (FreeAmalgam R)) =
      Nat.card (U R c ⊓ centralizer (stabilizer R c : Set (FreeAmalgam R)) : Subgroup (FreeAmalgam R)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R hc
  obtain ⟨j,hj⟩ := exists_mVertex_of_color R ha
  have hy : act R (g⁻¹*j) c=a := by
    rw [hg,act_mVertex,mul_inv_cancel_left,←hj]
  rw [←hy,moving_center_kernel_act,card_map_of_injective (MulAut.conj (g⁻¹*j)⁻¹).injective]

/-- The full commutator has the same order at both endpoints, and the
moving fixed kernels are conjugate. Hence the two literal critical image
orders agree, without deleting either kernel. -/
theorem Input.replacement_critical_indices_equal
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    (Q d.radical z).relIndex (Z d.radical a) = (Q d.radical a).relIndex (Z d.radical z) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨a,z,path⟩).reverse hedge (by omega)
  have hi := h.replacement_critical_commutator_card d path hb
  have hi' := h.replacement_critical_commutator_card d rev.path hb
  change Nat.card (⁅Z d.radical z,Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) =
    (Q d.radical a).relIndex (Z d.radical z) *
      Nat.card (U d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) at hi'
  rw [commutator_comm,moving_center_kernel_card_eq path.end_color path.start_color] at hi'
  let := finite_Z d.radical a
  let C := U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  let : Finite C := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C)) (hi.symm.trans hi')

/-- The actual large-mover terminal paths retain the whole moving fixed
kernel in every critical commutator. The kernels repeat after two backward
shifts; their literal edge and preceding-center intersections agree, and
all these full commutators have order q times the original fixed-kernel order. -/
theorem Input.replacement_large_mover_terminal_saturated_kernels
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical p.first)
      (Q d.radical p.first) (Q d.radical (p.path.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical p.first)) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pointPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, let C := fun j => U d.radical (s j).first ⊓
          centralizer (stabilizer d.radical (s j).first : Set (FreeAmalgam d.radical))
        let D := ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆
        C (i+2) = C i ∧
        D ⊓ Z d.radical ((s (i+2)).path.walk.getVert 1) = C i ∧
        D ⊓ (stabilizer d.radical (s (i+1)).first ⊓
          centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) = C i ∧
        Nat.card D = Nat.card F * Nat.card (C 0) ∧
        (∀ k, C i ≤ stabilizer d.radical (s (i+k)).first ⊓
          centralizer (stabilizer d.radical (s (i+k)).first : Set (FreeAmalgam d.radical))) ∧
        (Q d.radical (s (i+2)).last).relIndex (Z d.radical (s (i+2)).first)=Nat.card F ∧
        (Q d.radical (s (i+2)).first).relIndex (Z d.radical (s (i+2)).last)=Nat.card F ∧
        (¬ Z d.radical (s (i+2)).first ⊓ Q d.radical (s (i+2)).last ≤
          B d.radical (s (i+1)).first (geometry.Z_normal (s (i+1)).first))) := by
  obtain ⟨s,hs0,hs,hover,hcent⟩ := h.replacement_large_mover_terminal_central_kernels d p hb hJm
  refine ⟨s,hs0,hs,hover,?_⟩
  intro i
  dsimp only
  obtain ⟨hia,hiz,heq,hiE,heqprev,hiprev,hnot,hall,hkernel,hsplit,hsplitz⟩ := hcent i
  have hsat := h.replacement_critical_commutator_full_center_kernel d (s (i+2)).path hb.le
  rw [hsat] at heq heqprev hall
  let C := fun j => U d.radical (s j).first ⊓
    centralizer (stabilizer d.radical (s j).first : Set (FreeAmalgam d.radical))
  have hperiod : C (i+2)=C i := by
    obtain ⟨t,⟨⟨y,hy,hyv,hyt,hidx⟩,hgen,hfix⟩,hct,hat,hfirst⟩ := (hs (i+1)).choice
    have he := (hs i).overlap 0 (by omega)
    simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
    rw [he] at hyv
    have hc : C (i+2) ≤ centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical)) :=
      (hall 1).trans inf_le_right
    have hfixed : (C (i+2)).map (MulAut.conj y⁻¹).toMonoidHom=C (i+2) :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hc ((stabilizer d.radical (s (i+1)).first).inv_mem
          (Ltilde_le_stabilizer _ hy))))
    have htransport := moving_center_kernel_act y (s i).first
    rw [←hyv] at htransport
    have heqmap : (C (i+2)).map (MulAut.conj y⁻¹).toMonoidHom =
        (C i).map (MulAut.conj y⁻¹).toMonoidHom := hfixed.trans htransport
    exact map_injective (MulAut.conj y⁻¹).injective heqmap
  have hcard := h.replacement_critical_commutator_card d (s (i+2)).path hb.le
  rw [hia,moving_center_kernel_card_eq (s (i+2)).path.start_color (s 0).path.start_color] at hcard
  rw [show U d.radical (s (i+2)).first ⊓ centralizer
    (stabilizer d.radical (s (i+2)).first : Set (FreeAmalgam d.radical))=C i from hperiod] at heq heqprev hall
  exact ⟨hperiod,heq,heqprev.symm,hcard,hall,hia,
    (h.replacement_critical_indices_equal d (s (i+2)).path hb.le).symm.trans hia,hkernel⟩

/-- At distance six, the endpoint of the third shifted path is the
original starting vertex. Kernel saturation and propagation then identify
both parity classes of the full fixed kernels on the same terminal sequence. -/
theorem Input.replacement_large_mover_distance_six_common_kernel
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : geometry.b d.radical=6)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical p.first)
      (Q d.radical p.first) (Q d.radical (p.path.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical p.first)) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pointPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, let C := U d.radical p.first ⊓
          centralizer (stabilizer d.radical p.first : Set (FreeAmalgam d.radical))
        let D := ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆
        U d.radical (s i).first ⊓ centralizer
          (stabilizer d.radical (s i).first : Set (FreeAmalgam d.radical)) = C ∧
        D ⊓ Z d.radical ((s (i+2)).path.walk.getVert 1) = C ∧
        Nat.card D = Nat.card F * Nat.card C ∧
        C ≤ stabilizer d.radical (s i).first ⊓
          centralizer (stabilizer d.radical (s i).first : Set (FreeAmalgam d.radical))) := by
  obtain ⟨s,hs0,hs,hover,hdata⟩ :=
    h.replacement_large_mover_terminal_saturated_kernels d p (by omega) hJm
  let C := fun i => U d.radical (s i).first ⊓
    centralizer (stabilizer d.radical (s i).first : Set (FreeAmalgam d.radical))
  have hperiod (i : ℕ) : C (i+2)=C i := (hdata i).1
  have hlast : (s 3).last=(s 0).first := by
    have hh := shifted_last_vertex (pointPathChoice geometry (Nat.card F)) s hs 0 3 (by omega)
    simpa only [Nat.zero_add,hb,Nat.sub_self,SimpleGraph.Walk.getVert_zero] using hh
  have h0D : C 0 ≤ ⁅Z d.radical (s 3).first,Z d.radical (s 3).last⁆ := by
    apply le_trans _ (le_sup_right.trans
      (h.replacement_critical_commutator_contains_fixed_kernels d (s 3).path (by omega)))
    rw [hlast]
    exact inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer _))
  have hprop := (hdata 0).2.2.2.2.1
  have h03 : C 0 ≤ C 3 := by
    rw [show C 3 = ⁅Z d.radical (s 3).first,Z d.radical (s 3).last⁆ ⊓
      (stabilizer d.radical (s 3).first ⊓ centralizer
        (stabilizer d.radical (s 3).first : Set (FreeAmalgam d.radical))) from
      (h.replacement_critical_commutator_full_center_kernel d (s 3).path (by omega)).symm]
    exact le_inf h0D (by simpa only [Nat.zero_add] using hprop 3)
  have heq03 : C 0=C 3 := by
    let := finite_Z d.radical (s 3).first
    let : Finite (C 3) := Finite.of_injective
      (inclusion (inf_le_left.trans (U_le_Z (s 3).first))) (inclusion_injective _)
    exact eq_of_le_of_card_ge h03
      (moving_center_kernel_card_eq (s 3).path.start_color (s 0).path.start_color).le
  have hone : C 1=C 0 := (hperiod 1).symm.trans heq03.symm
  have hconstant (i : ℕ) : C i=C 0 := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      by_cases hzero : i=0
      · subst i; rfl
      by_cases hone' : i=1
      · subst i; exact hone
      have htwo : 2 ≤ i := by omega
      calc
        C i = C (i-2) := by simpa only [Nat.sub_add_cancel htwo] using hperiod (i-2)
        _ = C 0 := ih (i-2) (by omega)
  refine ⟨s,hs0,hs,hover,?_⟩
  intro i
  dsimp only
  obtain ⟨hi,hedge,hprev,hcard,hall,_,_,_⟩ := hdata i
  have hC0 : C 0 = U d.radical p.first ⊓
      centralizer (stabilizer d.radical p.first : Set (FreeAmalgam d.radical)) := by
    change U d.radical (s 0).first ⊓ centralizer
      (stabilizer d.radical (s 0).first : Set (FreeAmalgam d.radical)) = _
    rw [hs0]
  have hedge' : ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆ ⊓
      Z d.radical ((s (i+2)).path.walk.getVert 1) = C 0 := hedge.trans (hconstant i)
  have hci : C 0 ≤ stabilizer d.radical (s i).first ⊓
      centralizer (stabilizer d.radical (s i).first : Set (FreeAmalgam d.radical)) := by
    simpa only [Nat.zero_add] using hprop i
  exact ⟨(hconstant i).trans hC0,hedge'.trans hC0,by simpa only [←hC0] using hcard,by rwa [←hC0]⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
