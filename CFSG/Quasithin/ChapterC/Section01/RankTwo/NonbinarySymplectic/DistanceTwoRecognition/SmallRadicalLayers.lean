module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.WholeKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SmallRadicalStructure
public import Theory.Representation.SymplecticFourOrthogonalCover.DisplacementLifting
public import Theory.SpecificGroups.SymplecticFour.QuadraticRefinementObstruction

/-!
# Fixed attachments in the field-sized critical pair

When the replacement image has order q, the full central layer is Z = U Z_t.
Consequently the common critical displacement is exactly [U_a,U_z], with
both complete central-cover kernels retained. A full natural root preserves
no quadratic refinement, so each cover kernel lies in that displacement.
The literal natural projection then gives index q over each kernel and the
exact order q times the kernel order.

The last theorem applies these statements to the proper nonsylow branch,
discharging the field-sized premise from the original odd-index witness.
No identification of the two fixed kernels, their vanishing, radical
saturation, or field-degree restriction is asserted here. Those are the
remaining comparisons before the distance-two block application.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3) and the fixed-layer comparison in (3.7), printed pp.867,874--876.
The natural-root calculation uses the universal orthogonal cover and its
original projection, without imposing scalar closure on its binary kernel.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
open Theory.SpecificGroups.SymplecticFour

private theorem embedded_root_displacement_index
    {E W G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (U A : Subgroup G) (hAU : A ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range = U)
    (β : A →* L (K := E))
    (hact : ∀ a : A, ∀ w : W, j (Multiplicative.ofAdd (σ (β a) w)) =
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hF : 2 < Nat.card E) (hcard : Nat.card β.range = Nat.card E)
    (hdim : Module.finrank E (displacementSpace (β.range.map (commutator (Sp E)).subtype)) = 1)
    (hquad : ∀ x ∈ β.range.map (commutator (Sp E)).subtype,
      ∀ y ∈ β.range.map (commutator (Sp E)).subtype,
        ∀ v : Vector E, x • (y • v-v)=y • v-v) :
    let C := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
    C ≤ ⁅A,U⁆ ∧ C.relIndex ⁅A,U⁆ = Nat.card E := by
  let C := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  let α := (commutator (Sp E)).subtype.comp β
  have hαrange : α.range = β.range.map (commutator (Sp E)).subtype := MonoidHom.range_comp _ _
  have hC : C ≤ ⁅A,U⁆ := by
    by_contra hn
    obtain ⟨c,hc⟩ := embedded_cover_preserves_refinement_of_kernel_escape
      ⁅A,U⁆ A σ p hp j β hact (by rw [hjr]) hn
    have hαcard : Nat.card α.range = Nat.card E := by
      rw [hαrange,card_map_of_injective (commutator (Sp E)).subtype_injective,hcard]
    apply no_refinement_of_displacement_one hF α.range hαcard (hαrange.symm ▸ hdim)
      (hαrange.symm ▸ hquad)
    refine ⟨c,?_⟩
    rintro ⟨a,⟨x,rfl⟩⟩ v
    exact hc x v
  obtain ⟨π,hπ,hπj,hπact⟩ := exists_equivariant_embedded_projection U A hAU σ
    (binaryNatural (K := E)) j hj hjr p.toLinearMap hp.1
    (fun x w => LinearMap.congr_fun (p.isIntertwining' x) w) β hact
  have hker : π.ker.map U.subtype = C := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      have huj : u.val ∈ j.range := by rw [hjr]; exact u.property
      obtain ⟨w,hw⟩ := huj
      have he : u = ⟨j w,by rw [←hjr]; exact MonoidHom.mem_range.mpr ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
      refine ⟨w,?_,hw⟩
      have hh : π u = 1 := hu
      rw [he] at hh
      exact congrArg Multiplicative.toAdd ((hπj w.toAdd).symm.trans hh)
    · rintro x ⟨w,hw,rfl⟩
      refine ⟨⟨j w,by rw [←hjr]; exact MonoidHom.mem_range.mpr ⟨w,rfl⟩⟩,?_,rfl⟩
      change π ⟨j w,_⟩ = 1
      exact (hπj w.toAdd).trans (congrArg Multiplicative.ofAdd hw)
  let B := (displacementSpace α.range).toAddSubgroup.toSubgroup
  let P := (B.comap π).map U.subtype
  have hMP : ⁅A,U⁆ ≤ P := by
    apply commutator_le.mpr
    intro a ha u hu
    let v : U := ⟨a*u*a⁻¹,(mem_normalizer_iff.mp (hAU ha) u).mp hu⟩ * ⟨u,hu⟩⁻¹
    refine ⟨v,?_,rfl⟩
    change (π v).toAdd ∈ displacementSpace α.range
    dsimp only [v]
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    rw [hπact ⟨a,ha⟩ ⟨u,hu⟩]
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp α.range.subtype)
      ⟨α ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩ (π ⟨u,hu⟩).toAdd
  have hMU : ⁅A,U⁆ ≤ U := le_normalizer_iff_commutator_le_right.mp hAU
  have hmap : (⁅A,U⁆.subgroupOf U).map π = B := by
    apply le_antisymm
    · rintro v ⟨u,hu,rfl⟩
      obtain ⟨w,hw,he⟩ := hMP hu
      have he' : w=u := Subtype.ext he
      exact he' ▸ hw
    · intro v hv
      obtain ⟨w,hw,hwm⟩ := natural_displacement_lifts U A j hjr β σ hact p hp.1 v.toAdd hv
      refine ⟨⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩,hwm,?_⟩
      exact (hπj w).trans (congrArg Multiplicative.ofAdd hw)
  have hindex : C.relIndex ⁅A,U⁆ = Nat.card B := by
    rw [←hmap,←relIndex_ker]
    have hi := relIndex_subgroupOf (H := C) hMU
    rw [←hker,subgroupOf_map_subtype_eq] at hi
    rw [hker] at hi
    exact hi.symm
  have hBcard : Nat.card B = Nat.card E := by
    let e : B ≃ displacementSpace α.range :=
      { toFun := fun x => ⟨x.val.toAdd,x.property⟩
        invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := E),hαrange,hdim,pow_one]
  exact ⟨hC,hindex.trans hBcard⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full omega-center layer is Z and is generated by U and the edge
center. The entire fixed attachment is included through that edge center. -/
theorem replacement_field_sized_central_layers
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    X d.radical a = Z d.radical a ∧
      Z d.radical a = U d.radical a ⊔ Z d.radical t := by
  have hX := replacement_field_sized_X_decomposition h d path hb hat hzt hsize
  have hfix := replacement_fixed_X_le_edge h d (g := g) (by omega) path.start_color hat
  have hZX := g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
  have htZ := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  have he : X d.radical a = Z d.radical a := by
    apply le_antisymm _ hZX
    rw [hX]
    exact sup_le (U_le_Z a) (hfix.trans htZ)
  refine ⟨he,le_antisymm ?_ (sup_le (U_le_Z a) htZ)⟩
  rw [←he,hX]
  exact sup_le_sup_left hfix _

/-- In the field-sized case the full critical displacement is supplied by U. -/
theorem replacement_field_sized_displacement_eq_moving
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ⁅Z d.radical a,Z d.radical z⁆ = ⁅U d.radical a,Z d.radical z⁆ := by
  let C₀ := X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  have hcentral : C₀ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    have hz : Z d.radical z ≤ Q d.radical t := by
      rw [←(replacement_field_sized_paired_edges h d path hb hat hzt hsize).1]
      exact le_sup_right
    apply (hz.trans (replacement_inner_edge h d (by omega) path.start_color hat)).trans
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_right
    · exact (Q_le_centralizer_X d.radical a).trans (centralizer_le inf_le_left)
  have hX : Z d.radical a ≤ U d.radical a ⊔ C₀ := by
    rw [←replacement_field_sized_X_decomposition h d path hb hat hzt hsize]
    exact g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
  apply le_antisymm _ (commutator_mono (U_le_Z a) le_rfl)
  rw [commutator_comm (Z d.radical a),commutator_comm (U d.radical a)]
  exact commutator_le_moving_of_inner_mod_centralizer (Z d.radical z) (U d.radical a)
    (Z d.radical a)
    (((U_le_Z a).trans (Z_le_stabilizer_of_dist_le a
      (g.exists_critical a path.start_color) path.critical.1.le)).trans (Z_normalized d.radical z))
    (hX.trans (sup_le_sup_left hcentral _))


/-- Both moving layers supply the common displacement; the full fixed
attachments inside U are retained in this equality. -/
theorem replacement_field_sized_displacement_eq_paired_moving
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ⁅Z d.radical a,Z d.radical z⁆ = ⁅U d.radical a,U d.radical z⁆ := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hUZ : U d.radical z ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (U_le_Z z).trans
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hcent : Z d.radical t ≤ centralizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat).trans
      ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))
  have hZa : Z d.radical z ≤ U d.radical z ⊔ centralizer
      (U d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [(replacement_field_sized_central_layers h d rev hb hzt hat hsize).2]
    exact sup_le_sup_left hcent _
  rw [replacement_field_sized_displacement_eq_moving h d path hb hat hzt hsize]
  exact le_antisymm (commutator_le_moving_of_inner_mod_centralizer
    (U d.radical a) (U d.radical z) (Z d.radical z) hUZ hZa)
    (commutator_mono le_rfl (U_le_Z z))

/-- The common critical displacement contains the entire fixed attachment;
its quotient by that attachment has order q at the original field degree. -/
theorem replacement_field_sized_fixed_layer_index
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    A ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      A.relIndex ⁅Z d.radical a,Z d.radical z⁆ = 2^n := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have haq := (replacement_field_sized_edge_factorization h d rev hb hzt hat hsize).1
  have hzq := (replacement_field_sized_edge_factorization h d path hb hat hzt hsize).1
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z d.radical z, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hZA x) v
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ hδ hδcard (haq.trans hFc.symm)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hh := embedded_root_displacement_index (U d.radical a) (Z d.radical z)
    (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
    (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he j hj hjr β hβ
    hcard hβcard hβdim hβquad
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  dsimp only at hh
  rw [hk,commutator_comm (Z d.radical z),
    ←replacement_field_sized_displacement_eq_moving h d path hb hat hzt hsize,hFc] at hh
  exact hh


/-- Both full fixed attachments lie in the common elementary displacement,
and they have the same order. Equality or vanishing is not assumed. -/
theorem replacement_field_sized_paired_fixed_layers
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    let W := ⁅Z d.radical a,Z d.radical z⁆
    W = ⁅U d.radical a,U d.radical z⁆ ∧
      A ⊔ A' ≤ W ∧ W ≤ U d.radical a ⊓ U d.radical z ∧
      Nat.card W = 2^n * Nat.card A ∧ Nat.card A = Nat.card A' := by
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  let W := ⁅Z d.radical a,Z d.radical z⁆
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have ha := replacement_field_sized_fixed_layer_index h d path hb hat hzt hsize
  have hz := replacement_field_sized_fixed_layer_index h d rev hb hzt hat hsize
  rw [commutator_comm (Z d.radical z)] at hz
  have hWU : W ≤ U d.radical a := by
    rw [show W = ⁅Z d.radical a,Z d.radical z⁆ from rfl,
      replacement_field_sized_displacement_eq_moving h d path hb hat hzt hsize]
    exact le_normalizer_iff_commutator_le_left.mp
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
  have hWU' : W ≤ U d.radical z := by
    rw [show W = ⁅Z d.radical a,Z d.radical z⁆ from rfl,commutator_comm,
      replacement_field_sized_displacement_eq_moving h d rev hb hzt hat hsize]
    exact le_normalizer_iff_commutator_le_left.mp
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
  let := finite_Z d.radical a
  let : Finite W := Finite.of_injective (inclusion (hWU.trans (U_le_Z a)))
    (inclusion_injective _)
  have hcard : Nat.card A * 2^n = Nat.card W := by
    have hi := (A.subgroupOf W).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe ha.1).toEquiv] at hi
    exact ha.2 ▸ hi
  have hcard' : Nat.card A' * 2^n = Nat.card W := by
    have hi := (A'.subgroupOf W).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hz.1).toEquiv] at hi
    exact hz.2 ▸ hi
  exact ⟨replacement_field_sized_displacement_eq_paired_moving h d path hb hat hzt hsize,
    sup_le ha.1 hz.1,le_inf hWU hWU',by rw [←hcard,Nat.mul_comm],
    Nat.eq_of_mul_eq_mul_right (by positivity) (hcard.trans hcard'.symm)⟩

/-- The original odd-index comparison supplies the field-sized hypothesis in
the proper nonsylow branch, keeping the full fixed kernels on both sides. -/
theorem replacement_proper_nonsylow_paired_fixed_layers
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    let W := ⁅Z d.radical a,Z d.radical z⁆
    W = ⁅U d.radical a,U d.radical z⁆ ∧
      A ⊔ A' ≤ W ∧ W ≤ U d.radical a ⊓ U d.radical z ∧
      Nat.card W = 2^n * Nat.card A ∧ Nat.card A = Nat.card A' :=
  replacement_field_sized_paired_fixed_layers h d path hb hat hzt
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
