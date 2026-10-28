module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourHyperplane
/-!
# Opposite hyperplane movement in the large critical-image branch

The midpoint is the exact kernel of each critical action when the critical
image has order at least q squared. A hyperplane above it therefore has
image of order q at the opposite endpoint. Fixed-space lifting through the
original natural cover makes every centralizer index a power of q. If the
opposite centralizer escapes the endpoint core, this forces its index to
be q. The symplectic displacement bound then shows that it fills the whole
hyperplane fixer modulo the full core. Consequently [Z,Y]=[Z,P].

The opposite hyperplane action is a full long root. Its lack of an invariant
quadratic refinement places the entire opposite attachment in [X,Z′],
and the literal cover projection gives index q over that attachment.
Thus |[X,Z′]|=q|A′|, with no splitting or vanishing of either attachment.

These are the first two claims in the escaping-centralizer subcase of
MS93 (3.7)(4), printed p.875. Comparing the two attachments inside these
movements, the remaining source (5)/(6) arguments and the field restriction
remain necessary. Source: Meierfrankenfeld--Stellmacher, *Pushing up weak
BN-pairs of rank two* (1993). Private cover transports adapt the checked
SourceThreePlane and CriticalFixedLayers calculations.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
private theorem cover_moving_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹) :
    (centralizer (A : Set G)).relIndex U =
      Nat.card F ^ Module.finrank F
        (displacementSpace ((commutator (Sp F)).subtype.comp β).range) := by
  let α := (commutator (Sp F)).subtype.comp β
  have hi := embedded_centralizer_index σ U A j hj hjr β hact
  rw [fixedCodim_of_binaryCover p hp] at hi
  have hfixed : fixedSpace (binaryNatural (K := F)) β.range =
      (TwoLocalCover.fixedSpace α.range).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨a,rfl⟩ := hx
      exact hv ⟨β a,⟨a,rfl⟩⟩
    · intro hv x
      obtain ⟨a,ha⟩ := x.property
      change binaryNatural x.val v=v
      rw [←ha]
      exact hv (α a) ⟨a,rfl⟩
  rw [hi]
  change 2 ^ Module.finrank (ZMod 2)
    (Vector F ⧸ fixedSpace (binaryNatural (K := F)) β.range)=_
  rw [hfixed]
  have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
    (TwoLocalCover.fixedSpace α.range)).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  rw [hc,fixed_quotient_card]



private theorem central_supplement_fixed_index {G : Type*} [Group G]
    (V C D A : Subgroup G) [Finite D] [IsMulCommutative D]
    (hVD : V ≤ D) (hCD : C ≤ D) (hgen : D=V ⊔ C)
    (hCA : C ≤ centralizer (A : Set G)) :
    (centralizer (A : Set G)).relIndex D=(centralizer (A : Set G)).relIndex V := by
  let X := D ⊓ centralizer (A : Set G)
  have hCX : C ≤ X := le_inf hCD hCA
  have hVX : V ⊔ X=D := le_antisymm (sup_le hVD inf_le_left)
    (hgen.le.trans (sup_le le_sup_left (hCX.trans le_sup_right)))
  have hXU : X ≤ normalizer (V : Set G) :=
    (inf_le_left.trans (D.le_centralizer.trans (centralizer_le hVD))).trans
      (Subgroup.centralizer_le_normalizer _)
  let : Finite X := Finite.of_injective (inclusion (show X ≤ D from inf_le_left))
    (inclusion_injective _)
  have he : X ⊓ V=V ⊓ centralizer (A : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨hVD hx.1,hx.2⟩,hx.1⟩⟩
  calc
    _ = X.relIndex D := (inf_relIndex_left _ _).symm
    _ = X.relIndex (V ⊔ X) := congrArg (X.relIndex ·) hVX.symm
    _ = X.relIndex V := relIndex_sup_of_normalizes V X hXU
    _ = _ := by rw [←inf_relIndex_right,he,inf_relIndex_left]

private theorem embedded_actor_quadratic
    {E W G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := E)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := E))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hcomm : ⁅A,U⁆ ≤ centralizer (A : Set G)) :
    ∀ x ∈ ((commutator (Sp E)).subtype.comp β).range,
      ∀ y ∈ ((commutator (Sp E)).subtype.comp β).range, ∀ v : Vector E,
        x • (y • v-v)=y • v-v := by
  rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ v
  obtain ⟨w,rfl⟩ := hp.1 v
  have hval : j (Multiplicative.ofAdd (σ (β y) w-w))=⁅y.val,j (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  have hc : x.val*⁅y.val,j (Multiplicative.ofAdd w)⁆=⁅y.val,j (Multiplicative.ofAdd w)⁆*x.val :=
    hcomm (commutator_mem_commutator y.property (hjr ▸ ⟨_,rfl⟩)) x.val x.property
  have hf : σ (β x) (σ (β y) w-w)=σ (β y) w-w := by
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hact,hval,hc,mul_inv_cancel_right]
  have hh := congrArg p hf
  rw [p.isIntertwining,map_sub,p.isIntertwining] at hh
  exact hh

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
    (hF : 2 < Nat.card E) (hcard : Nat.card ((commutator (Sp E)).subtype.comp β).range = Nat.card E)
    (hdim : Module.finrank E (displacementSpace (((commutator (Sp E)).subtype.comp β).range)) = 1)
    (hquad : ∀ x ∈ ((commutator (Sp E)).subtype.comp β).range,
      ∀ y ∈ ((commutator (Sp E)).subtype.comp β).range,
        ∀ v : Vector E, x • (y • v-v)=y • v-v) :
    let C := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
    C ≤ ⁅A,U⁆ ∧ C.relIndex ⁅A,U⁆ = Nat.card E := by
  let C := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  let α := (commutator (Sp E)).subtype.comp β
  have hC : C ≤ ⁅A,U⁆ := by
    by_contra hn
    obtain ⟨c,hc⟩ := embedded_cover_preserves_refinement_of_kernel_escape
      ⁅A,U⁆ A σ p hp j β hact (by rw [hjr]) hn
    apply no_refinement_of_displacement_one hF α.range hcard hdim hquad
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
    rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := E),hdim,pow_one]
  exact ⟨hC,hindex.trans hBcard⟩


private theorem movement_central_supplement
    {G : Type*} [Group G] (U C Y A : Subgroup G)
    (hCU : C ≤ normalizer (U : Set G)) (hCY : C ≤ centralizer (Y : Set G))
    (hAY : A ≤ Y) : ⁅A,U ⊔ C⁆=⁅A,U⁆ := by
  apply le_antisymm ?_ (commutator_mono le_rfl le_sup_left)
  apply commutator_le.mpr
  intro b hb x hx
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hx
  obtain ⟨u,hu,c,hc,rfl⟩ := hx
  have hbc : Commute b c := hCY hc b (hAY hb)
  rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbc]
  simpa only [mul_one,mul_inv_cancel_right] using commutator_mem_commutator hb hu


open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem midpoint_centralizes_radical
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t) :
    Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (hz.trans he.symm)
  rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
  exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2

private theorem plane_cover_actor_card
    {z t : Vertex d.radical}
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t) :
    Nat.card (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp
      (inclusion hA)).range=(Q d.radical z).relIndex A := by
  rw [←index_ker,←MonoidHom.comap_ker,cv.actor_kernel,comap_inclusion_subgroupOf]
  rfl

private theorem plane_cover_full_fixed_index
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t) :
    (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=
      (2^n)^Module.finrank cv.field.Carrier (displacementSpace
        (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hA)).range) := by
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z hz
  let := finite_Z d.radical z
  have he := central_supplement_fixed_index (U d.radical z) (Z d.radical t) (Z d.radical z) A
    (U_le_Z z) (Sp4Four.edge_Z_le_endpoint d.radical hz hzt)
    (Z_eq_moving_sup_edge_of_distance_two h d g hb hz hzt)
    ((midpoint_centralizes_radical d hz hzt).trans (centralizer_le hA))
  have hm := cover_moving_index (MovedSection.coverAction (replacementMovedSection h d) cv.equiv)
    (MovedSection.coverProjection (replacementMovedSection h d) cv.equiv) cv.cover (U d.radical z) A
    cv.embedding cv.injective cv.range_eq (cv.actor.comp (inclusion hA))
    (fun x w => cv.actor_conjugation (inclusion hA x) w)
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  exact he.trans (hm.trans (congrArg (·^_) hFc))

private theorem plane_cover_hyperplane_actor_bound
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t)
    (hi : (Z d.radical z ⊓ centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z)=2^n) : (Q d.radical z).relIndex A ≤ 2^n := by
  let α := ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hA)
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have hd : Module.finrank cv.field.Carrier (displacementSpace α.range)=1 := by
    have hh := plane_cover_full_fixed_index h d g hb hz hzt cv A hA
    have hi' : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n :=
      (inf_relIndex_left _ _).symm.trans hi
    exact Nat.pow_right_injective hq (hh.symm.trans (hi'.trans (pow_one _).symm))
  have hh := card_actor_le_displacement_dimension α.range
  rw [plane_cover_actor_card h d cv A hA,hd,one_pow,pow_one,cv.field.card_eq,cv.degree] at hh
  exact hh

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem inf_eq_of_index_bound {G : Type*} [Group G]
    (C V Q : Subgroup G) [Finite V] (hCV : C ≤ V) (hCQ : C ≤ Q)
    (hi : C.relIndex V ≤ Q.relIndex V) : V ⊓ Q=C := by
  have hCI : C ≤ V ⊓ Q := le_inf hCV hCQ
  have hm := relIndex_mul_relIndex C (V ⊓ Q) V hCI inf_le_left
  rw [inf_relIndex_left] at hm
  have hp : 0 < Q.relIndex V := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hc : C.relIndex (V ⊓ Q)=1 := by
    have hn : 0 < C.relIndex (V ⊓ Q) := Nat.pos_of_ne_zero
      (mt (relIndex_eq_zero_of_le_right (show V ⊓ Q ≤ V from inf_le_left)) index_ne_zero_of_finite)
    nlinarith
  exact le_antisymm (relIndex_eq_one.mp hc) hCI

/-- In the large-image branch the full midpoint is the kernel of both
critical actions, and both images have order q squared. -/
theorem source_four_large_midpoint_kernels
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    Z d.radical a ⊓ Q d.radical z=Z d.radical t ∧
      Z d.radical z ⊓ Q d.radical a=Z d.radical t ∧
      (Q d.radical z).relIndex (Z d.radical a)=(2^n)^2 ∧
      (Q d.radical a).relIndex (Z d.radical z)=(2^n)^2 := by
  obtain ⟨_,_,hai,hzi,_⟩ := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hta := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  have htz := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  have haQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hzQ : Z d.radical z ≤ Q d.radical z :=
    (g.omega_bound z path.end_color (by rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hreverse : (2^n)^2 ≤ (Q d.radical a).relIndex (Z d.radical z) := by
    by_contra hn
    have hh := (replacement_critical_indices_eq_field_of_small h d rev (by omega)
      (lt_of_not_ge hn)).2
    rw [hh] at hcritical
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith only [hq,hcritical]
  let := finite_Z d.radical a
  let := finite_Z d.radical z
  have hae := inf_eq_of_index_bound (Z d.radical t) (Z d.radical a) (Q d.radical z)
    hta (htz.trans hzQ) (hai.trans_le hcritical)
  have hze := inf_eq_of_index_bound (Z d.radical t) (Z d.radical z) (Q d.radical a)
    htz (hta.trans haQ) (hzi.trans_le hreverse)
  refine ⟨hae,hze,?_,?_⟩
  · rw [←inf_relIndex_left,hae,hai]
  · rw [←inf_relIndex_left,hze,hzi]

/-- The escaping opposite centralizer in the large-image hyperplane
argument has exactly field order modulo its kernel, and fills the entire
hyperplane fixer modulo the full endpoint core. -/
theorem source_four_large_escaping_hyperplane
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical))
    (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    let Y := Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))
    Y.relIndex (Z d.radical a)=2^n ∧ (Q d.radical z).relIndex Y=2^n ∧
      P=Q d.radical z ⊔ Y ∧ ⁅Z d.radical z,P⁆=⁅Z d.radical z,Y⁆ := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y := Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))
  let C := Z d.radical t
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  obtain ⟨⟨ca⟩,⟨cz⟩,hai,hzi,_⟩ := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  obtain ⟨hak,hzk,_,_⟩ := source_four_large_midpoint_kernels h d g hb hsat path hat hzt c c' hcritical
  have hta : C ≤ Z d.radical a := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  have htz : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  have haQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hzQ : Z d.radical z ≤ Q d.radical z :=
    (g.omega_bound z path.end_color (by rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    midpoint_centralizes_radical d path.end_color hzt
  have hCX : C ≤ X := le_inf htz (hCT.trans (centralizer_le hP))
  have hCY : C ≤ Y := le_inf hta (hCT.trans (centralizer_le
    (inf_le_left.trans (hzQ.trans c'.core_le_edge))))
  have hXT : X ≤ Q d.radical t := inf_le_left.trans (hzQ.trans c'.core_le_edge)
  have hYT : Y ≤ Q d.radical t := inf_le_left.trans (haQ.trans c.core_le_edge)
  let := finite_Z d.radical a
  let := finite_Z d.radical z
  let : Finite X := Finite.of_injective (inclusion (show X ≤ Z d.radical z from inf_le_left)) (inclusion_injective _)
  let : Finite Y := Finite.of_injective (inclusion (show Y ≤ Z d.radical a from inf_le_left)) (inclusion_injective _)
  have hXi : C.relIndex X=2^n := by
    have hm := relIndex_mul_relIndex C X (Z d.radical z) hCX inf_le_left
    rw [hi,hzi] at hm
    nlinarith only [hm,hq]
  have hXker : X ⊓ Q d.radical a=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show X ≤ Z d.radical z from inf_le_left)).trans_eq hzk
    · exact le_inf hCX (hta.trans haQ)
  have hYker : Y ⊓ Q d.radical z=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show Y ≤ Z d.radical a from inf_le_left)).trans_eq hak
    · exact le_inf hCY (htz.trans hzQ)
  let αX := ((commutator (Sp ca.field.Carrier)).subtype.comp ca.actor).comp (inclusion hXT)
  have hXcard : Nat.card αX.range=2^n := by
    rw [plane_cover_actor_card h d ca X hXT,←inf_relIndex_left,hXker,hXi]
  let r := Module.finrank ca.field.Carrier (displacementSpace αX.range)
  have hr : Y.relIndex (Z d.radical a)=(2^n)^r := by
    rw [inf_relIndex_left]
    exact plane_cover_full_fixed_index h d g hb path.start_color hat ca X hXT
  have hr0 : r ≠ 0 := by
    intro he
    have hh := card_actor_le_displacement_dimension αX.range
    rw [hXcard,show Module.finrank ca.field.Carrier (displacementSpace αX.range)=0 from he] at hh
    simp only [zero_pow (by decide : (2:ℕ) ≠ 0),pow_zero] at hh
    omega
  have hCYn : C.relIndex Y ≠ 1 := by
    intro he
    exact hescape ((relIndex_eq_one.mp he).trans (htz.trans hzQ))
  have hCYpos : 0 < C.relIndex Y := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hr1 : r=1 := by
    by_contra hn
    have hr2 : 2 ≤ r := by omega
    have hbnd := Nat.pow_le_pow_right (by omega : 0 < 2^n) hr2
    have hm := relIndex_mul_relIndex C Y (Z d.radical a) hCY inf_le_left
    rw [hai,hr] at hm
    have hk : 2 ≤ C.relIndex Y := by omega
    nlinarith only [hm,hbnd,hk,hq]
  have hYindex : Y.relIndex (Z d.radical a)=2^n := by rw [hr,hr1,pow_one]
  have hYq : (Q d.radical z).relIndex Y=2^n := by
    rw [←inf_relIndex_left,hYker]
    have hm := relIndex_mul_relIndex C Y (Z d.radical a) hCY inf_le_left
    rw [hai,hYindex] at hm
    nlinarith only [hm,hq]
  have hYP : Y ≤ P := by rw [hpoint]; exact le_inf hYT inf_le_right
  have hQP : Q d.radical z ≤ P := by
    rw [hpoint]
    exact le_inf c'.core_le_edge (le_centralizer_iff.mp (inf_le_left.trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical z path.end_color))))
  have hPcard := plane_cover_hyperplane_actor_bound h d g hb path.end_color hzt cz P hP hi
  have hQPnorm : Y ≤ normalizer (Q d.radical z : Set (FreeAmalgam d.radical)) :=
    (hYT.trans c'.edge_le).trans (Q_normalized d.radical z)
  have hjoin : P=Q d.radical z ⊔ Y := by
    have hJP : Q d.radical z ⊔ Y ≤ P := sup_le hQP hYP
    have hm := relIndex_mul_relIndex (Q d.radical z) (Q d.radical z ⊔ Y) P le_sup_left hJP
    have hj : (Q d.radical z).relIndex (Q d.radical z ⊔ Y)=(Q d.radical z).relIndex Y := by
      let J := Q d.radical z ⊔ Y
      let : ((Q d.radical z).subgroupOf J).Normal :=
        normal_subgroupOf_of_le_normalizer (sup_le (Q d.radical z).le_normalizer hQPnorm)
      have hh := relIndex_sup_left (Y.subgroupOf J) ((Q d.radical z).subgroupOf J)
      rw [←subgroupOf_sup (show Q d.radical z ≤ J from le_sup_left) (show Y ≤ J from le_sup_right),
        relIndex_subgroupOf (show J ≤ J from le_rfl),relIndex_subgroupOf (show Y ≤ J from le_sup_right)] at hh
      exact hh
    rw [hj,hYq] at hm
    have hn : 0 < (Q d.radical z ⊔ Y).relIndex P := Nat.pos_of_ne_zero
      (mt (relIndex_eq_zero_of_le_left (show Q d.radical z ≤ Q d.radical z ⊔ Y from le_sup_left))
        (by
          have hh := plane_cover_actor_card h d cz P hP
          exact hh ▸ (Nat.ne_of_gt Nat.card_pos)))
    have he : (Q d.radical z ⊔ Y).relIndex P=1 := by nlinarith only [hm,hPcard,hn,hq]
    exact le_antisymm (relIndex_eq_one.mp he) hJP
  refine ⟨hYindex,hYq,hjoin,?_⟩
  apply le_antisymm ?_ (commutator_mono le_rfl hYP)
  apply commutator_le_moving_of_inner_mod_centralizer (Z d.radical z) Y P
    ((hYT.trans c'.edge_le).trans (Z_normalized d.radical z))
  rw [hjoin,sup_comm]
  exact sup_le_sup_left (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical z path.end_color))) _

/-- In the escaping-centralizer branch the hyperplane moves the opposite
full cover in a root preimage, including the entire opposite attachment. -/
theorem source_four_large_escaping_movement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical))
    (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    A ≤ ⁅X,Z d.radical a⁆ ∧ A.relIndex ⁅X,Z d.radical a⁆=2^n ∧
      Nat.card (⁅X,Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical))=2^n * Nat.card A := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y := Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))
  let C := Z d.radical t
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  obtain ⟨⟨ca⟩,_,hai,hzi,hmoveA,_,_⟩ := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  obtain ⟨hak,hzk,_,_⟩ := source_four_large_midpoint_kernels h d g hb hsat path hat hzt c c' hcritical
  have hta : C ≤ Z d.radical a := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  have htz : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  have haQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hzQ : Z d.radical z ≤ Q d.radical z :=
    (g.omega_bound z path.end_color (by rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    midpoint_centralizes_radical d path.end_color hzt
  have hCX : C ≤ X := le_inf htz (hCT.trans (centralizer_le hP))
  have hCY : C ≤ Y := le_inf hta (hCT.trans (centralizer_le
    (inf_le_left.trans (hzQ.trans c'.core_le_edge))))
  have hXT : X ≤ Q d.radical t := inf_le_left.trans (hzQ.trans c'.core_le_edge)
  have hYT : Y ≤ Q d.radical t := inf_le_left.trans (haQ.trans c.core_le_edge)
  let := finite_Z d.radical a
  let := finite_Z d.radical z
  let : Finite X := Finite.of_injective (inclusion (show X ≤ Z d.radical z from inf_le_left)) (inclusion_injective _)
  let : Finite Y := Finite.of_injective (inclusion (show Y ≤ Z d.radical a from inf_le_left)) (inclusion_injective _)
  have hXi : C.relIndex X=2^n := by
    have hm := relIndex_mul_relIndex C X (Z d.radical z) hCX inf_le_left
    rw [hi,hzi] at hm
    nlinarith only [hm,hq]
  have hXker : X ⊓ Q d.radical a=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show X ≤ Z d.radical z from inf_le_left)).trans_eq hzk
    · exact le_inf hCX (hta.trans haQ)
  have hYker : Y ⊓ Q d.radical z=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show Y ≤ Z d.radical a from inf_le_left)).trans_eq hak
    · exact le_inf hCY (htz.trans hzQ)
  let αX := ((commutator (Sp ca.field.Carrier)).subtype.comp ca.actor).comp (inclusion hXT)
  have hXcard : Nat.card αX.range=2^n := by
    rw [plane_cover_actor_card h d ca X hXT,←inf_relIndex_left,hXker,hXi]
  let r := Module.finrank ca.field.Carrier (displacementSpace αX.range)
  have hr : Y.relIndex (Z d.radical a)=(2^n)^r := by
    rw [inf_relIndex_left]
    exact plane_cover_full_fixed_index h d g hb path.start_color hat ca X hXT
  have hYindex := (source_four_large_escaping_hyperplane h d g hb hsat path hat hzt c c'
    hcritical P hP hpoint hi hescape).1
  have hr1 : r=1 := Nat.pow_right_injective hq
    (hr.symm.trans (hYindex.trans (pow_one _).symm))
  have hFa : Nat.card ca.field.Carrier=2^n := ca.field.card_eq.trans (congrArg (2^·) ca.degree)
  have hlarge : 2 < Nat.card ca.field.Carrier := by
    rw [hFa]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  let s := replacementMovedSection h d
  let p := MovedSection.coverProjection s ca.equiv
  let σ := MovedSection.coverAction s ca.equiv
  let β := ca.actor.comp (inclusion hXT)
  have hβact (x : X) (w : s.space.toSubmodule) :
      ca.embedding (Multiplicative.ofAdd (σ (β x) w))=
        x.val*ca.embedding (Multiplicative.ofAdd w)*x.val⁻¹ := ca.actor_conjugation (inclusion hXT x) w
  have hR : ⁅Z d.radical a,Z d.radical z⁆ ≤ C := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl haQ).trans
      (source_two_midpoint_containment h d g hb hsat path hat hzt c c')
  have hcomm : ⁅X,U d.radical a⁆ ≤ centralizer (X : Set (FreeAmalgam d.radical)) := by
    rw [commutator_comm]
    exact ((commutator_mono (U_le_Z a) hXT).trans_eq hmoveA).trans
      (hR.trans (hCT.trans (centralizer_le hXT)))
  have hquad := embedded_actor_quadratic p ca.cover (U d.radical a) X
    ca.embedding ca.injective ca.range_eq β hβact hcomm
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map ca.embedding=
      U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨ca.range_eq ▸ ⟨w,rfl⟩,(ca.kernel _).mp hw⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨w,rfl⟩ := ca.range_eq.symm ▸ hx
      exact ⟨w,(ca.kernel _).mpr hc,rfl⟩
  obtain ⟨hkerle,hkerindex⟩ := embedded_root_displacement_index
    (U d.radical a) X ((hXT.trans c.edge_le).trans (U_normalized a))
    σ p ca.cover ca.embedding ca.injective ca.range_eq β hβact hlarge (hXcard.trans hFa.symm) hr1 hquad
  change p.toLinearMap.ker.toAddSubgroup.toSubgroup.map ca.embedding ≤ ⁅X,U d.radical a⁆ at hkerle
  change (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map ca.embedding).relIndex ⁅X,U d.radical a⁆=Nat.card ca.field.Carrier at hkerindex
  rw [hk] at hkerle hkerindex
  rw [hFa] at hkerindex
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hCU : C ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hta.trans ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hmove : ⁅X,Z d.radical a⁆=⁅X,U d.radical a⁆ := by
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat]
    exact movement_central_supplement (U d.radical a) C (Q d.radical t) X hCU hCT hXT
  rw [←hmove] at hkerle hkerindex
  have hcard : Nat.card (⁅X,Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical))=
      2^n * Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical))
      (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
      ⁅X,Z d.radical a⁆ bot_le hkerle
    simpa only [relIndex_bot_left,hkerindex,mul_comm] using hh.symm
  exact ⟨hkerle,hkerindex,hcard⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
