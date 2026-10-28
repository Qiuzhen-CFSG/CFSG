module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourFixedKernels

/-!
# Comparing the attachments of an escaping hyperplane

In the large critical-image branch, the two full fixed attachments have
the same order: both are images of the kernel of the original moved-section
projection. If the opposite hyperplane centralizer escapes, its movement
has order q times that common order. Containment in the first hyperplane
movement would put it in the field-sized section-centralizer movement,
forcing both attachments trivial. Unequal attachments exclude containment.

The natural image of movement on a field-subspace preimage is a field
subspace: it is the sum of the images of the restricted displacement maps.
Thus its index over the full binary attachment is a power of q. Below
field order, this forces the first attachment into the opposite movement.
The actual opposite hyperplane action is a full long root, so every moved
element outside its smaller kernel is one individual commutator. Such a
commutator cannot be a nonidentity member of the first attachment; hence
the two complete attachments agree. No field structure is imposed on the
binary covering kernel.

Apply these calculations to the actual hyperplane and section centralizer
constructed in SourceFourHyperplane. If the attachments differ and the
opposite centralizer escapes, both attachments must have full field order.
The full-size escape comparison, the nonescaping branch of source (4),
source (5)/(6) and the terminal field restriction remain necessary.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(4), printed p.875. Private cover transports reuse the checked
SourceFourEscape calculations. The final theorem is applied with the literal
Chapter11 intrinsic MS input in SaturatedMSRecognition.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour

private theorem embedded_subspace_movement_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : Function.Surjective p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (U Y X : Subgroup G) (hjr : j.range=U) (hYU : Y ≤ normalizer (U : Set G))
    (hXU : X ≤ U) (V : Submodule F (Vector F)) (β : Y →* L (K := F))
    (hact : ∀ y : Y, ∀ w : W, j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hX : ∀ w : W, j (Multiplicative.ofAdd w) ∈ X ↔ p w ∈ V) :
    ∃ r : ℕ, (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j).relIndex ⁅Y,X⁆ =
      Nat.card F^r := by
  let K := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  let α := (commutator (Sp F)).subtype.comp β
  let D : Submodule F (Vector F) := ⨆ y : Y, V.map (symplecticNatural 2 (α y)-LinearMap.id)
  let B := D.toAddSubgroup.toSubgroup
  obtain ⟨π,hπ⟩ := exists_embedded_projection U j hj hjr p.toLinearMap
  have hk : π.ker.map U.subtype=K := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      obtain ⟨w,hw⟩ := (hjr.symm ▸ u.property : u.val ∈ j.range)
      have he : u=⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
      refine ⟨w,?_,hw⟩
      have hh : π u=1 := hu
      rw [he] at hh
      exact congrArg Multiplicative.toAdd ((hπ w.toAdd).symm.trans hh)
    · rintro x ⟨w,hw,rfl⟩
      refine ⟨⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩,?_,rfl⟩
      change π ⟨j w,_⟩=1
      exact (hπ w.toAdd).trans (congrArg Multiplicative.ofAdd hw)
  have hMU : ⁅Y,X⁆ ≤ U := (commutator_mono le_rfl hXU).trans
    (le_normalizer_iff_commutator_le_right.mp hYU)
  let P := (B.comap π).map U.subtype
  have hMP : ⁅Y,X⁆ ≤ P := by
    apply commutator_le.mpr
    intro y hy x hx
    obtain ⟨w,rfl⟩ := (hjr.symm ▸ hXU hx : x ∈ j.range)
    let v := σ (β ⟨y,hy⟩) w.toAdd-w.toAdd
    refine ⟨⟨j (Multiplicative.ofAdd v),by rw [←hjr]; exact ⟨_,rfl⟩⟩,?_,?_⟩
    · change (π ⟨j (Multiplicative.ofAdd v),_⟩).toAdd ∈ D
      rw [hπ]
      change p v ∈ D
      dsimp only [v]
      rw [map_sub,p.isIntertwining]
      exact (le_iSup (fun y : Y => V.map (symplecticNatural 2 (α y)-LinearMap.id)) ⟨y,hy⟩)
        ⟨p w.toAdd,(hX w.toAdd).mp hx,rfl⟩
    · change j (Multiplicative.ofAdd (σ (β ⟨y,hy⟩) w.toAdd-w.toAdd))=⁅y,j w⁆
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
  have hlift (v : Vector F) (hv : v ∈ D) :
      ∃ w : W, p w=v ∧ j (Multiplicative.ofAdd w) ∈ ⁅Y,X⁆ := by
    refine Submodule.iSup_induction _
      (motive := fun v => ∃ w : W, p w=v ∧ j (Multiplicative.ofAdd w) ∈ ⁅Y,X⁆) hv ?_ ?_ ?_
    · intro y v hv
      obtain ⟨v,hv,rfl⟩ := hv
      obtain ⟨w,rfl⟩ := hp v
      refine ⟨σ (β y) w-w,?_,?_⟩
      · rw [map_sub,p.isIntertwining]
        rfl
      · rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
        exact commutator_mem_commutator y.property ((hX w).mpr hv)
    · exact ⟨0,map_zero _,by simp⟩
    · rintro u v ⟨w,hw,hm⟩ ⟨w',hw',hm'⟩
      refine ⟨w+w',by rw [map_add,hw,hw'],?_⟩
      simpa only [ofAdd_add,map_mul] using (⁅Y,X⁆).mul_mem hm hm'
  have him : (⁅Y,X⁆.subgroupOf U).map π=B := by
    apply le_antisymm
    · rintro v ⟨u,hu,rfl⟩
      obtain ⟨w,hw,he⟩ := hMP hu
      have he' : w=u := Subtype.ext he
      exact he' ▸ hw
    · intro v hv
      obtain ⟨w,hw,hm⟩ := hlift v.toAdd hv
      refine ⟨⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩,hm,?_⟩
      exact (hπ w).trans (congrArg Multiplicative.ofAdd hw)
  have hi : K.relIndex ⁅Y,X⁆=Nat.card B := by
    rw [←him,←relIndex_ker]
    have he := relIndex_subgroupOf (H := K) hMU
    rw [←hk,subgroupOf_map_subtype_eq] at he
    rw [hk] at he
    exact he.symm
  refine ⟨Module.finrank F D,hi.trans ?_⟩
  let e : B ≃ D :=
    { toFun := fun x => ⟨x.val.toAdd,x.property⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := F)]

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

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem plane_cover_value
    {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {C₀ : Subgroup J}
    {T : Subgroup M} {s : MovedSection ρ C₀} {n : ℕ} {a t : Vertex T}
    [FiniteDimensional (ZMod 2) s.space.toSubmodule]
    (ca : RadicalPlaneCover T s n a t)
    (X : Subgroup (FreeAmalgam T)) (hXT : X ≤ Q T t)
    (hXcard : Nat.card (((commutator (Sp ca.field.Carrier)).subtype.comp ca.actor).comp
      (inclusion hXT)).range=2^n)
    (hr1 : Module.finrank ca.field.Carrier (displacementSpace
      (((commutator (Sp ca.field.Carrier)).subtype.comp ca.actor).comp (inclusion hXT)).range)=1)
    (hcomm : ⁅X,U T a⁆ ≤ centralizer (X : Set (FreeAmalgam T)))
    (hlarge₀ : 2 < 2^n)
    (hsmall : Nat.card (U T a ⊓ centralizer (Ltilde T a : Set (FreeAmalgam T)) :
      Subgroup (FreeAmalgam T)) ≠ 2^n)
    (x : FreeAmalgam T) (hx : x ∈ ⁅X,U T a⁆)
    (hn : x ∉ U T a ⊓ centralizer (Ltilde T a : Set (FreeAmalgam T))) :
    ∃ b ∈ X, ∃ u ∈ U T a, ⁅b,u⁆=x := by
  have hFa : Nat.card ca.field.Carrier=2^n := ca.field.card_eq.trans (congrArg (2^·) ca.degree)
  have hlarge : 2 < Nat.card ca.field.Carrier := by
    rw [hFa]
    exact hlarge₀
  let p := MovedSection.coverProjection s ca.equiv
  let σ := MovedSection.coverAction s ca.equiv
  let β := ca.actor.comp (inclusion hXT)
  have hβact (x : X) (w : s.space.toSubmodule) :
      ca.embedding (Multiplicative.ofAdd (σ (β x) w))=
        x.val*ca.embedding (Multiplicative.ofAdd w)*x.val⁻¹ := ca.actor_conjugation (inclusion hXT x) w
  have hquad := embedded_actor_quadratic p ca.cover (U T a) X
    ca.embedding ca.injective ca.range_eq β hβact hcomm
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map ca.embedding=
      U T a ⊓ centralizer (Ltilde T a : Set (FreeAmalgam T)) := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨ca.range_eq ▸ ⟨w,rfl⟩,(ca.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := ca.range_eq.symm ▸ hv
      exact ⟨w,(ca.kernel _).mpr hc,rfl⟩
  have hsmall' : Nat.card p.toLinearMap.ker ≠ Nat.card ca.field.Carrier := by
    rw [←embedded_cover_kernel_card p ca.embedding ca.injective,hk,hFa]
    exact hsmall
  have hc : Nat.card β.range=Nat.card ca.field.Carrier := by
    have hh := hXcard
    change Nat.card (((commutator (Sp ca.field.Carrier)).subtype.comp β).range)=2^n at hh
    rw [MonoidHom.range_comp,card_map_of_injective Subtype.val_injective] at hh
    exact hh.trans hFa.symm
  have hd : Module.finrank ca.field.Carrier
      (displacementSpace (β.range.map (commutator (Sp ca.field.Carrier)).subtype))=1 := by
    change Module.finrank ca.field.Carrier
      (displacementSpace (((commutator (Sp ca.field.Carrier)).subtype.comp β).range))=1 at hr1
    rw [←MonoidHom.range_comp]
    exact hr1
  have hq' : ∀ b ∈ β.range.map (commutator (Sp ca.field.Carrier)).subtype,
      ∀ b' ∈ β.range.map (commutator (Sp ca.field.Carrier)).subtype,
        ∀ v : Vector ca.field.Carrier, b • (b' • v-v)=b' • v-v := by
    rw [←MonoidHom.range_comp]
    exact hquad
  exact embedded_root_value_of_kernel_card_ne hlarge (U T a) X p ca.cover
    ca.embedding ca.range_eq β hβact hc hd hq' hsmall' x hx (by rwa [hk])
/-- Below the maximal covering-kernel order, every element of the escaping
hyperplane movement outside that kernel is an individual commutator of the
actual hyperplane and the opposite original moving module. -/
theorem source_four_large_escaping_value
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
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z)
    (hsmall : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical)) ≠ 2^n)
    (x : FreeAmalgam d.radical)
    (hx : x ∈ ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆)
    (hn : x ∉ U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ b ∈ Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),
      ∃ u ∈ U d.radical a, ⁅b,u⁆=x := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y := Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))
  let C := Z d.radical t
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have geom := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  let ca := Classical.choice geom.1
  have hzi := geom.2.2.2.1
  have hmoveA := geom.2.2.2.2.1
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
  have hXT : X ≤ Q d.radical t := inf_le_left.trans (hzQ.trans c'.core_le_edge)
  let := finite_Z d.radical a
  let := finite_Z d.radical z
  let : Finite X := Finite.of_injective (inclusion (show X ≤ Z d.radical z from inf_le_left)) (inclusion_injective _)
  have hXi : C.relIndex X=2^n := by
    have hm := relIndex_mul_relIndex C X (Z d.radical z) hCX inf_le_left
    rw [hi,hzi] at hm
    nlinarith only [hm,hq]
  have hXker : X ⊓ Q d.radical a=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show X ≤ Z d.radical z from inf_le_left)).trans_eq hzk
    · exact le_inf hCX (hta.trans haQ)
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
  have hR : ⁅Z d.radical a,Z d.radical z⁆ ≤ C := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl haQ).trans
      (source_two_midpoint_containment h d g hb hsat path hat hzt c c')
  have hcomm : ⁅X,U d.radical a⁆ ≤ centralizer (X : Set (FreeAmalgam d.radical)) := by
    rw [commutator_comm]
    exact ((commutator_mono (U_le_Z a) hXT).trans_eq hmoveA).trans
      (hR.trans (hCT.trans (centralizer_le hXT)))
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hCU : C ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hta.trans ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hmove : ⁅X,Z d.radical a⁆=⁅X,U d.radical a⁆ := by
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat]
    exact movement_central_supplement (U d.radical a) C (Q d.radical t) X hCU hCT hXT
  exact plane_cover_value ca X hXT hXcard hr1 hcomm
    (Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary) hsmall x (hmove ▸ hx) hn

/-- An individual commutator of the two full Z-layers cannot be a nonidentity
member of either endpoint's complete fixed attachment. The midpoint supplement
is retained and centralizes the other full Z-layer. -/
theorem critical_full_value_in_fixed_eq_one
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical=2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (b : FreeAmalgam d.radical) (hbZ : b ∈ Z d.radical z)
    (u : FreeAmalgam d.radical) (hu : u ∈ Z d.radical a)
    (hfix : ⁅b,u⁆ ∈ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) :
    ⁅b,u⁆=1 := by
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hta := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  have htz := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  have hn : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hta.trans ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat,
    ←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hn] at hu
  obtain ⟨v,hv,w,hw,rfl⟩ := hu
  have hbw : Commute b w := (Z d.radical z).le_centralizer (htz hw) b hbZ
  have he : ⁅b,v*w⁆=⁅b,v⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbw]
    simp only [mul_one,mul_inv_cancel_right]
  rw [he] at hfix ⊢
  exact critical_value_in_fixed_eq_one h d path hb hat b hbZ v hv hfix

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem plane_attachment_card
    {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {C : Subgroup J}
    {T : Subgroup M} {s : MovedSection ρ C} {n : ℕ} {a t : Vertex T}
    (cv : RadicalPlaneCover T s n a t) :
    Nat.card (U T a ⊓ centralizer (Ltilde T a : Set (FreeAmalgam T)) :
      Subgroup (FreeAmalgam T)) = Nat.card s.central.toSubmodule := by
  let p := MovedSection.coverProjection s cv.equiv
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding =
      U T a ⊓ centralizer (Ltilde T a : Set (FreeAmalgam T)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  rw [←hk,embedded_cover_kernel_card p cv.embedding cv.injective]
  have he : p.toLinearMap.ker=s.central.toSubmodule := by
    ext w
    change cv.equiv.linearEquiv (s.central.toSubmodule.mkQ w)=0 ↔ w ∈ s.central.toSubmodule
    rw [LinearEquiv.map_eq_zero_iff,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  rw [he]

/-- In the large branch the full attachments have equal orders, because
both are images of the kernel of the original moved-section quotient. -/
theorem source_four_large_attachment_card_eq
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical)) =
    Nat.card (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical)) := by
  have geom := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  exact (plane_attachment_card (Classical.choice geom.1)).trans
    (plane_attachment_card (Classical.choice geom.2.1)).symm

/-- If the opposite hyperplane centralizer escapes, containment of its
movement in the first hyperplane movement would force both full attachments
trivial. Thus unequal attachments exclude that containment, as on p.875. -/
theorem source_four_large_escaping_not_le_hyperplane
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P B : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hB : ∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧
      ∀ x ∈ Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)), ⁅b,x⁆ ∈ ⁅Z d.radical z,P⁆)
    (hcard : Nat.card (⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆ :
      Subgroup (FreeAmalgam d.radical))=2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z) :
    ¬ ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ≤
      ⁅Z d.radical z,P⁆ := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let M := ⁅X,Z d.radical a⁆
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  intro hle
  have hZaT : Z d.radical a ≤ Q d.radical t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c.core_le_edge)
  have hZaB : Z d.radical a ≤ B := by
    intro b hbZ
    refine (hB b).mpr ⟨hZaT hbZ,fun x hx => ?_⟩
    apply hle
    rw [commutator_comm X]
    exact commutator_mem_commutator hbZ hx
  have hMD : M ≤ ⁅X,B⁆ := commutator_mono le_rfl hZaB
  let : Finite (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hMc := Nat.card_le_card_of_injective (inclusion hMD) (inclusion_injective _)
  rw [hcard] at hMc
  have hcm := (source_four_large_escaping_movement h d g hb hsat path hat hzt c c'
    hcritical P hP hpoint hi hescape).2.2
  have hAc : Nat.card A ≤ 1 := by
    change Nat.card M=2^n*Nat.card A at hcm
    have hq : 0 < 2^n := by positivity
    nlinarith only [hMc,hcm,hq]
  let := finite_Z d.radical a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  have hA : A=⊥ := A.eq_bot_of_card_le hAc
  have hc := source_four_large_attachment_card_eq h d g hb hsat path hat hzt c c' hcritical
  change Nat.card A=Nat.card A' at hc
  have hA' : A'=⊥ := Subgroup.card_eq_one.mp (hc.symm.trans (hA ▸ Subgroup.card_bot))
  exact hne (hA.trans hA'.symm)

/-- Below full field order, the intersection of the escaping root movement
with the opposite attachment is exactly the intersection of the two attachments.
This is the individual-commutator comparison in source (4), before the remaining
geometric containment of that attachment has been established. -/
theorem source_four_large_escaping_attachment_intersection
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z)
    (hsmall : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical)) ≠ 2^n) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    ⁅X,Z d.radical a⁆ ⊓ A'=A ⊓ A' := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  apply le_antisymm
  · rintro x ⟨hx,hxA'⟩
    refine ⟨?_,hxA'⟩
    by_contra hn
    obtain ⟨b,hbX,u,hu,he⟩ := source_four_large_escaping_value h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape hsmall x hx hn
    have hc : ⁅u,b⁆ ∈ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
      rw [←commutatorElement_inv,he]
      exact inv_mem hxA'.2
    have he1 := critical_full_value_in_fixed_eq_one h d rev hb hzt hat
      u (U_le_Z a hu) b hbX.1 hc
    have he2 : ⁅b,u⁆=1 := commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp he1).symm
    exact hn (he.symm ▸ he2.symm ▸ A.one_mem)
  · exact inf_le_inf_right _
      (source_four_large_escaping_movement h d g hb hsat path hat hzt c c'
        hcritical P hP hpoint hi hescape).1

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem plane_cover_fixed_movement_index
    {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {C₀ : Subgroup J}
    {T : Subgroup M} {s : MovedSection ρ C₀} {n : ℕ} {z t : Vertex T}
    [FiniteDimensional (ZMod 2) s.space.toSubmodule]
    (cv : RadicalPlaneCover T s n z t)
    (Y P : Subgroup (FreeAmalgam T)) (hY : Y ≤ Q T t) (hP : P ≤ Q T t) :
    ∃ r : ℕ, (U T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T))).relIndex
      ⁅Y,U T z ⊓ centralizer (P : Set (FreeAmalgam T))⁆ = (2^n)^r := by
  let p := MovedSection.coverProjection s cv.equiv
  let σ := MovedSection.coverAction s cv.equiv
  let β := cv.actor.comp (inclusion hY)
  let γ := cv.actor.comp (inclusion hP)
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp γ
  have hγact (a : P) (w : s.space.toSubmodule) :
      cv.embedding (Multiplicative.ofAdd (σ (γ a) w))=
        a.val*cv.embedding (Multiplicative.ofAdd w)*a.val⁻¹ := cv.actor_conjugation (inclusion hP a) w
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T)) := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  have hf (w : s.space.toSubmodule) :
      cv.embedding (Multiplicative.ofAdd w) ∈ U T z ⊓ centralizer (P : Set (FreeAmalgam T)) ↔
        p w ∈ TwoLocalCover.fixedSpace α.range := by
    constructor
    · intro hw a ha
      obtain ⟨a,rfl⟩ := ha
      have he : σ (γ a) w=w := by
        apply Multiplicative.ofAdd.injective
        apply cv.injective
        rw [hγact,hw.2 a.val a.property,mul_inv_cancel_right]
      exact (LinearMap.congr_fun (p.isIntertwining' (γ a)) w).symm.trans (congrArg p he)
    · intro hw
      refine ⟨cv.range_eq ▸ ⟨_,rfl⟩,fun a ha => ?_⟩
      have he := cover_fixed_of_projection_fixed p cv.cover (γ ⟨a,ha⟩) w
        (hw (α ⟨a,ha⟩) ⟨_,rfl⟩)
      have he' := congrArg (fun v => cv.embedding (Multiplicative.ofAdd v)) he
      change cv.embedding (Multiplicative.ofAdd (σ (γ ⟨a,ha⟩) w))=_ at he'
      rw [hγact,mul_inv_eq_iff_eq_mul] at he'
      exact he'
  obtain ⟨r,hr⟩ := embedded_subspace_movement_index p cv.cover.1 cv.embedding cv.injective
    (U T z) Y (U T z ⊓ centralizer (P : Set (FreeAmalgam T))) cv.range_eq
    ((hY.trans cv.edge_le).trans (U_normalized z)) inf_le_left
    (TwoLocalCover.fixedSpace α.range) β (fun y w => cv.actor_conjugation (inclusion hY y) w) hf
  rw [hk,cv.field.card_eq,cv.degree] at hr
  exact ⟨r,hr⟩

/-- The movement of a full fixed hyperplane has field-power index over
its intersection with the entire attachment. This retains the binary cover
kernel and uses the actual common-radical actions at the first endpoint. -/
theorem source_four_large_hyperplane_movement_index
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t) :
    ∃ r : ℕ, (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))).relIndex
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ = (2^n)^r := by
  have geom := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  let cv := Classical.choice geom.2.1
  let C := Z d.radical t
  let X₀ := U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  have hZaT : Z d.radical a ≤ Q d.radical t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c.core_le_edge)
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    midpoint_centralizes_radical d path.end_color hzt
  have hCZ : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hCU : C ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le
      (inf_le_left.trans (U_le_Z z))))).trans (Subgroup.centralizer_le_normalizer _)
  have hX : Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))=X₀ ⊔ C := by
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt,
      sup_comm (U d.radical z),inf_centralizer_sup_of_centralizing C (U d.radical z) P
        hCU (hCT.trans (centralizer_le hP)),sup_comm]
  have he : ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆=
      ⁅Z d.radical a,X₀⁆ := by
    rw [commutator_comm,hX]
    exact movement_central_supplement X₀ C (Q d.radical t) (Z d.radical a) hCX hCT hZaT
  obtain ⟨r,hr⟩ := plane_cover_fixed_movement_index cv (Z d.radical a) P hZaT hP
  rw [he]
  exact ⟨r,hr⟩

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem attachment_le_of_field_power_index
    {G : Type*} [Group G] (A M : Subgroup G) [Finite A] [Finite M]
    {q : ℕ} (hq : 1 < q) (hsmall : Nat.card A < q)
    (hcard : Nat.card M=q*Nat.card A) (r : ℕ) (hi : A.relIndex M=q^r) : A ≤ M := by
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hbound : q^r ≤ Nat.card M := hi ▸ Nat.le_of_dvd hMpos (relIndex_dvd_card A M)
  have hr0 : r ≠ 0 := by
    intro he
    have hMA : M ≤ A := relIndex_eq_one.mp (by simpa only [he,pow_zero] using hi)
    have hh := Nat.card_le_card_of_injective (inclusion hMA) (inclusion_injective _)
    nlinarith only [hh,hcard,hq,hApos]
  have hr1 : r=1 := by
    by_contra hn
    have hr : 2 ≤ r := by omega
    have hh := Nat.pow_le_pow_right (by omega : 0 < q) hr
    nlinarith only [hh,hbound,hcard,hsmall,hq]
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ M) M bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,hi,hr1,pow_one,hcard] at hm
  have hc : Nat.card (A ⊓ M : Subgroup G)=Nat.card A := by nlinarith only [hm,hq]
  have he : A ⊓ M=A := Subgroup.eq_of_le_of_card_ge inf_le_left hc.ge
  exact he.ge.trans inf_le_right

/-- The escaping-centralizer subcase of source (4) cannot have unequal
attachments of less than field order. The first attachment lies in the
opposite movement by its field-power index; individual commutators then
identify the two complete attachments. -/
theorem source_four_large_escaping_small_attachment_eq
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z)
    (hsmall : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical)) ≠ 2^n) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  let M := ⁅X,Z d.radical a⁆
  let := finite_Z d.radical a
  let := finite_Z d.radical z
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  let : Finite A' := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z z))) (inclusion_injective _)
  have hcards : Nat.card A=Nat.card A' :=
    source_four_large_attachment_card_eq h d g hb hsat path hat hzt c c' hcritical
  have hMcard : Nat.card M=2^n*Nat.card A' :=
    (source_four_large_escaping_movement h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).2.2.trans (congrArg (2^n*·) hcards)
  let : Finite M := Nat.finite_of_card_ne_zero (by rw [hMcard]; exact mul_ne_zero (by positivity) Nat.card_pos.ne')
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have hsmall' : Nat.card A' < 2^n := by
    have hh := moving_fixed_attachment_card_le_field h d path.start_color
    change Nat.card A ≤ 2^n at hh
    rw [←hcards]
    exact lt_of_le_of_ne hh hsmall
  obtain ⟨r,hr⟩ := source_four_large_hyperplane_movement_index h d g hb hsat path hat hzt c c' hcritical P hP
  have hA'M : A' ≤ M := attachment_le_of_field_power_index A' M hq hsmall' hMcard r hr
  have hmeet : M ⊓ A'=A ⊓ A' := source_four_large_escaping_attachment_intersection
    h d g hb hsat path hat hzt c c' hcritical P hP hpoint hi hescape hsmall
  have hA'A : A' ≤ A := by
    have he : A'=A ⊓ A' := (inf_eq_right.mpr hA'M).symm.trans hmeet
    exact he.le.trans inf_le_left
  exact (Subgroup.eq_of_le_of_card_ge hA'A hcards.le).symm


/-- The actual hyperplane supplied by source (4), with the escaping movement
excluded from H when the full attachments differ. In that escaping subcase
both complete attachments must have field order. All section centralizers are literal. -/
theorem source_four_large_unequal_hyperplane
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      let A₁ := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=2^n ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        ¬ ⁅X,Z d.radical a⁆ ≤ H₀ ∧
        Nat.card A₁=2^n ∧ Nat.card A₀=2^n) := by
  obtain ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR⟩ :=
    source_four_large_hyperplane_attachment h d g hb hsat path hat hzt c c' hcritical
  refine ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,?_⟩
  intro hescape
  have hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n := by
    by_contra hn
    exact hne (source_four_large_escaping_small_attachment_eq h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape hn)
  exact ⟨source_four_large_escaping_not_le_hyperplane h d g hb hsat path hat hzt c c'
    hcritical P B hP hpoint hi hmem hcard hne hescape,hfull,
    (source_four_large_attachment_card_eq h d g hb hsat path hat hzt c c' hcritical).symm.trans hfull⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
