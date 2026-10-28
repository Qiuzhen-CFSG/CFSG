module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceSixCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourRadicalGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeMovement

/-!
# Whole-core displacement in MS93 (3.7)(6)

For the large critical pair, the paired full radical displacements agree.
Consequently [Q,B] lies in U for every B in the opposite Z-layer. The
whole-core dual cover bounds this displacement modulo the complete fixed
core D by the natural displacement. Intersecting with U retains exactly
the full attachment A = U ∩ D. The reverse inclusion of natural movement,
and the central midpoint factor in Z, give the exact fixed index.

Apply this to the actual X = C_{Z′}(x^g) selected in SourceSixCritical.
Its reciprocal fixed index is q, so [Q′^g,X] has index q modulo A′ and
cannot generate the full radical displacement of index q squared, even
after adjoining A′. The same x, conjugator, induced midpoint action and
full kernels are retained in the literal Chapter11 consumer.

This proves the displacement comparison on printed p.876. The subsequent
whole-core centralizer bound and collapse, the order-q critical-pair
existence conclusion, and the field-four endgame remain to be established.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(6). The private cover-index transports reuse the checked
SourceFourRadicalGeneration calculations without changing its boundary.
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



private theorem cover_displacement_index
    {E W G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (U A : Subgroup G) (hAU : A ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range = U)
    (β : A →* L (K := E))
    (hact : ∀ a : A, ∀ w : W, j (Multiplicative.ofAdd (σ (β a) w)) =
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    : (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j).relIndex ⁅A,U⁆ =
      (centralizer (A : Set G)).relIndex U := by
  let C := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  let α := (commutator (Sp E)).subtype.comp β
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
  have hBcard : Nat.card B = Nat.card E ^ Module.finrank E (displacementSpace α.range) := by
    let e : B ≃ displacementSpace α.range :=
      { toFun := fun x => ⟨x.val.toAdd,x.property⟩
        invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := E)]
  exact (hindex.trans hBcard).trans
    (cover_moving_index σ p hp U A j hj hjr β hact).symm


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

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
private theorem plane_cover_displacement_index
    {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {C₀ : Subgroup J}
    {T : Subgroup M} {s : MovedSection ρ C₀} {n : ℕ} {z t : Vertex T}
    [FiniteDimensional (ZMod 2) s.space.toSubmodule]
    (cv : RadicalPlaneCover T s n z t)
    (A : Subgroup (FreeAmalgam T)) (hA : A ≤ Q T t) :
    (U T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T))).relIndex ⁅A,U T z⁆ =
      (centralizer (A : Set (FreeAmalgam T))).relIndex (U T z) := by
  let p := MovedSection.coverProjection s cv.equiv
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T)) := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  rw [←hk]
  exact cover_displacement_index (U T z) A
    ((hA.trans cv.edge_le).trans (U_normalized z))
    (MovedSection.coverAction s cv.equiv) p cv.cover cv.embedding cv.injective cv.range_eq
    (cv.actor.comp (inclusion hA)) (fun a w => cv.actor_conjugation (inclusion hA a) w)


variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The whole-core displacement has at most the natural fixed index, even
before the whole core has collapsed. The complete fixed attachment is retained. -/
private theorem whole_core_displacement_bound
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (B : Subgroup (FreeAmalgam d.radical)) (hB : B ≤ Z d.radical z) :
    (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅Q d.radical a,B⁆ ≤
      (centralizer (B : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) := by
  obtain ⟨⟨cv⟩,_,_,_,hRa,hRz,_⟩ :=
    source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let D := fixedCore d.radical a
  let N := ⁅U d.radical a,B⁆
  let M := ⁅Q d.radical a,B⁆
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)).trans
      (omegaCenter_le _))
  have hBT : B ≤ Q d.radical t := hB.trans
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c'.core_le_edge))
  have hBS := hBT.trans c.edge_le
  have hMU : M ≤ U d.radical a := by
    have hm : M ≤ ⁅Z d.radical a,Q d.radical t⁆ := by
      rw [hRa,←hRz,commutator_comm]
      exact commutator_mono c.core_le_edge hB
    exact hm.trans (full_radical_Z_displacement_le_moving h d g (by omega) path.start_color c)
  have hNU : N ≤ U d.radical a := by
    dsimp only [N]
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp (hBS.trans (U_normalized a))
  have hMQ := hMU.trans hUQ
  have hDQ : D ≤ Q d.radical a := inf_le_left
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Finite (Z d.radical a) := finite_Z d.radical a
  let : Finite D := Finite.of_injective (inclusion hDQ) (inclusion_injective _)
  let : Finite M := Finite.of_injective (inclusion hMQ) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion (hNU.trans hUQ)) (inclusion_injective _)
  let : Finite (↥(N ⊔ D)) := Finite.of_injective
    (inclusion (sup_le (hNU.trans hUQ) hDQ)) (inclusion_injective _)
  have hnormal : D ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    apply (show D ≤ centralizer (N : Set (FreeAmalgam d.radical)) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro x hx y hy
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color))
      (U_le_Z a (hNU hy)) x (hDQ hx)).symm
  have hDM : D ⊓ M=A ⊓ M := by
    ext x
    exact ⟨fun hx => ⟨⟨hMU hx.2,hx.1.2⟩,hx.2⟩,
      fun hx => ⟨⟨hUQ hx.1.1,hx.1.2⟩,hx.2⟩⟩
  have hDN : D ⊓ N=A ⊓ N := by
    ext x
    exact ⟨fun hx => ⟨⟨hNU hx.2,hx.1.2⟩,hx.2⟩,
      fun hx => ⟨⟨hUQ hx.1.1,hx.1.2⟩,hx.2⟩⟩
  calc
    A.relIndex M = D.relIndex M := by rw [←inf_relIndex_right A M,←hDM,inf_relIndex_right]
    _ ≤ D.relIndex (N ⊔ D) := relIndex_le_of_le_right
      (whole_core_displacement_le h d g hb path.start_color B hBS) index_ne_zero_of_finite
    _ = D.relIndex N := relIndex_sup_of_normalizes N D hnormal
    _ = A.relIndex N := by rw [←inf_relIndex_right D N,hDN,inf_relIndex_right]
    _ = (centralizer (B : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
      rw [show N=⁅B,U d.radical a⁆ from commutator_comm _ _]
      exact plane_cover_displacement_index cv B hBT
    _ ≤ (centralizer (B : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) :=
      relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite

/-- The whole-core displacement has exactly the natural fixed index, even
before the whole core has collapsed. The complete fixed attachment is retained. -/
theorem source_six_whole_core_displacement_index
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (B : Subgroup (FreeAmalgam d.radical)) (hB : B ≤ Z d.radical z) :
    (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅Q d.radical a,B⁆ =
      (centralizer (B : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) := by
  have hupper := whole_core_displacement_bound h d g hb hsat path hat hzt c c' hcritical B hB
  obtain ⟨⟨cv⟩,_,_,_,_⟩ :=
    source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)).trans
      (omegaCenter_le _))
  have hBT : B ≤ Q d.radical t := hB.trans
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c'.core_le_edge))
  let := finite_stabilizer d.radical a
  let := finite_Z d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hMQ : ⁅Q d.radical a,B⁆ ≤ Q d.radical a := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp ((hBT.trans c.edge_le).trans (Q_normalized d.radical a))
  let : Finite (⁅Q d.radical a,B⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hMQ) (inclusion_injective _)
  have hnatural := plane_cover_displacement_index cv B hBT
  let := g.Z_elementary (by omega) a path.start_color
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hat (path.start_color.trans he.symm)
  have hCT : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hfixed := central_supplement_fixed_index (U d.radical a) (Z d.radical t) (Z d.radical a) B
    (U_le_Z a) (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat)
    (Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat)
    (hCT.trans (centralizer_le hBT))
  apply le_antisymm hupper
  rw [hfixed,←hnatural,commutator_comm B]
  exact relIndex_le_of_le_right (commutator_mono hUQ le_rfl) index_ne_zero_of_finite

/-- The source-(6) whole-core displacement cannot fill the full radical
movement, even after adjoining the entire fixed attachment. -/
theorem source_six_whole_core_movement_ne_full
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (B : Subgroup (FreeAmalgam d.radical)) (hB : B ≤ Z d.radical z)
    (hindex : (centralizer (B : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a)=2^n) :
    let A := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    A.relIndex ⁅Q d.radical a,B⁆ = 2^n ∧
      ⁅Q d.radical a,B⁆ ⊔ A ≠ ⁅Z d.radical z,Q d.radical t⁆ := by
  let A := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  let M := ⁅Q d.radical a,B⁆
  have hAe : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))=A :=
    source_four_fixed_attachments h d g hb hsat path hat hzt c c'
  have hbound : A.relIndex M = 2^n := by
    have hh := source_six_whole_core_displacement_index h d g hb hsat path hat hzt c c' hcritical B hB
    rwa [hAe,hindex] at hh
  refine ⟨hbound,?_⟩
  intro he
  have hgeom := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hMU : M ≤ U d.radical a := by
    have hh : M ≤ ⁅Z d.radical a,Q d.radical t⁆ := by
      rw [hgeom.2.2.2.2.1,←hgeom.2.2.2.2.2.1,commutator_comm]
      exact commutator_mono c.core_le_edge hB
    exact hh.trans (full_radical_Z_displacement_le_moving h d g (by omega) path.start_color c)
  let := g.Z_elementary (by omega) a path.start_color
  have hAN : A ≤ normalizer (M : Set (FreeAmalgam d.radical)) :=
    ((hAe.symm.le.trans inf_le_left).trans (U_le_Z a)).trans
      (((Z d.radical a).le_centralizer.trans (centralizer_le (hMU.trans (U_le_Z a)))).trans
        (Subgroup.centralizer_le_normalizer _))
  let := finite_Z d.radical z
  let : Finite A := Finite.of_injective
    (inclusion (show A ≤ Z d.radical z from inf_le_left.trans (U_le_Z z))) (inclusion_injective _)
  have hi := relIndex_sup_of_normalizes M A hAN
  rw [he,hgeom.2.2.2.2.2.1] at hi
  have hc := (source_four_large_displacement_order h d g hb hsat path hat hzt c c' hcritical).2.1
  change A.relIndex ⁅Z d.radical a,Z d.radical z⁆=(2^n)^2 at hc
  rw [hc] at hi
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  nlinarith only [hbound,hi,hq]

/-- The literal source-(6) selection with its exact whole-core displacement
index and the exclusion of full radical movement. -/
theorem source_six_field_pair_or_small_whole_core_movement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧
      Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t ∧
      ∃ y ∈ stabilizer d.radical a, ∃ k ∈ stabilizer d.radical t,
        (∀ u ∈ Q d.radical t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a ∧ Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        Nonempty (CriticalPath d.radical g (act d.radical k⁻¹ z) z) ∧
        ((Q d.radical z).relIndex (Z d.radical (act d.radical k⁻¹ z))=2^n ∨
          (y*x*y⁻¹ ∉ Q d.radical z ∧
            (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))).relIndex
              (Z d.radical z)=2^n ∧
            (Q d.radical (act d.radical k⁻¹ z)).relIndex
              (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical)))=2^n ∧
            (centralizer ((Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))) :
              Set (FreeAmalgam d.radical))).relIndex (Z d.radical (act d.radical k⁻¹ z))=2^n ∧
            (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))).relIndex
              ⁅Q d.radical (act d.radical k⁻¹ z),
                Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))⁆ = 2^n ∧
            ⁅Q d.radical (act d.radical k⁻¹ z),
                Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))⁆ ⊔
              (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) ≠
                ⁅Z d.radical z,Q d.radical t⁆)) := by
  obtain ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,halt⟩ :=
    source_six_field_pair_or_centralizer_configuration h d g hb hsat path hat hzt c c' hcritical
  refine ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,?_⟩
  by_cases hc : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical (act d.radical k⁻¹ z))
  swap
  · exact Or.inl (replacement_critical_indices_eq_field_of_small h d p (by omega) (lt_of_not_ge hc)).1
  rcases halt with hsmall | ⟨hwQ,hi,hQi,hCi⟩
  · rw [hsmall] at hc
    have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
    exfalso
    nlinarith only [hc,hq]
  apply Or.inr
  refine ⟨hwQ,hi,hQi,hCi,?_⟩
  let v := act d.radical k⁻¹ z
  have hkt : act d.radical k⁻¹ t=t := (stabilizer d.radical t).inv_mem hk
  have hvt : Adjacent d.radical v t := by
    simpa only [hkt] using (adjacent_act_iff d.radical k⁻¹ z t).mpr hzt
  obtain ⟨cv⟩ := exists_edgeMarking h d g (by omega) p.start_color hvt
  exact source_six_whole_core_movement_ne_full h d g hb hsat p hvt hzt cv c' hc
    (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))) inf_le_left hCi

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
