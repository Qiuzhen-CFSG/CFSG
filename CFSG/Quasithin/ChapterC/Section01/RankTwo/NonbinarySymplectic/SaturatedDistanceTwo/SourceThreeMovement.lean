module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreePlane

/-!
# Whole-core and plane-radical movement in MS93 (3.7)(3)

The actual whole core modulo its complete component-fixed subgroup is a
natural dual cover. Dualizing the fixed-vector lifting theorem shows that
each individual displacement on this section is realized in its embedded
natural submodule, with the same actor. Transport through the original
coordinate map therefore gives [Q,A] ≤ [U,A] D. For the opposite critical
layer this is the source containment [Q,Z′] ≤ R D, where R = [Z,Z′].

In the noncontained-core branch, the preceding plane-cover calculation
identifies the natural displacement planes of Q and the full radical T.
The entire opposite fixed attachment lies in R, so this equality lifts
through the original cover and gives [T,Z′] = [Q,Z′]. Source (1) puts the
component-radical displacement in U; intersecting R D with U and retaining
the full attachment U ∩ D gives [T₀,Z′] = R.

This proves the whole-core and component-intersection movement step on
printed p.874. The subsequent containment T₀ ≤ Z Q′, overlap comparison
and plane-radical generator contradiction remain necessary to exclude
this branch. Paired fixed-kernel equality, source (5)/(6) selection and the
field restriction are not asserted here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(3), printed p.874, using (1.5)(ii) and (3.7)(1)--(2).
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour

private theorem dual_displacement_lifts
    {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (i : (binaryNatural (K := F)).IntertwiningMap σ)
    (hi : Function.Injective i) (hd : IsDualCover i.range)
    (g : L (K := F)) (w : W) :
    ∃ v, σ g w-w=i (binaryNatural g v-v) := by
  let p₀ := dualIntertwining i
  have hp₀ := dualCover_dual_isCover i hi hd
  let e := binarySelfDual (K := F)
  let p : σ.dual.IntertwiningMap (binaryNatural (K := F)) :=
    (e.symm.toLinearMap.comp p₀.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g f
      apply e.injective
      change e (e.symm (p₀ (σ.dual g f))) = e (binaryNatural g (e.symm (p₀ f)))
      rw [e.apply_symm_apply,p₀.isIntertwining,binarySelfDual_equivariant,
        e.apply_symm_apply])
  have hp : IsCover p := by
    refine ⟨e.symm.surjective.comp hp₀.1,?_,hp₀.2.2⟩
    intro f hf
    apply hp₀.2.1
    change e.symm (p₀ f)=0 at hf
    exact e.symm.injective (hf.trans (map_zero e.symm).symm)
  let D := (i.toLinearMap.comp (binaryNatural g-LinearMap.id)).range
  have hmem : σ g w-w ∈ D := by
    by_contra hn
    obtain ⟨f,hf,hfD⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
    have he : (binaryNatural (K := F)).dual g⁻¹ (p₀ f)=p₀ f := by
      apply LinearMap.ext
      intro v
      change f (i (binaryNatural (g⁻¹)⁻¹ v))=f (i v)
      rw [inv_inv]
      have hz : f (i (binaryNatural g v-v))=0 := by
        have hh : f (i (binaryNatural g v-v)) ∈ (⊥ : Submodule (ZMod 2) (ZMod 2)) := by
          rw [←hfD]
          exact Submodule.mem_map_of_mem ⟨v,rfl⟩
        exact hh
      simpa only [map_sub,sub_eq_zero] using hz
    have he' : binaryNatural g⁻¹ (p f)=p f := by
      apply e.injective
      change e (binaryNatural g⁻¹ (e.symm (p₀ f)))=e (e.symm (p₀ f))
      rw [binarySelfDual_equivariant,e.apply_symm_apply,he]
    have hfix := cover_fixed_of_projection_fixed p hp g⁻¹ f he'
    have hw := LinearMap.congr_fun hfix w
    change f (σ (g⁻¹)⁻¹ w)=f w at hw
    rw [inv_inv] at hw
    exact hf (by rw [map_sub,hw,sub_self])
  obtain ⟨v,hv⟩ := hmem
  exact ⟨v,hv.symm⟩

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


private theorem cover_displacement_le_of_equal_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A T : Subgroup G) (hAT : A ≤ T)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (β : T →* L (K := F))
    (hact : ∀ (a : T) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hindex : (centralizer (A : Set G)).relIndex U=(centralizer (T : Set G)).relIndex U)
    (hker : ∀ w, p w=0 → j (Multiplicative.ofAdd w) ∈ ⁅A,U⁆) :
    ⁅T,U⁆ ≤ ⁅A,U⁆ := by
  let βA := β.comp (inclusion hAT)
  let α := (commutator (Sp F)).subtype.comp β
  let αA := (commutator (Sp F)).subtype.comp βA
  have hactA (a : A) (w : W) : j (Multiplicative.ofAdd (σ (βA a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹ := hact (inclusion hAT a) w
  rw [cover_moving_index σ p hp U A j hj hjr βA hactA,
    cover_moving_index σ p hp U T j hj hjr β hact] at hindex
  have hdim : Module.finrank F (displacementSpace αA.range)=
      Module.finrank F (displacementSpace α.range) :=
    Nat.pow_right_injective (Finite.one_lt_card : 1 < Nat.card F) hindex
  have hmono : displacementSpace αA.range ≤ displacementSpace α.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,v⟩,rfl⟩
    obtain ⟨a,ha⟩ := x.property
    change x.val • v-v ∈ _
    rw [←ha]
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp α.range.subtype)
      ⟨α (inclusion hAT a),⟨inclusion hAT a,rfl⟩⟩ v
  have heq := Submodule.eq_of_le_of_finrank_le hmono hdim.ge
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨w,rfl⟩ := hjr.symm ▸ hy
  let v := σ (β ⟨x,hx⟩) w.toAdd-w.toAdd
  have hv : p v ∈ displacementSpace αA.range := by
    rw [heq]
    dsimp only [v]
    rw [map_sub,p.isIntertwining]
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp α.range.subtype)
      ⟨α ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩⟩ (p w.toAdd)
  obtain ⟨u,hu,hucomm⟩ := natural_displacement_lifts U A j hjr βA σ hactA p hp.1 (p v) hv
  have hdiff : j (Multiplicative.ofAdd (v-u)) ∈ ⁅A,U⁆ :=
    hker _ (by rw [map_sub,hu,sub_self])
  have hh := (⁅A,U⁆).mul_mem hucomm hdiff
  rw [←map_mul,←ofAdd_add,show u+(v-u)=v by abel] at hh
  dsimp only [v] at hh
  rw [ofAdd_sub,map_div,div_eq_mul_inv,hact] at hh
  exact hh

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Each whole-core displacement modulo the complete fixed core is already
realized by a displacement of the natural core, with the same actor. -/
theorem whole_core_displacement_le
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical a) :
    ⁅Q d.radical a,A⁆ ≤ ⁅U d.radical a,A⁆ ⊔ fixedCore d.radical a := by
  obtain ⟨E,hE,s,γ,hγ,i,hi,hd,hrange,_⟩ := wholeKernel_natural_dualCover h d g hb ha
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun B : Subgroup d.overgroup => B.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hγonto : Function.Surjective γ := MonoidHom.range_eq_top.mp (hγ.trans hCtop)
  let π := s.sectionData.coordinates
  let cm (x : stabilizer d.radical a) (y : Q d.radical a) : Q d.radical a :=
    (⟨x.val*y.val*x.val⁻¹,
      (mem_normalizer_iff.mp (s.sectionData.normalized x.property) y).mp y.property⟩ : Q d.radical a)*y⁻¹
  have hcm (x : stabilizer d.radical a) (y : Q d.radical a) :
      (π (cm x y)).toAdd=s.action (s.quotient x) (π y).toAdd-(π y).toAdd := by
    dsimp only [cm,π]
    rw [map_mul,map_inv]
    change (s.sectionData.coordinates ⟨x.val*y.val*x.val⁻¹,_⟩).toAdd +
      -(s.sectionData.coordinates y).toAdd = _
    rw [s.sectionData.equivariant,sub_eq_add_neg]
    rfl
  rw [commutator_comm (Q d.radical a)]
  apply commutator_le.mpr
  intro x hx y hy
  let xs : stabilizer d.radical a := ⟨x,hA hx⟩
  let yq : Q d.radical a := ⟨y,hy⟩
  obtain ⟨b,hbq⟩ := hγonto (s.quotient xs)
  obtain ⟨v,hv⟩ := dual_displacement_lifts i hi hd b (π yq).toAdd
  obtain ⟨u,hu,heu⟩ := (hrange (i v)).mp ⟨v,rfl⟩
  have he : π (cm xs yq)=π (cm xs u) := by
    apply Multiplicative.toAdd.injective
    rw [hcm,hcm,heu,←hbq]
    change (s.action.comp γ) b (π yq).toAdd-(π yq).toAdd =
      (s.action.comp γ) b (i v)-i v
    rw [hv,←i.isIntertwining,map_sub]
  have hk : ((cm xs u)⁻¹*cm xs yq).val ∈ fixedCore d.radical a := by
    apply (s.sectionData.coordinates_eq_one_iff _).mp
    change π ((cm xs u)⁻¹*cm xs yq)=1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hc : (cm xs u).val ∈ ⁅U d.radical a,A⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hx hu
  have hh := (⁅U d.radical a,A⁆ ⊔ fixedCore d.radical a).mul_mem
    (mem_sup_left hc) (mem_sup_right hk)
  change (cm xs u).val*((cm xs u).val⁻¹*(cm xs yq).val) ∈ _ at hh
  have hh' : (cm xs yq).val ∈ ⁅U d.radical a,A⁆ ⊔ fixedCore d.radical a := by
    simpa only [mul_inv_cancel_left] using hh
  exact hh'

/-- The whole-core movement used in source (3.7)(3), retaining the full
fixed attachment and the literal opposite critical layer. -/
theorem source_three_whole_core_movement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical=2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    ⁅Q d.radical a,Z d.radical z⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆ ⊔ fixedCore d.radical a := by
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hh := whole_core_displacement_le h d g hb path.start_color (Z d.radical z) hZA
  rwa [←critical_displacement_eq_moving h d path hb hat hzt] at hh

/-- In the noncontained-core case the opposite whole core already generates
all full-radical displacement on Z′. The full central attachment is present
in the critical commutator, so equality of natural displacement planes lifts
through the original cover. -/
theorem source_three_noncontained_full_movement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    ⁅Q d.radical t,Z d.radical z⁆=⁅Q d.radical a,Z d.radical z⁆ := by
  obtain ⟨⟨cv⟩,hcore,hfull⟩ :=
    source_three_noncontained_plane_cover h d g hb hsat path hat hzt c c' hcritical hnot
  have hpair := critical_paired_fixed_layers h d path hb hat hzt hcritical
  have hZaQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hmove : ⁅Q d.radical t,U d.radical z⁆ ≤ ⁅Q d.radical a,U d.radical z⁆ := by
    apply cover_displacement_le_of_equal_index
      (MovedSection.coverAction (replacementMovedSection h d) cv.equiv)
      (MovedSection.coverProjection (replacementMovedSection h d) cv.equiv) cv.cover
      (U d.radical z) (Q d.radical a) (Q d.radical t) c.core_le_edge
      cv.embedding cv.injective cv.range_eq cv.actor cv.actor_conjugation
      (hcore.trans hfull.symm)
    intro w hw
    have hk : cv.embedding (Multiplicative.ofAdd w) ∈
        U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :=
      ⟨cv.range_eq ▸ ⟨_,rfl⟩,(cv.kernel w).mp hw⟩
    have hh := hpair.2.1 (mem_sup_right hk)
    rw [hpair.1] at hh
    exact commutator_mono ((U_le_Z a).trans hZaQ) le_rfl hh
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (path.end_color.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcentral : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hUzT : U d.radical z ≤ Q d.radical t := (U_le_Z z).trans
    (Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color) (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
        g.distance_constant z path.end_color]
      change 1 < g.b d.radical
      omega))
  apply le_antisymm ?_ (commutator_mono c.core_le_edge le_rfl)
  apply (commutator_le_moving_of_inner_mod_centralizer (Q d.radical t)
    (U d.radical z) (Z d.radical z) (hUzT.trans (Q d.radical t).le_normalizer) ?_).trans
      (hmove.trans (commutator_mono le_rfl (U_le_Z z)))
  rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt]
  exact sup_le_sup_left hcentral _

/-- The component part of the full radical moves Z′ only into the critical
commutator. This is the component-intersection step on printed p.874; neither
full fixed core is discarded and no equality of their kernels is assumed. -/
theorem source_three_noncontained_component_movement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    ⁅componentRadical d a t,Z d.radical z⁆ = ⁅Z d.radical a,Z d.radical z⁆ := by
  let W := ⁅Z d.radical a,Z d.radical z⁆
  have hpair := critical_paired_fixed_layers h d path hb hat hzt hcritical
  have hWU : W ≤ U d.radical a := hpair.2.2.1.trans inf_le_left
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _))
  have hWD : W ≤ normalizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) :=
    hWU.trans (hUQ.trans (c.core_le_edge.trans c.fixedCore_normalized))
  have hcomp : ⁅componentRadical d a t,Z d.radical z⁆ ≤ U d.radical a := by
    rw [commutator_comm]
    exact (paired_source_triples h d g hb hsat path hat hzt c c').1
  have hbound : ⁅componentRadical d a t,Z d.radical z⁆ ≤ W ⊔ fixedCore d.radical a := by
    apply (commutator_mono inf_le_left le_rfl).trans
    rw [source_three_noncontained_full_movement h d g hb hsat path hat hzt c c' hcritical hnot]
    exact source_three_whole_core_movement h d path hb hat hzt
  apply le_antisymm
  · intro x hx
    have hxU := hcomp hx
    have hxprod := hbound hx
    rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hWD] at hxprod
    obtain ⟨r,hr,y,hy,rfl⟩ := hxprod
    have hyU : y ∈ U d.radical a := by
      have hh := (U d.radical a).mul_mem ((U d.radical a).inv_mem (hWU hr)) hxU
      simpa only [inv_mul_cancel_left] using hh
    have hyW : y ∈ W := hpair.2.1 (mem_sup_left ⟨hyU,hy.2⟩)
    exact W.mul_mem hr hyW
  · rw [critical_displacement_eq_moving h d path hb hat hzt]
    exact commutator_mono
      ((c.componentRadical_inf_core g hb path.start_color).symm.le.trans inf_le_left) le_rfl

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
