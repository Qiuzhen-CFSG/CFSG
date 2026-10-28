module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeMovement
public import Theory.SpecificGroups.SymplecticFour.QuadraticRefinementObstruction

/-!
# The full plane geometry of a large critical image

For a critical image of order at least q squared, source (2) makes its
natural displacement fixed by the entire common radical. Quadratic
symplectic geometry forces this displacement to be a self-orthogonal
plane. Genuine saturation gives radical order at least q cubed, so the
radical fills that plane's pointwise fixer after an actual symplectic
basis change. The resulting cover retains the original quotient marking,
the full endpoint core as kernel, and the complete central attachment.

The large quadratic actor preserves no quadratic refinement. Therefore
its commutator contains the whole cover kernel. Equality of the natural
displacement planes then lifts to equality of the critical and full-radical
commutators. Apply this at both ends of the same critical path: both
midpoint indices are q squared and both full fixed attachments lie in the
same full-radical displacement R.

These are the Q₂ geometry and displacement inputs to MS93 (3.7)(4),(6),
printed pp.875--876. The hyperplane comparison proving equality of the
attachments in this branch, the remaining (5)/(6) arguments, and the field
restriction remain open. No order-q condition is imposed on the full radical.

The private cover and plane transports adapt SourceThreePlane and
SourceThreeMovement to the actual large critical actor. Source:
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two* (1993).
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour

private theorem displacement_mono {F : Type*} [Field F]
    {A B : Subgroup (Sp F)} (hAB : A ≤ B) : displacementSpace A ≤ displacementSpace B := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x,v⟩,rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp B.subtype)
    ⟨x.val,hAB x.property⟩ v

private theorem plane_radical_of_fixed_plane {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] (T : Subgroup (Sp F)) (P : Submodule F (Vector F))
    (hdim : Module.finrank F P=2) (hiso : ∀ x ∈ P, ∀ y ∈ P, form F x y=0)
    (hfix : P ≤ TwoLocalCover.fixedSpace T) (hcard : Nat.card F^3 ≤ Nat.card T) :
    ∃ v : Sp F, T.map (MulAut.conj v).toMonoidHom=planeRadicalAmbient := by
  have hne : P ≠ ⊥ := by intro he; rw [he,finrank_bot] at hdim; omega
  obtain ⟨v,hv⟩ := TwoLocalCover.isotropic_subspace_conjugate_standard P hne hiso
  have hp : P.map (toLinear v).toLinearMap=plane F := by
    rcases hv with hp | hp
    · have he := congrArg (fun V : Submodule F (Vector F) => Module.finrank F V) hp
      rw [(toLinear v).finrank_map_eq,hdim,finrank_point] at he
      omega
    · exact hp
  refine ⟨v,Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    let y := (MulAut.conj v) x
    have hyfix (w : Vector F) (hw : w ∈ plane F) : y • w=w := by
      obtain ⟨u,hu,rfl⟩ := hp.symm ▸ hw
      change (v*x*v⁻¹) • (v • u)=v • u
      rw [mul_smul,mul_smul,inv_smul_smul,hfix hu x hx]
    have hA : y.val.toBlocks₁₁=1 := by
      ext i k
      have hh := congrFun (hyfix (e k) (e_mem_plane k)) (.inl i)
      simpa [smul_eq_mulVec,Theory.SpecificGroups.SymplecticFour.e,Matrix.mulVec_single,Matrix.toBlocks₁₁,Matrix.one_apply,
        Pi.single_apply] using hh
    have hP : y ∈ planeParabolic := by
      rw [mem_planeParabolic_iff]
      intro i k
      have hh := congrFun (hyfix (e k) (e_mem_plane k)) (.inr i)
      simpa [smul_eq_mulVec,Theory.SpecificGroups.SymplecticFour.e,Matrix.mulVec_single] using hh
    have hy : y ∈ planeLocal := (Plane.mem_local_iff y).mpr ⟨hP,by rw [hA]; exact Matrix.det_one⟩
    refine ⟨⟨y,hy⟩,?_,rfl⟩
    apply Subtype.ext
    exact hA
  · rw [card_map_of_injective (K := T) (MulAut.conj v).injective]
    exact (SymplecticConjugatePair.card_planeRadical (F := F)).trans_le hcard

private theorem embedded_displacement_fixed
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U T A : Subgroup G) (hAT : A ≤ T)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (β : T →* L (K := F))
    (hact : ∀ t : T, ∀ w, j (Multiplicative.ofAdd (σ (β t) w))=
      t.val*j (Multiplicative.ofAdd w)*t.val⁻¹)
    (hcomm : ⁅U,A⁆ ≤ centralizer (T : Set G)) :
    displacementSpace (((commutator (Sp F)).subtype.comp β).comp (inclusion hAT)).range ≤
      TwoLocalCover.fixedSpace ((commutator (Sp F)).subtype.comp β).range := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x,v⟩,rfl⟩ t ⟨y,rfl⟩
  change ((commutator (Sp F)).subtype.comp β) y • (x.val • v-v)=x.val • v-v
  obtain ⟨x,hx⟩ := x.property
  rw [←hx]
  obtain ⟨w,rfl⟩ := hp.1 v
  have hval : j (Multiplicative.ofAdd (σ (β (inclusion hAT x)) w-w))=
      ⁅x.val,j (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  have hc : y.val*⁅x.val,j (Multiplicative.ofAdd w)⁆=
      ⁅x.val,j (Multiplicative.ofAdd w)⁆*y.val := by
    apply hcomm
    · rw [commutator_comm]
      exact commutator_mem_commutator x.property (hjr ▸ ⟨_,rfl⟩)
    · exact y.property
  have he : σ (β y) (σ (β (inclusion hAT x)) w-w)=σ (β (inclusion hAT x)) w-w := by
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hact,hval,hc,mul_inv_cancel_right]
  have hh := congrArg p he
  rw [p.isIntertwining,map_sub,p.isIntertwining] at hh
  exact hh
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

private theorem plane_of_large_fixed
    {F : Type*} [Field F] [Finite F]
    (T A : Subgroup (Sp F)) (hAT : A ≤ T)
    (hfix : displacementSpace A ≤ TwoLocalCover.fixedSpace T)
    (hlarge : Nat.card F < Nat.card A) :
    Module.finrank F (displacementSpace A)=2 ∧
      TwoLocalCover.fixedSpace T=displacementSpace A ∧
      displacementSpace T=displacementSpace A := by
  have hquad : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
    intro x hx y hy v
    exact hfix (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp A.subtype) ⟨y,hy⟩ v) x (hAT hx)
  have hself := large_quadratic_displacement_self_orthogonal A hquad hlarge
  have hdim : Module.finrank F (displacementSpace A)=2 := by
    have hh := LinearMap.BilinForm.finrank_orthogonal
      (W := displacementSpace A) TwoLocalCover.form_nondegenerate
    rw [hself] at hh
    have hV : Module.finrank F (Vector F)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hV] at hh
    omega
  have hfixed : TwoLocalCover.fixedSpace T=displacementSpace A := by
    apply le_antisymm ?_ hfix
    intro v hv
    rw [←hself,orthogonal_displacementSpace]
    exact fun x hx => hv x (hAT hx)
  refine ⟨hdim,hfixed,?_⟩
  apply le_antisymm ?_ (displacement_mono hAT)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x,v⟩,rfl⟩
  exact displacement_mem_of_self_orthogonal (displacementSpace A) hself x.val
    (fun u hu => hfix hu x.val x.property) v

private theorem large_cover_kernel_le_commutator
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (hF : 2 < Nat.card F) (U A : Subgroup G)
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ a : A, ∀ w, j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hcard : Nat.card F^2 ≤ Nat.card ((commutator (Sp F)).subtype.comp β).range)
    (hquad : ∀ x ∈ ((commutator (Sp F)).subtype.comp β).range,
      ∀ y ∈ ((commutator (Sp F)).subtype.comp β).range, ∀ v : Vector F,
        x • (y • v-v)=y • v-v) :
    p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j ≤ ⁅A,U⁆ := by
  by_contra hn
  obtain ⟨v,hv⟩ := embedded_cover_preserves_refinement_of_kernel_escape ⁅A,U⁆ A
    σ p hp j β hact (by rw [hjr]) hn
  apply no_refinement_of_large_quadratic hF _ hcard hquad
  refine ⟨v,?_⟩
  rintro ⟨_,⟨x,rfl⟩⟩ w
  exact hv x w

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A critical image of at least q squared forces the full saturated radical
onto the plane radical in the original natural cover. Its movement has index
q squared, and the complete fixed attachment lies in the critical commutator. -/
theorem source_four_large_plane_cover
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    Nonempty (RadicalPlaneCover d.radical (replacementMovedSection h d) n z t) ∧
      (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)=(2^n)^2 ∧
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)=(2^n)^2 ∧
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ≤
        ⁅Z d.radical a,U d.radical z⁆ := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let β := γ.comp (inclusion c'.edge_le)
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hact (u : Q d.radical t) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β u) w)) =
        u.val*j (Multiplicative.ofAdd w)*u.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion c'.edge_le u)))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion c'.edge_le u) w
  have hαker : α.ker = (Q d.radical z).subgroupOf (Q d.radical t) := by
    have hkκ : κ.ker = (Q d.radical z).subgroupOf (stabilizer d.radical z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [α,β,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hFc : Nat.card E.Carrier=2^n := E.card_eq.trans (congrArg (2^·) hE)
  have hZaQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hZaT := hZaQ.trans c.core_le_edge
  let βZ := β.comp (inclusion hZaT)
  let αZ := (commutator (Sp E.Carrier)).subtype.comp βZ
  have hZker : αZ.ker=(Q d.radical z).subgroupOf (Z d.radical a) := by
    change (α.comp (inclusion hZaT)).ker=_
    rw [←MonoidHom.comap_ker,hαker,comap_inclusion_subgroupOf]
  have hZcard : Nat.card E.Carrier^2 ≤ Nat.card αZ.range := by
    rw [←index_ker,hZker,hFc]
    exact hcritical
  have hZT : αZ.range ≤ α.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨inclusion hZaT y,rfl⟩
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (path.end_color.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcomm : ⁅U d.radical z,Z d.radical a⁆ ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    apply ((commutator_mono (U_le_Z z) hZaQ).trans
      (source_two_midpoint_containment h d g hb hsat path hat hzt c c')).trans
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hfix := embedded_displacement_fixed (MovedSection.coverProjection s e) he
    (U d.radical z) (Q d.radical t) (Z d.radical a) hZaT
    j hj hjr β hact hcomm
  have hlarge : Nat.card E.Carrier < Nat.card αZ.range := by
    have hq : 1 < Nat.card E.Carrier := Finite.one_lt_card
    nlinarith
  obtain ⟨hZdim,hfixed,hTdisp⟩ := plane_of_large_fixed α.range αZ.range hZT hfix hlarge
  have hquad : ∀ x ∈ αZ.range, ∀ y ∈ αZ.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    intro x hx y hy v
    exact hfix (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp αZ.range.subtype) ⟨y,hy⟩ v) x (hZT hx)
  have hcard : Nat.card E.Carrier^3 ≤ Nat.card α.range := by
    rw [←index_ker,hαker]
    have hc : (Q d.radical z).relIndex (Q d.radical t)=Nat.card c'.action.range := by
      rw [←index_ker,c'.action_kernel]
      rfl
    change Nat.card E.Carrier^3 ≤ (Q d.radical z).relIndex (Q d.radical t)
    rw [hc,c'.action_range,hFc,←h.field_card]
    rcases marked_radical_card h d g (by omega) hsat with hh | hh
    · exact hh.ge
    · rw [hh]
      exact Nat.pow_le_pow_right Nat.card_pos (by decide)
  have hp := plane_radical_of_fixed_plane α.range (displacementSpace αZ.range)
    hZdim (quadratic_displacement_isotropic αZ.range hquad) hfix hcard
  refine ⟨⟨{ toAmbientVertexCover := ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,
              hfaith,hsemi,hconj,hproj,hker⟩
             edge_le := c'.edge_le
             actor := β
             actor_marking := fun u => congrArg Subtype.val
               (e.groupEquiv.symm_apply_apply (κC (inclusion c'.edge_le u)))
             actor_conjugation := hact
             actor_kernel := hαker
             plane_image := hp }⟩,?_,?_,?_⟩
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U d.radical z) (Z d.radical a) j hj hjr βZ
        (fun u w => hact (inclusion hZaT u) w),hZdim,hFc]
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U d.radical z) (Q d.radical t) j hj hjr β hact,hTdisp,hZdim,hFc]
  · have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
        U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
      apply le_antisymm
      · rintro x ⟨w,hw,rfl⟩
        exact ⟨hjr ▸ ⟨w,rfl⟩,(hker w.toAdd).mp hw⟩
      · rintro x ⟨hx,hc⟩
        obtain ⟨w,rfl⟩ := hjr.symm ▸ hx
        exact ⟨w,(hker w.toAdd).mpr hc,rfl⟩
    rw [←hk]
    apply large_cover_kernel_le_commutator
      (F := E.Carrier) ?_ (U d.radical z) (Z d.radical a)
      (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he j hjr βZ
      (fun u w => hact (inclusion hZaT u) w) hZcard hquad
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)



/-- In the large critical-image branch the full radical moves the opposite
Z-layer by exactly the critical commutator, including its full fixed kernel. -/
theorem source_four_large_full_movement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ⁅Q d.radical t,Z d.radical z⁆=⁅Z d.radical a,Z d.radical z⁆ := by
  obtain ⟨⟨cv⟩,hcriticalIndex,hfull,hfixed⟩ :=
    source_four_large_plane_cover h d g hb hsat path hat hzt c c' hcritical
  have hZaQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hZaT := hZaQ.trans c.core_le_edge
  have hmove : ⁅Q d.radical t,U d.radical z⁆ ≤ ⁅Z d.radical a,U d.radical z⁆ := by
    apply cover_displacement_le_of_equal_index
      (MovedSection.coverAction (replacementMovedSection h d) cv.equiv)
      (MovedSection.coverProjection (replacementMovedSection h d) cv.equiv) cv.cover
      (U d.radical z) (Z d.radical a) (Q d.radical t) hZaT
      cv.embedding cv.injective cv.range_eq cv.actor cv.actor_conjugation
      (hcriticalIndex.trans hfull.symm)
    intro w hw
    exact hfixed ⟨cv.range_eq ▸ ⟨_,rfl⟩,(cv.kernel w).mp hw⟩
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
  apply le_antisymm ?_ (commutator_mono hZaT le_rfl)
  apply (commutator_le_moving_of_inner_mod_centralizer (Q d.radical t)
    (U d.radical z) (Z d.radical z) (hUzT.trans (Q d.radical t).le_normalizer) ?_).trans
      (hmove.trans (commutator_mono le_rfl (U_le_Z z)))
  rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt]
  exact sup_le_sup_left hcentral _

/-- The large critical branch has the plane-radical geometry at both ends,
both midpoint indices q squared, and the same full displacement R. Both
complete fixed attachments belong to R; their equality is not assumed. -/
theorem source_four_large_paired_geometry
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    Nonempty (RadicalPlaneCover d.radical (replacementMovedSection h d) n a t) ∧
      Nonempty (RadicalPlaneCover d.radical (replacementMovedSection h d) n z t) ∧
      (Z d.radical t).relIndex (Z d.radical a)=(2^n)^2 ∧
      (Z d.radical t).relIndex (Z d.radical z)=(2^n)^2 ∧
      ⁅Z d.radical a,Q d.radical t⁆=⁅Z d.radical a,Z d.radical z⁆ ∧
      ⁅Z d.radical z,Q d.radical t⁆=⁅Z d.radical a,Z d.radical z⁆ ∧
      (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) ⊔
        (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) ≤
          ⁅Z d.radical a,Z d.radical z⁆ := by
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
    nlinarith
  obtain ⟨ha,_,hai,haf⟩ := source_four_large_plane_cover h d g hb hsat rev hzt hat c' c hreverse
  obtain ⟨hz,_,hzi,hzf⟩ := source_four_large_plane_cover h d g hb hsat path hat hzt c c' hcritical
  refine ⟨ha,hz,
    (midpoint_relIndex_eq_moving_centralizer h d g hb path.start_color hat c).trans hai,
    (midpoint_relIndex_eq_moving_centralizer h d g hb path.end_color hzt c').trans hzi,
    ?_,?_,?_⟩
  · rw [commutator_comm (Z d.radical a),
      source_four_large_full_movement h d g hb hsat rev hzt hat c' c hreverse,
      commutator_comm]
  · rw [commutator_comm (Z d.radical z)]
    exact source_four_large_full_movement h d g hb hsat path hat hzt c c' hcritical
  · apply sup_le
    · exact haf.trans (by rw [commutator_comm]; exact commutator_mono (U_le_Z a) le_rfl)
    · exact hzf.trans (commutator_mono le_rfl (U_le_Z z))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
