module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoIndexContradiction
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry

/-!
# The noncontained-core plane and the complete Sylow branch of MS93 (3.7)(3)

Assume the actual critical Z-image has order q. If Q is not contained in
Z Q′, its image on the opposite natural cover escapes that full long root.
Its natural displacement therefore has dimension at least two. Source (2)
puts the full displacement inside the midpoint omega-center, fixed by the
whole radical. Symplectic orthogonality forces a self-orthogonal plane as
both the core displacement and the radical fixed space and displacement.
The saturated radical has order at least q cubed, so it fills the pointwise
fixer of that plane after an actual symplectic basis change.

The constructed cover retains the original quotient, component marking,
full core kernel and full central attachment. Fixed-vector lifting computes
both movement indices as q squared. Since Z = U Z_t, this gives the printed
indices [Z : Z_t] = [Z′ : Z_t] = q squared and full radical order q cubed.
Consequently the noncontained-core branch is impossible for a full Sylow
image of order q to the fourth. The Sylow branch of (3) now proves Q = UD,
X = Z and both overlap indices equal q, without assuming core containment
or an order-q critical image.

The remaining plane-radical noncontainment contradiction needs the
whole-core displacement and component-radical overlap comparison on p.874.
This module does not assert that exclusion, paired fixed-kernel equality,
critical-pair selection or the field restriction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(2)--(3), printed pp.873--874.
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

private theorem plane_of_root_escape {F : Type*} [Field F] [Finite F]
    (T A B : Subgroup (Sp F)) (hAT : A ≤ T) (hBA : B ≤ A)
    (hBdim : Module.finrank F (displacementSpace B)=1)
    (hBcard : Nat.card B=Nat.card F)
    (hfix : displacementSpace A ≤ TwoLocalCover.fixedSpace T) (hnot : ¬ A ≤ B) :
    Module.finrank F (displacementSpace A)=2 ∧
      TwoLocalCover.fixedSpace T=displacementSpace A ∧
      displacementSpace T=displacementSpace A := by
  have hquad : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
    intro x hx y hy v
    exact hfix (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp A.subtype) ⟨y,hy⟩ v) x (hAT hx)
  have hle := TwoLocalCover.finrank_le_two_of_isotropic (displacementSpace A)
    (quadratic_displacement_isotropic A hquad)
  have hdim : Module.finrank F (displacementSpace A)=2 := by
    by_contra hn
    have hsmall : Module.finrank F (displacementSpace A) ≤ 1 := by omega
    have he : displacementSpace B=displacementSpace A :=
      Submodule.eq_of_le_of_finrank_eq (displacement_mono hBA)
        (le_antisymm (Submodule.finrank_mono (displacement_mono hBA)) (hsmall.trans_eq hBdim.symm))
    apply hnot
    rw [←root_fixedSpace_fixer_eq B hBdim hBcard]
    intro x hx
    apply (mem_fixingSubgroup_iff _).mpr
    intro v hv
    rw [←orthogonal_displacementSpace,he,orthogonal_displacementSpace] at hv
    exact hv x hx
  have hself : (form F).orthogonal (displacementSpace A)=displacementSpace A := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [orthogonal_displacementSpace]
      exact displacementSpace_le_fixedSpace_of_quadratic A hquad
    · rw [LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,hdim]
      simp [Theory.SpecificGroups.SymplecticFour.Vector]
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


open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource

section Covers
variable {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
variable {ρ : Representation (ZMod 2) J W} {C : Subgroup J}

/-- The full common radical on the original ambient cover, now identified
with a plane radical. The full endpoint core remains the actor kernel. -/
structure RadicalPlaneCover (T : Subgroup M) (s : MovedSection ρ C) (n : ℕ)
    (z t : Vertex T) extends AmbientVertexCover T s n z where
  edge_le : Q T t ≤ stabilizer T z
  actor : Q T t →* L (K := field.Carrier)
  actor_marking : ∀ u : Q T t, (equiv.groupEquiv.symm (actor u) : J) =
    quotient (inclusion edge_le u)
  actor_conjugation : ∀ u : Q T t, ∀ w : s.space.toSubmodule,
    embedding (Multiplicative.ofAdd (MovedSection.coverAction s equiv (actor u) w)) =
      u.val*embedding (Multiplicative.ofAdd w)*u.val⁻¹
  actor_kernel : ((commutator (Sp field.Carrier)).subtype.comp actor).ker =
    (Q T z).subgroupOf (Q T t)
  plane_image : ∃ v : Sp field.Carrier,
    ((commutator (Sp field.Carrier)).subtype.comp actor).range.map
      (MulAut.conj v).toMonoidHom = planeRadicalAmbient

/-- The plane image computes the index over the exact full actor kernel. -/
theorem RadicalPlaneCover.radical_index {T : Subgroup M} {s : MovedSection ρ C}
    {n : ℕ} {z t : Vertex T} (cv : RadicalPlaneCover T s n z t) :
    (Q T z).relIndex (Q T t)=(2^n)^3 := by
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,⟨v,hv⟩⟩
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hc : Nat.card α.range=Nat.card E.Carrier^3 := by
    have hh := congrArg (fun A : Subgroup (Sp E.Carrier) => Nat.card A) hv
    rw [card_map_of_injective (MulAut.conj v).injective] at hh
    exact hh.trans SymplecticConjugatePair.card_planeRadical
  rw [←index_ker,hαker,E.card_eq,hE] at hc
  exact hc

end Covers

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The noncontained-core branch of source (3.7)(3) forces the full radical
to be a plane radical on the actual natural cover. Both the opposite-core
and full-radical movement indices are exactly q squared. -/
theorem source_three_noncontained_plane_cover
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    Nonempty (RadicalPlaneCover d.radical (replacementMovedSection h d) n z t) ∧
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)=(2^n)^2 ∧
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)=(2^n)^2 := by
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
  let βA := β.comp (inclusion c.core_le_edge)
  let αA := (commutator (Sp E.Carrier)).subtype.comp βA
  let βZ := β.comp (inclusion hZaT)
  let αZ := (commutator (Sp E.Carrier)).subtype.comp βZ
  have hZaS := hZaT.trans c'.edge_le
  let δ := κ.comp (inclusion hZaS)
  have hother := (replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  have hδcard : Nat.card δ.range=Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZaS κ hκQ).trans
      (hcritical.trans hFc.symm)
  obtain ⟨η,hηcard,hηmark,hηact,hηdim,hηquad⟩ := inner_root_actor_of_field_index path (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ (fun x w => hconj (inclusion hZaS x) w) hδcard (hother.trans hFc.symm)
  have hβmark (u : Q d.radical t) : (e.groupEquiv.symm (β u) : _) =
      κ (inclusion c'.edge_le u) :=
    congrArg Subtype.val (e.groupEquiv.symm_apply_apply (κC (inclusion c'.edge_le u)))
  have hβZ : βZ=η := by
    apply MonoidHom.ext
    intro x
    apply e.groupEquiv.symm.injective
    exact Subtype.ext ((hβmark (inclusion hZaT x)).trans (hηmark x).symm)
  have hZdim : Module.finrank E.Carrier (displacementSpace αZ.range)=1 := by
    have hr : αZ.range=η.range.map (commutator (Sp E.Carrier)).subtype := by
      rw [MonoidHom.range_comp,hβZ]
    rw [hr]
    exact hηdim
  have hZcard : Nat.card αZ.range=Nat.card E.Carrier := by
    rw [MonoidHom.range_comp,hβZ,card_map_of_injective
      (commutator (Sp E.Carrier)).subtype_injective,hηcard]
  have hAT : αA.range ≤ α.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨inclusion c.core_le_edge y,rfl⟩
  have hZA : αZ.range ≤ αA.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨inclusion hZaQ y,rfl⟩
  have hnot' : ¬ αA.range ≤ αZ.range := by
    intro hh
    apply hnot
    intro x hx
    obtain ⟨y,hy⟩ := hh (show αA ⟨x,hx⟩ ∈ αA.range from ⟨⟨x,hx⟩,rfl⟩)
    let u : Q d.radical t := inclusion c.core_le_edge ⟨x,hx⟩ * (inclusion hZaT y)⁻¹
    have hu : u ∈ α.ker := by
      change α u=1
      dsimp only [u]
      rw [map_mul,map_inv]
      change αA ⟨x,hx⟩ * (αZ y)⁻¹=1
      rw [hy,mul_inv_cancel]
    have hq : x*y.val⁻¹ ∈ Q d.radical z :=
      show u ∈ (Q d.radical z).subgroupOf (Q d.radical t) from hαker ▸ hu
    have hh := (Z d.radical a ⊔ Q d.radical z).mul_mem
      (mem_sup_right hq) (mem_sup_left y.property)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (path.end_color.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcomm : ⁅U d.radical z,Q d.radical a⁆ ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    apply ((commutator_mono (U_le_Z z) le_rfl).trans
      (source_two_midpoint_containment h d g hb hsat path hat hzt c c')).trans
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hfix := embedded_displacement_fixed (MovedSection.coverProjection s e) he
    (U d.radical z) (Q d.radical t) (Q d.radical a) c.core_le_edge
    j hj hjr β hact hcomm
  obtain ⟨hAdim,hfixed,hTdisp⟩ := plane_of_root_escape α.range αA.range αZ.range
    hAT hZA hZdim hZcard hfix hnot'
  have hquad : ∀ x ∈ αA.range, ∀ y ∈ αA.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    intro x hx y hy v
    exact hfix (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp αA.range.subtype) ⟨y,hy⟩ v) x (hAT hx)
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
  have hp := plane_radical_of_fixed_plane α.range (displacementSpace αA.range)
    hAdim (quadratic_displacement_isotropic αA.range hquad) hfix hcard
  refine ⟨⟨{ toAmbientVertexCover := ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,
              hfaith,hsemi,hconj,hproj,hker⟩
             edge_le := c'.edge_le
             actor := β
             actor_marking := hβmark
             actor_conjugation := hact
             actor_kernel := hαker
             plane_image := hp }⟩,?_,?_⟩
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U d.radical z) (Q d.radical a) j hj hjr βA
        (fun u w => hact (inclusion c.core_le_edge u) w),hAdim,hFc]
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U d.radical z) (Q d.radical t) j hj hjr β hact,hTdisp,hAdim,hFc]

/-- The incident omega-center is precisely the full-radical fixed part of
Z. Thus its relative index is computed on the original natural cover,
including the entire central attachment. -/
theorem midpoint_relIndex_eq_moving_centralizer
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t) (c : EdgeMarking h d z t) :
    (Z d.radical t).relIndex (Z d.radical z)=
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex (U d.radical z) := by
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (hz.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hZX := g.omega_bound z hz (by
    rw [g.distance_constant z hz]; change 0 < g.b d.radical; omega)
  have hUZ : U d.radical z ≤ Z d.radical z := U_le_Z z
  have hZT : Z d.radical z ≤ Q d.radical t :=
    hZX.trans ((omegaCenter_le _).trans c.core_le_edge)
  have htZ := Sp4Four.edge_Z_le_endpoint d.radical hz hzt
  have hEq : (Z d.radical t).subgroupOf (U d.radical z)=
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical z) := by
    ext u
    constructor
    · intro hu
      exact (mem_omegaCenter_iff.mp (hZt ▸ hu)).2.2
    · intro hu
      change u.val ∈ Z d.radical t
      rw [hZt]
      exact mem_omegaCenter_iff.mpr ⟨hZT (hUZ u.property),
        (mem_omegaCenter_iff.mp (hZX (hUZ u.property))).2.1,hu⟩
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z hz
  let : ((Z d.radical t).subgroupOf (Z d.radical z)).Normal := inferInstance
  calc
    _ = (Z d.radical t).relIndex (U d.radical z ⊔ Z d.radical t) := by
      rw [←Z_eq_moving_sup_edge_of_distance_two h d g hb hz hzt]
    _ = (Z d.radical t).relIndex (U d.radical z) := by
      rw [←relIndex_subgroupOf (sup_le hUZ htZ),subgroupOf_sup hUZ htZ,
        relIndex_sup_right,relIndex_subgroupOf hUZ]
    _ = _ := congrArg Subgroup.index hEq

/-- In the noncontained-core subcase of (3.7)(3), both literal Z-layers
have index q squared over the common midpoint center. The full radical
has order q cubed in the original marked quotient. -/
theorem source_three_noncontained_layers
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    Nonempty (RadicalPlaneCover d.radical (replacementMovedSection h d) n z t) ∧
      (Z d.radical t).relIndex (Z d.radical a)=(2^n)^2 ∧
      (Z d.radical t).relIndex (Z d.radical z)=(2^n)^2 ∧
      Nat.card ((d.ambient.subgroupOf K).map (componentProjection h))=Nat.card F^3 := by
  obtain ⟨⟨cv⟩,hcore,hfull⟩ :=
    source_three_noncontained_plane_cover h d g hb hsat path hat hzt c c' hcritical hnot
  have hzindex : (Z d.radical t).relIndex (Z d.radical z)=(2^n)^2 :=
    (midpoint_relIndex_eq_moving_centralizer h d g hb path.end_color hzt c').trans hfull
  have hcardZ : Nat.card (Z d.radical a)=Nat.card (Z d.radical z) := by
    obtain ⟨u,_,he⟩ := stabilizer_transitive_neighbors d.radical t
      (adjacent_symm d.radical hat) (adjacent_symm d.radical hzt)
    rw [←he,Z_act,card_map_of_injective (MulAut.conj u⁻¹).injective]
  let := finite_Z d.radical a
  let := finite_Z d.radical z
  have htA := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  have htZ := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  let : Finite (Z d.radical t) := Finite.of_injective (inclusion htA) (inclusion_injective _)
  have ha := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical))
    (Z d.radical t) (Z d.radical a) bot_le htA
  have hz := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical))
    (Z d.radical t) (Z d.radical z) bot_le htZ
  rw [relIndex_bot_left,relIndex_bot_left,hcardZ] at ha
  rw [relIndex_bot_left,relIndex_bot_left,hzindex] at hz
  have hindex : (Z d.radical t).relIndex (Z d.radical a)=(2^n)^2 :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (ha.trans hz.symm)
  have hmarked : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h))=Nat.card F^3 := by
    rw [←c'.action_range,←index_ker,c'.action_kernel,h.field_card]
    exact cv.radical_index
  exact ⟨⟨cv⟩,hindex,hzindex,hmarked⟩

/-- The full Sylow branch of source (3.7)(3) is contained: the
noncontained-core calculation would force a cubic full radical image,
contradicting the actual Sylow order q to the fourth. This discharges the
core-containment premise, with both overlap indices and fixed core retained. -/
theorem source_three_of_full_sylow
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (S : Sylow 2 (Sp F)) (hS : (S : Subgroup (Sp F))=c.action.range) :
    Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z ∧
      Q d.radical a=U d.radical a ⊔ fixedCore d.radical a ∧
      X d.radical a=Z d.radical a ∧
      (Z d.radical z).relIndex (Z d.radical a)=2^n ∧
      (Z d.radical a).relIndex (Z d.radical z)=2^n := by
  have hcritical := (critical_indices_eq_field_of_full_sylow h d path hb hat hzt c c' S hS).1
  have hinside : Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z := by
    by_contra hn
    have hc := (source_three_noncontained_layers h d g hb hsat path hat hzt c c'
      hcritical hn).2.2.2
    rw [←c.action_range,←hS] at hc
    have hsyl : Nat.card S=Nat.card F^4 :=
      (Nat.card_congr (Sylow.equiv S
        (unipotentSylow h.field_card (by have := h.nonbinary; omega))).toEquiv).trans card_unipotent
    have hq : 1 < Nat.card F := Finite.one_lt_card
    exact (Nat.pow_lt_pow_right hq (by decide : 3 < 4)).ne (hc.symm.trans hsyl)
  obtain ⟨hQ,hX⟩ := source_three_contained_core h d path hb hat c hcritical hinside
  exact ⟨hinside,hQ,hX,source_three_contained_core_overlap h d path hb hat hzt hcritical hinside⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
