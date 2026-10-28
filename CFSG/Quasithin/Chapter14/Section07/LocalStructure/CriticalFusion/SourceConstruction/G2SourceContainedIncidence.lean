module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceContainedCore

/-!
# Excluding the contained reciprocal point

Extend the natural quotient to a natural/Weyl identification on the same
marked actor. In the nonoffender case the reciprocal core maps to the
natural polar hyperplane. Its commutator with the natural root four is
nonzero and contained in Zα. The root displacement calculation puts it on
the singular point lying on the original seed line, so Zα lies in V. The
previous reciprocal-index argument excludes that containment.

Thus the selected critical actor is an offender. Full-actor reciprocity
then gives Zα not contained in U, completing the contained-point branch
without assuming point noncontainment or a module-identification record.
The faithful action, generalized-Fitting identity, core-commutator identity,
structural and orbit inputs retain their earlier source producers and final
discharge by qt-d-14775-source.

Source: Aschbacher--Smith, 14.7.60--62, printed pp.1067--1068, with the
original setup of 14.7.1, pp.1042--1043. The coordinate conventions retain
the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open Representation.OneCohomology Representation.OneCohomology.CentralCoverOriginalAction

private theorem cover_on_marking
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (J : Subgroup D) [J.Normal]
    (e : J ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (f : D →* Atlas.G2.Model (ZMod 2))
    (hf : ∀ a : J, f a = (e a : Atlas.G2.Model (ZMod 2)))
    (ρ : Representation (ZMod 2) D W)
    (q : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (hq : Function.Surjective q)
    (he : ∀ a v, q (ρ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (q v))
    (hk : q.ker ≤ fixed (ρ.comp J.subtype))
    (hgen : Coinvariants.ker (ρ.comp J.subtype) = ⊤) :
    (∃ E : Atlas.G2.Natural.Space (ZMod 2) ≃ₗ[ZMod 2] W,
      (∀ a v, E (Atlas.G2.Natural.action (ZMod 2) (f a) v) = ρ a (E v)) ∧
      ∀ v, q (E v) = v) ∨
    (∃ E : Atlas.G2.Natural.TraceZero (ZMod 2) ≃ₗ[ZMod 2] W,
      (∀ a v, E (Atlas.G2.Natural.traceZeroAction (ZMod 2) (f a) v) = ρ a (E v)) ∧
      ∀ v, q (E v) = Atlas.G2.Natural.mk (ZMod 2) v) := by
  let α : Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2))) W :=
    (ρ.comp J.subtype).comp e.symm.toMonoidHom
  let p : α.IntertwiningMap (Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2)) :=
    q.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro a v
      change q (ρ (e.symm a) v) = Atlas.G2.Natural.action (ZMod 2) a (q v)
      rw [he,hf,e.apply_symm_apply])
  have hp : IsCover p := by
    refine ⟨hq,fun v hv a => hk hv (e.symm a),?_⟩
    exact (commutator_comp_equiv (ρ.comp J.subtype) e.symm).trans hgen
  obtain ⟨s,hs,hover⟩ := Atlas.G2.Natural.OrthogonalCover.exists_quotient (ZMod 2) p hp
  let ζ := (Atlas.G2.Natural.traceZeroAction (ZMod 2)).comp f
  let η := (Atlas.G2.Natural.action (ZMod 2)).comp f
  have hζ : ζ.comp J.subtype =
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)).comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro v
    change Atlas.G2.Natural.traceZeroAction (ZMod 2) (f a) v =
      Atlas.G2.Natural.traceZeroAction (ZMod 2) (e a) v
    rw [hf]
  have hζgen : Coinvariants.ker (ζ.comp J.subtype) = ⊤ := by
    rw [hζ,commutator_comp_equiv,Atlas.G2.Natural.OrthogonalCover.commutator_eq_top]
  have hsJ (a : J) (v) : s (ζ a v) = ρ a (s v) := by
    have hh := LinearMap.congr_fun (s.isIntertwining' (e a)) v
    change s (Atlas.G2.Natural.traceZeroAction (ZMod 2) (e a) v) =
      ρ (e.symm (e a)) (s v) at hh
    simpa only [ζ,MonoidHom.comp_apply,hf,e.symm_apply_apply] using hh
  have hsD := quotient_original_equivariant J (η := η) (ζ := ζ) (τ := ρ)
    (Atlas.G2.Natural.mk (ZMod 2)) q s.toLinearMap (fun _ _ => rfl)
    he hk hζgen hsJ hover
  have hlo : 6 ≤ Module.finrank (ZMod 2) W := by
    simpa only [Atlas.G2.Natural.finrank_space] using LinearMap.finrank_le_finrank_of_surjective hq
  have hhi : Module.finrank (ZMod 2) W ≤ 7 := by
    simpa only [Atlas.G2.Natural.OrthogonalCover.finrank_traceZero] using
      LinearMap.finrank_le_finrank_of_surjective hs
  by_cases hd : Module.finrank (ZMod 2) W = 6
  · have hi : Function.Injective q :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (hd.trans (Atlas.G2.Natural.finrank_space (ZMod 2)).symm)).mpr hq
    let E := (LinearEquiv.ofBijective q ⟨hi,hq⟩).symm
    have hE (v) : q (E v) = v := (LinearEquiv.ofBijective q ⟨hi,hq⟩).apply_symm_apply v
    exact Or.inl ⟨E,fun a v => hi (by rw [hE,he,hE]),hE⟩
  · have hd : Module.finrank (ZMod 2) W = 7 := by omega
    have hi : Function.Injective s :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        ((Atlas.G2.Natural.OrthogonalCover.finrank_traceZero (ZMod 2)).trans hd.symm)).mpr hs
    exact Or.inr ⟨LinearEquiv.ofBijective s.toLinearMap ⟨hi,hs⟩,hsD,hover⟩

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

include c in
theorem source_cover_on_marking
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Injective f)
    (q : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2)) (hq : Function.Surjective q)
    (he : ∀ a v, q (σ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (q v))
    (hfix : ∀ a v, σ a v = v ↔
      Atlas.G2.Natural.action (ZMod 2) (f a) (q v) = q v) :
    (∃ E : Atlas.G2.Natural.Space (ZMod 2) ≃ₗ[ZMod 2] W,
      (∀ a v, E (Atlas.G2.Natural.action (ZMod 2) (f a) v) = σ a (E v)) ∧
      ∀ v, q (E v) = v) ∨
    (∃ E : Atlas.G2.Natural.TraceZero (ZMod 2) ≃ₗ[ZMod 2] W,
      (∀ a v, E (Atlas.G2.Natural.traceZeroAction (ZMod 2) (f a) v) = σ a (E v)) ∧
      ∀ v, q (E v) = Atlas.G2.Natural.mk (ZMod 2) v) := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let J := star F (K F)
  let : J.Normal := by
    change (star F (K F)).Normal
    exact hfit ▸ inferInstance
  let e₀ : J ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
    (Chapter13.Section08.Components.componentStarEquiv F.H (K F)
      (map_subtype_le _) hcomponent).symm.trans eK
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := e₀.symm.toMonoidHom) e₀.symm.surjective
  have hmap : J.map f = commutator (Atlas.G2.Model (ZMod 2)) := by
    apply Subgroup.eq_of_le_of_card_ge
    · have hh := _root_.map_commutator_eq J (f.comp J.subtype)
      rw [Group.IsPerfect.commutator_eq_top,←MonoidHom.range_eq_map,MonoidHom.range_comp,
        range_subtype] at hh
      rw [hh]
      exact commutator_mono le_top le_top
    · rw [card_map_of_injective hf]
      exact (Nat.card_congr e₀.toEquiv).ge
  let e : J ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
    (J.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hmap)
  apply cover_on_marking J e f (fun _ => rfl) σ q hq he
  · intro v hv a
    apply (hfix a v).mpr
    rw [show q v = 0 from hv,map_zero]
  · rw [←subspaceCommutator_top_eq_coinvariants]
    exact full_star_commutator c h

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open G2Exclusion.MarkedGeometry G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit

private theorem line_in_distinguishedPlane_incident (L : ZeroProductLine (ZMod 2))
    (hL : L.val ≤ distinguishedPlane) : pointOnLine firstPoint L := by
  rw [firstPoint_on_line_iff]
  by_contra hn
  let p : L.val →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    (LinearMap.pi ![LinearMap.proj 1,LinearMap.proj 2]).comp L.val.subtype
  have hi : Function.Injective p := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    have h1 : x.val 1 = 0 := congrFun hx 0
    have h2 : x.val 2 = 0 := congrFun hx 1
    have he : x.val = (x.val 0) • basisVector 0 := by
      rw [distinguishedPlane_coordinates (hL x.property)]
      ext j
      fin_cases j <;> simp [basisVector,h1,h2]
    have h0 : x.val 0 = 0 := by
      by_contra hh
      have hh' : x.val 0 = 1 := ((by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) _).resolve_left hh
      have hx' := x.property
      rw [he,hh',one_smul] at hx'
      exact hn hx'
    change x = 0
    apply Subtype.ext
    change x.val = 0
    simpa only [h0,zero_smul] using he
  have hs : Function.Surjective p :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using L.property.1)).mp hi
  obtain ⟨x,hx⟩ := hs ![1,0]
  obtain ⟨y,hy⟩ := hs ![0,1]
  have hzero := L.property.2 x.val x.property y.val y.property
  rw [distinguishedPlane_mul (hL x.property) (hL y.property)] at hzero
  have h1 : x.val 1 = 1 := congrFun hx 0
  have h2 : x.val 2 = 0 := congrFun hx 1
  have k1 : y.val 1 = 0 := congrFun hy 0
  have k2 : y.val 2 = 1 := congrFun hy 1
  have hz := congrFun hzero 0
  simp [h1,h2,k1,k2,basisVector] at hz

private theorem root_mem_natural (a b : ZMod 2) : rootActor a b 0 ∈ BinaryCore.natural := by
  rw [← elementary_inf_derived]
  exact ⟨⟨⟨a,b,0,0,0⟩,⟨rfl,rfl⟩,rfl⟩,(rootActor_mem_derived a b 0).mpr rfl⟩

/-- A singular line fixed by the natural four-group passes through its marked point. -/
private theorem model_fixed_line_incident (m : BinaryG2Module) (L : ZeroProductLine (ZMod 2))
    (hL : m.singularMap.line L ≤ fixedSpace m.action BinaryCore.natural) :
    pointOnLine firstPoint L := by
  apply line_in_distinguishedPlane_incident L
  intro x hx
  obtain ⟨ht,hn⟩ := CosetIdentification.line_singular L x hx
  let v : TraceZero (ZMod 2) := ⟨x,ht⟩
  have hm : m.singularMap.Equivariant m.action := by
    cases m with
    | natural => exact naturalMap_equivariant
    | weyl => exact weylMap_equivariant
  have hfixed (g : Model (ZMod 2)) (hg : g ∈ BinaryCore.natural) : g.val x = x := by
    have he := hL (show m.singularMap.linear v ∈ m.singularMap.line L from ⟨v,hx,rfl⟩) ⟨g,hg⟩
    change m.action g (m.singularMap.linear v) = m.singularMap.linear v at he
    rw [hm] at he
    have hv := m.singularMap.separates (traceZeroAction (ZMod 2) g v) v
      ((automorphism_norm g x).trans hn) hn he
    exact congrArg Subtype.val hv
  have ha := hfixed (rootActor 1 0 0) (root_mem_natural 1 0)
  have hb := hfixed (rootActor 0 1 0) (root_mem_natural 0 1)
  rw [rootActor_apply] at ha hb
  have h6 : x 6 = 0 := by simpa using congrFun ha 0
  have h5 : x 5 = 0 := by simpa using congrFun hb 0
  have h7 : x 7 = 0 := by simpa using congrFun ha 1
  have h4 : x 4 = x 3 := by
    change x 3 + x 4 = 0 at ht
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right ht
  have h3 : x 3 = 0 := by
    have hh : x 3 * x 3 = 0 := by simpa [Atlas.SplitOctonion.norm,h4,h5,h6,h7] using hn
    exact (mul_self_eq_zero.mp hh)
  intro i hi
  fin_cases i <;> simp_all

/-- The natural quotient, retaining the scalar kernel in the Weyl case. -/
private def modelNaturalProjection : (m : BinaryG2Module) → m.Space →ₗ[ZMod 2] Natural.Space (ZMod 2)
  | .natural => LinearMap.id
  | .weyl => Natural.mk (ZMod 2)

private theorem model_lift (m : BinaryG2Module) (v : m.Space) :
    ∃ x : TraceZero (ZMod 2), m.singularMap.linear x = v := by
  cases m with
  | natural => exact mk_surjective (ZMod 2) v
  | weyl => exact ⟨v,rfl⟩

/-- On the natural polar hyperplane, every displacement by the root four
lies on the actual singular point, including in the Weyl module. -/
private theorem model_hyperplane_displacement (m : BinaryG2Module)
    (g : Model (ZMod 2)) (hg : g ∈ BinaryCore.natural) (v : m.Space)
    (hv : Restricted.NaturalCoordinates.equiv (ZMod 2) (modelNaturalProjection m v) ∈
      Natural.BinaryPointFlag.hyperplane) :
    m.action g v - v ∈ m.singularMap.point firstPoint := by
  obtain ⟨x,rfl⟩ := model_lift m v
  have hx7 : x.val 7 = 0 := by
    have hh := (Natural.BinaryPointFlag.mem_hyperplane _).mp hv
    cases m <;> exact hh
  obtain ⟨a,⟨hc,hd,he⟩,rfl⟩ := hg
  have ha : a = ⟨a.a,a.b,0,0,0⟩ := by cases a; simp_all
  rw [ha]
  have hdisp : traceZeroAction (ZMod 2) (rootActor a.a a.b 0) x - x =
      (a.a*x.val 6+a.b*x.val 5) • (⟨basisVector 0,by simp [trace,basisVector]⟩ : TraceZero (ZMod 2)) := by
    apply Subtype.ext
    change (rootActor a.a a.b 0).val x.val - x.val = _
    rw [rootActor_apply]
    ext j
    fin_cases j <;> simp [hx7,basisVector]
    ring
  have hmem : traceZeroAction (ZMod 2) (rootActor a.a a.b 0) x - x ∈
      traceRestriction firstPoint.val.submodule := by
    rw [hdisp]
    apply Submodule.smul_mem
    simp only [traceRestriction,Submodule.mem_comap]
    change (basisVector (F := ZMod 2) 0 : Carrier (ZMod 2)) ∈ firstPoint.val.submodule
    change basisVector 0 ∈ (Projectivization.mk (ZMod 2) (basisVector 0) first_basis_ne_zero).submodule
    rw [Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self _
  change m.action (rootActor a.a a.b 0) (m.singularMap.linear x) - m.singularMap.linear x ∈ _
  rw [m.equivariant,←map_sub]
  exact Submodule.mem_map_of_mem hmem

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

omit [Finite G] in
private theorem model_image_of_quotient_image
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (B : Subgroup G) (P : Submodule (ZMod 2) m.Space)
    (hB : letI := c.kernel_normal
      (B.subgroupOf F.U).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) =
        P.toAddSubgroup.toSubgroup.map (literalModuleEquiv c m E).toMonoidHom) :
    c.imageSpace B = P.map E.toLinearMap := by
  let := c.kernel_normal
  apply Submodule.toAddSubgroup_injective
  apply AddSubgroup.toSubgroup.injective
  have hh := congrArg (Subgroup.map c.quotientEquiv.toMonoidHom) hB
  rw [map_map,map_map] at hh
  have hq : c.quotientEquiv.toMonoidHom.comp
      (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) = c.coordinates := by
    ext u
    exact c.quotientEquiv_mk u
  have hm : c.quotientEquiv.toMonoidHom.comp (literalModuleEquiv c m E).toMonoidHom =
      E.toAddEquiv.toMultiplicative.toMonoidHom := by
    ext v
    exact c.quotientEquiv.apply_symm_apply _
  rw [hq,hm] at hh
  exact hh

/-- The original seed is a line on the supplied equivariant model marking. -/
theorem source_seed_line_on_marking
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Injective f)
    (hJ : commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v)) :
    ∃ l : ZeroProductLine (ZMod 2), c.imageSpace V = (m.singularMap.line l).map E.toLinearMap := by
  let := h.chosen.elementary
  let := internalModuleAction c f m E
  obtain ⟨p,hp,_⟩ := marked_geometry_of_recognition c h f hf hJ m E he
    Atlas.G2.Natural.BinaryModelOffenders.rank_le_two
    (fun A hA hr => by have hh := model_small_rank_bound m A hA (by omega); omega)
    (fun A _ hA hr => by have hh := model_small_rank_bound m A hA (by omega); omega)
    (model_bestOffender m)
  obtain ⟨l,hl,_⟩ := (original_marked_points c m E p hp.point hp.line).2
  exact ⟨l,model_image_of_quotient_image c m E V (m.singularMap.line l) hl⟩

private theorem source_point_le_seed_of_hyperplane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Injective f)
    (hJ : commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range)
    (q : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (heq : ∀ a v, q (σ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (q v))
    (hA : (star F path.Uα).map f = Atlas.G2.BinaryCore.natural)
    (hhyper : (c.imageSpace (F.U ⊓ path.Qα)).map
      ((Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)).toLinearMap.comp q) =
      Atlas.G2.Natural.BinaryPointFlag.hyperplane)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v))
    (hproj : ∀ v, q (E v) = modelNaturalProjection m v) : path.Zα ≤ V := by
  let D := F.U ⊓ path.Qα
  let r := (Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)).toLinearMap.comp q
  let C := ⁅path.Uα,D⁆
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hCZ : C ≤ path.Zα := by
    dsimp only [C]
    rw [commutator_comm]
    exact (commutator_mono inf_le_right le_rfl).trans (reciprocal_core_commutator c path)
  have hCi : c.imageSpace C = subspaceCommutator σ (c.imageSpace D) (star F path.Uα) := by
    rw [c.imageSpace_commutator path.Uα D hAH inf_le_left,subspaceCommutator_comp_map]
    rfl
  have hCn : C ≠ ⊥ := by
    intro hz
    have hv : (Pi.single 4 1 : Fin 6 → ZMod 2) ∈ (c.imageSpace D).map r := by
      rw [hhyper]
      simp
    obtain ⟨v,hv,hrv⟩ := hv
    have ha : Atlas.G2.rootA (1 : ZMod 2) ∈ (star F path.Uα).map f := by
      rw [hA]
      exact Atlas.G2.BinaryCore.z_mem_natural
    obtain ⟨a,ha,hfa⟩ := ha
    have hd : σ a v-v ∈ c.imageSpace C := by
      rw [hCi]
      exact Submodule.subset_span ⟨a,ha,v,hv,rfl⟩
    have hzero : σ a v-v = 0 := by
      rw [hz] at hd
      obtain ⟨u,hu,huv⟩ := (c.mem_imageSpace_iff _ _).mp hd
      have hu1 : u = 1 := Subtype.ext hu
      simpa [hu1] using huv.symm
    have hract (a) (v) : r (σ a v) =
        Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) (f a) (r v) := by
      change Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2) (q (σ a v)) = _
      rw [heq]
      exact LinearMap.congr_fun
        ((Atlas.G2.Restricted.NaturalCoordinates.repEquiv (ZMod 2)).isIntertwining' (f a)) (q v)
    have hh := congrArg r hzero
    rw [map_sub,hract,hfa,hrv,map_zero] at hh
    have hh0 := congrFun hh 0
    simp at hh0
  have hCeq : C = path.Zα := by
    have hcard : Nat.card path.Zα = 2 := by
      rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj _).injective]
      simpa using F.card 1 (by decide)
    let : Fact (Nat.card path.Zα).Prime := ⟨by rw [hcard]; decide⟩
    rcases (C.subgroupOf path.Zα).eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hh := congrArg (Subgroup.map path.Zα.subtype) hb
      rw [map_subgroupOf_eq_of_le hCZ,Subgroup.map_bot] at hh
      exact (hCn hh).elim
    · have hh := congrArg (Subgroup.map path.Zα.subtype) ht
      rw [map_subgroupOf_eq_of_le hCZ,←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
  obtain ⟨l,hl⟩ := source_seed_line_on_marking c h f hf hJ m E he
  have hlf : m.singularMap.line l ≤ fixedSpace m.action Atlas.G2.BinaryCore.natural := by
    intro v hv a
    have hav : (a : Atlas.G2.Model (ZMod 2)) ∈ (star F path.Uα).map f := by
      rw [hA]
      exact a.property
    obtain ⟨b,hb,hfb⟩ := hav
    obtain ⟨b,hb,rfl⟩ := hb
    apply E.injective
    change E (m.action (a : Atlas.G2.Model (ZMod 2)) v) = E v
    rw [←hfb,he]
    have hv' : E v ∈ c.imageSpace V := hl ▸ Submodule.mem_map_of_mem hv
    exact c.fixed_on_imageSpace_of_commutator_le (F.Ri L 1) V
      (LocalReduction.point_core_commutator_seed h) b (hplace hb) _ hv'
  have hlpoint := (m.singularMap.incidence Atlas.G2.firstPoint l).mp (model_fixed_line_incident m l hlf)
  have himage : c.imageSpace C ≤ c.imageSpace V := by
    rw [hCi]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,hv,rfl⟩
    have hvhyper : r v ∈ Atlas.G2.Natural.BinaryPointFlag.hyperplane :=
      hhyper ▸ Submodule.mem_map_of_mem hv
    have hmhyper : Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)
        (modelNaturalProjection m (E.symm v)) ∈ Atlas.G2.Natural.BinaryPointFlag.hyperplane := by
      rw [←hproj,E.apply_symm_apply]
      exact hvhyper
    have hdisp := model_hyperplane_displacement m (f a)
      (hA ▸ mem_map_of_mem f ha) (E.symm v) hmhyper
    rw [hl]
    refine ⟨m.action (f a) (E.symm v)-E.symm v,hlpoint hdisp,?_⟩
    rw [map_sub]
    change E (m.action (f a) (E.symm v))-E (E.symm v) = σ a v-v
    rw [he,E.apply_symm_apply]
  have hCU : C ≤ F.U := (le_normalizer_iff_commutator_le_right.mp
    (hAH.trans c.normalized)).trans' (commutator_mono le_rfl inf_le_left)
  rw [←hCeq]
  intro x hx
  have hv := himage ((c.mem_imageSpace_iff C _).mpr ⟨⟨x,hCU hx⟩,hx,rfl⟩)
  have hh := (c.coordinates_mem_imageSpace_iff V (le_conjugateSpanBy V F.H) ⟨x,hCU hx⟩).mp hv
  simpa only [sup_eq_left.mpr (F.le_seed 1)] using hh


open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

include c in
/-- The original selected critical actor is an offender; the contained-point
incidence calculation discharges the nonoffender branch of 14.7.61. -/
theorem source_critical_offender
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) : IsOffender σ (star F path.Uα) := by
  by_contra hn
  obtain ⟨_,_,f,q,hf',hJ,hq,heq,hfix,_,hA,hhyper,_⟩ :=
    source_nonoffender_core_hyperplane c h hab hcomponent hfit eK structural hf hcomm
      P hP orbit path hplace selection hn
  have hZV : path.Zα ≤ V := by
    rcases source_cover_on_marking c h hcomponent hfit eK f hf' q hq heq hfix with
      ⟨E,he,hproj⟩ | ⟨E,he,hproj⟩
    · exact source_point_le_seed_of_hyperplane c h path hplace f hf' hJ q heq hA hhyper
        .natural E he hproj
    · exact source_point_le_seed_of_hyperplane c h path hplace f hf' hJ q heq hA hhyper
        .weyl E he hproj
  exact source_critical_point_not_le_seed c h hab hcomponent hfit eK structural hf hcomm
    P hP orbit path hplace selection hZV

include c in
/-- The point cannot lie in the whole original span, with the contained-point
branch now discharged and no local actor marking assumed. -/
theorem source_critical_point_not_le_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) : ¬ path.Zα ≤ F.U := by
  have ho := source_critical_offender c h hab hcomponent hfit eK structural hf hcomm
    P hP orbit path hplace selection
  obtain ⟨hq,hb⟩ := source_selected_critical_bound c h hab structural hf path selection
  obtain ⟨f,hf',_,hm⟩ := source_natural_or_weyl c h hab hcomponent hfit eK hf
    P hP orbit path hplace selection hq hb
  have hmodel : ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      ∀ a v, E (m.action (f a) v) = σ a (E v) := by
    rcases hm with ⟨E,he⟩ | ⟨E,he⟩
    · exact ⟨.natural,E,he⟩
    · exact ⟨.weyl,E,he⟩
  obtain ⟨m,E,he⟩ := hmodel
  obtain ⟨p,hA⟩ := model_offender_fullCentralizer m _
    (ho.map_equivariant σ m.action f hf' E.symm
      (fun a v => by rw [←E.apply_symm_apply v,←he,E.symm_apply_apply,E.symm_apply_apply]))
  exact (source_full_actor_reciprocity c h hab hcomponent hfit eK structural hf hcomm
    path hplace selection m E f hf' he p hA).2.1


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
