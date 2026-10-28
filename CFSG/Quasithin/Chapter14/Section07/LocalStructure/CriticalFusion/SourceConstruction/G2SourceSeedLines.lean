module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceContainedIncidence

/-!
# The reciprocal family consists of actual seed conjugates

Full natural L-action sends any two nonzero seed vectors to one another.
Consequently an ambient conjugate of V through V₁ is already an H-conjugate,
and is a line in the original natural/Weyl geometry. Model line transitivity
proves the converse, retaining the literal kernel V₁.

Apply this to each commutator four-group of the selected critical actor.
Joining it to V₁ gives an actual seed conjugate. The proved equality of
reciprocal ambient families gives the same conclusion after joining to Zα.
The final theorem constructs both markings, their common family, both
noncontainments and these seed conjugates from the original source inputs;
it includes no assumed marking or point-noncontainment premise.

The quotient four-cycle and residual exclusion remain for the final source
assembly. Earlier faithful, structural, orbit, generalized-Fitting and
core-commutator inputs retain their existing producers and final discharge
by qt-d-14775-source.

Source: Aschbacher--Smith, 14.7.61--62 and formulas (a),(d),(a′), printed
pp.1068--1069. Model conventions retain LICENSES/ATLAS.txt attribution.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A seed conjugate through the original point is already conjugate under
its actual point centralizer. -/
theorem seed_conjugate_through_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (g : G) (hpoint : F.Vi 1 ≤ conjugate V g) :
    ∃ a : F.H, conjugate V g = conjugate V a := by
  obtain ⟨z,hz,hzgen⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzV : z ∈ V := F.le_seed 1 (hzgen.symm ▸ mem_zpowers z)
  have hzg : g*z*g⁻¹ ∈ V := by
    obtain ⟨v,hv,he⟩ := hpoint (hzgen.symm ▸ mem_zpowers z)
    simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] at he
    have hh := congrArg (fun x : G => g*x*g⁻¹) he
    have he' : v = g*z*g⁻¹ := by
      simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh
    exact he' ▸ hv
  have hgne : g*z*g⁻¹ ≠ 1 := by
    intro he
    apply hz
    have hh := congrArg (fun x : G => g⁻¹*x*g) he
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,mul_one,inv_mul_cancel] using hh
  obtain ⟨l,hl,_,hswap⟩ := vector_interchange h hzV hzg hz hgne
  have ha : l*g ∈ F.H := by
    rw [F.H_eq_centralizer (by decide) z hzgen,mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (l*g)*z*(l*g)⁻¹ = l*(g*z*g⁻¹)*l⁻¹ := by group
      _ = z := hswap
  refine ⟨⟨l*g,ha⟩,?_⟩
  change V.conjBy g⁻¹ = V.conjBy (l*g)⁻¹
  rw [mul_inv_rev,conjBy_mul]
  have hn : V.conjBy l⁻¹ = V :=
    mem_normalizer_iff_map_conj_eq.mp (h.chosen.normalizes (L.inv_mem hl))
  rw [hn]


open Representation Representation.BinaryOffender
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

/-- Every ambient seed conjugate through the original point gives a line in
the same original module geometry, with its coordinates retained. -/
theorem source_conjugate_seed_line
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Injective f)
    (hJ : commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v))
    (g : G) (hpoint : F.Vi 1 ≤ conjugate V g) :
    conjugate V g ≤ F.U ∧ ∃ l : ZeroProductLine (ZMod 2),
      c.imageSpace (conjugate V g) = (m.singularMap.line l).map E.toLinearMap := by
  obtain ⟨a,ha⟩ := seed_conjugate_through_point h g hpoint
  rw [ha]
  constructor
  · rintro x ⟨v,hv,rfl⟩
    exact (mem_normalizer_iff.mp (c.normalized a⁻¹.property) v).mp
      (le_conjugateSpanBy V F.H hv)
  · obtain ⟨l,hl⟩ := source_seed_line_on_marking c h f hf hJ m E he
    refine ⟨f (starMap F a⁻¹) • l,?_⟩
    change c.imageSpace (V.conjBy ((a⁻¹ : F.H) : G)) = _
    rw [c.imageSpace_conjBy V (le_conjugateSpanBy V F.H) a⁻¹,hl,
      m.singularMap.line_equivariant m.action m.equivariant,
      ←Submodule.map_comp,←Submodule.map_comp]
    congr 1
    ext v
    exact (he _ v).symm


/-- Every geometric line is the image of an actual H-conjugate of the seed. -/
theorem source_line_is_seed_conjugate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Bijective f)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v))
    (l : ZeroProductLine (ZMod 2)) :
    ∃ a : F.H, c.imageSpace (conjugate V a) = (m.singularMap.line l).map E.toLinearMap := by
  have hJ : commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range := by
    rw [MonoidHom.range_eq_top.mpr hf.2]
    exact le_top
  obtain ⟨l₀,hl₀⟩ := source_seed_line_on_marking c h f hf.1 hJ m E he
  obtain ⟨g₀,hg₀⟩ := CosetIdentification.exists_line_translate l₀
  obtain ⟨g₁,hg₁⟩ := CosetIdentification.exists_line_translate l
  obtain ⟨a,ha⟩ := hf.2 (g₁*g₀⁻¹)
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) a
  have hmove : f (starMap F a) • l₀ = l := by
    change f (QuotientGroup.mk' (pCore 2 F.H) a) • l₀ = l
    rw [ha,←hg₀,mul_smul,inv_smul_smul,hg₁]
  refine ⟨a⁻¹,?_⟩
  change c.imageSpace (V.conjBy ((a : G)⁻¹)⁻¹) = _
  rw [inv_inv,c.imageSpace_conjBy V (le_conjugateSpanBy V F.H) a,hl₀,←hmove,
    m.singularMap.line_equivariant m.action m.equivariant,
    ←Submodule.map_comp,←Submodule.map_comp]
  congr 1
  ext v
  exact (he _ v).symm

omit [Finite G] in
private theorem seed_conjugate_contains_point (a : F.H) : F.Vi 1 ≤ conjugate V a := by
  have hp : (F.Vi 1).conjBy (a : G)⁻¹ = F.Vi 1 :=
    mem_normalizer_iff_map_conj_eq.mp a⁻¹.property
  have hh := map_mono (f := (MulAut.conj (a:G)⁻¹).toMonoidHom) (F.le_seed 1)
  exact hp ▸ hh

/-- A subgroup above the original point whose quotient is a geometric line
is an actual conjugate of V. This retains the literal denominator. -/
theorem source_line_preimage_is_seed_conjugate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Bijective f)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v))
    (B : Subgroup G) (hBU : B ≤ F.U) (hPB : F.Vi 1 ≤ B)
    (l : ZeroProductLine (ZMod 2))
    (hB : c.imageSpace B = (m.singularMap.line l).map E.toLinearMap) :
    ∃ a : F.H, B = conjugate V a := by
  obtain ⟨a,ha⟩ := source_line_is_seed_conjugate c h f hf m E he l
  have hCU : conjugate V a ≤ F.U := by
    rintro x ⟨v,hv,rfl⟩
    exact (mem_normalizer_iff.mp (c.normalized a⁻¹.property) v).mp
      (le_conjugateSpanBy V F.H hv)
  have hPC := seed_conjugate_contains_point a
  have hi : c.imageSpace B = c.imageSpace (conjugate V a) := hB.trans ha.symm
  refine ⟨a,le_antisymm ?_ ?_⟩
  · intro x hx
    have hx' := (c.mem_imageSpace_iff B _).mpr ⟨⟨x,hBU hx⟩,hx,rfl⟩
    rw [hi] at hx'
    have hh := (c.coordinates_mem_imageSpace_iff (conjugate V a) hCU ⟨x,hBU hx⟩).mp hx'
    simpa only [sup_eq_left.mpr hPC] using hh
  · intro x hx
    have hx' := (c.mem_imageSpace_iff (conjugate V a) _).mpr ⟨⟨x,hCU hx⟩,hx,rfl⟩
    rw [←hi] at hx'
    have hh := (c.coordinates_mem_imageSpace_iff B hBU ⟨x,hCU hx⟩).mp hx'
    simpa only [sup_eq_left.mpr hPB] using hh

open G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

include c in
/-- Formula (a): every nontrivial commutator four-group, joined with V₁,
is an actual conjugate of the original seed on the same critical marking. -/
theorem source_commutator_seed_conjugate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Bijective f)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map f = fullCentralizer m.singularMap m.action p)
    (hpoint : ¬ F.Vi 1 ≤ path.Uα)
    (b : G) (hb : b ∈ derivedActorLift (f.comp (starMap F)) path.Uα)
    (hne : ⁅F.U,zpowers b⁆ ≠ ⊥) :
    ∃ a : F.H, ⁅F.U,zpowers b⁆ ⊔ F.Vi 1 = conjugate V a := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hθ : (path.Uα.subgroupOf F.H).map (f.comp (starMap F)) =
      fullCentralizer m.singularMap m.action p := by
    rw [←map_map]
    exact hA
  obtain ⟨l,_,hi,_⟩ := source_commutator_line c h path hplace m E
    (f.comp (starMap F)) (fun a v => he (starMap F a) v) p
    (derivedActorLift (f.comp (starMap F)) path.Uα) (derivedActorLift_le _ _)
    hpoint (derivedActorLift_image _ m p _ hθ) b hb hne
  have hbA : b ∈ path.Uα := derivedActorLift_le _ _ hb
  have hCU : ⁅F.U,zpowers b⁆ ≤ F.U :=
    le_normalizer_iff_commutator_le_left.mp
      ((zpowers_le.mpr (hAH hbA)).trans c.normalized)
  apply source_line_preimage_is_seed_conjugate c h f hf m E he
    (⁅F.U,zpowers b⁆ ⊔ F.Vi 1) (sup_le hCU c.kernel_le) le_sup_right l
  rw [imageSpace_sup_point c _ hCU]
  exact hi


open G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

include c in
/-- The same reciprocal critical actors and literal common family, with
point noncontainment proved from the original source inputs. -/
theorem source_reciprocal_geometry
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
    (selection : path.RankSelection) :
    ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Bijective i ∧
      commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range ∧
    ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      (∀ a v, E (m.action (i a) v) = σ a (E v)) ∧
    ∃ (p : Atlas.G2.SingularPoints (ZMod 2)) (r : SourceReversal.Geometry path)
      (q : Atlas.G2.SingularPoints (ZMod 2)),
      (star F path.Uα).map i = fullCentralizer m.singularMap m.action p ∧
      r.path.RankSelection ∧ r.path.Uα ≤ F.Ri L 1 ∧
      (star F r.path.Uα).map i = fullCentralizer m.singularMap m.action q ∧
      (¬ F.Vi 1 ≤ path.Uα) ∧ (¬ F.Vi 1 ≤ r.path.Uα) ∧
      ({C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα,
        C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
        C = conjugate ⁅F.U,zpowers b⁆ r.conjugator}) ∧
      ∀ C : Subgroup G, C ≠ ⊥ →
        (∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα, C = ⁅F.U,zpowers b⁆) →
        Nat.card C = 4 ∧ C ≤ F.U ∧ C ≤ path.Uα ∧
          (∃ a : F.H, C ⊔ F.Vi 1 = conjugate V a) ∧
          (∃ g : G, C ⊔ path.Zα = conjugate V g) := by
  obtain ⟨i,hi,hJ,m,E,he,hrest⟩ := source_recognized_reciprocal_family
    c h hab hcomponent hfit eK structural hf hcomm P hP orbit path hplace selection
    (source_critical_point_not_le_span c h hab hcomponent hfit eK structural hf hcomm
      P hP orbit path hplace selection)
  have hs := G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.source_full_actor_of_ff
    σ m.action i hi E.symm
    (fun a v => by rw [←E.apply_symm_apply v,←he,E.symm_apply_apply,E.symm_apply_apply]) hJ
    Atlas.G2.Natural.BinaryModelOffenders.rank_le_two
    (fun A hA hr => by have hh := model_small_rank_bound m A hA (by omega); omega)
    (fun A _ hA hr => by have hh := model_small_rank_bound m A hA (by omega); omega)
    ⟨star F path.Uα,source_critical_offender c h hab hcomponent hfit eK structural hf hcomm
      P hP orbit path hplace selection⟩
  obtain ⟨p,r,q,hA,hrs,hrplace,hrA,hpoint,hrpoint,hfamily⟩ := hrest
  refine ⟨i,⟨hi,hs.1⟩,hJ,m,E,he,p,r,q,hA,hrs,hrplace,hrA,hpoint,hrpoint,hfamily,?_⟩
  intro C hC hCb
  have hreverse : C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
      C = conjugate ⁅F.U,zpowers b⁆ r.conjugator := by
    change C ∈ {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
      C = conjugate ⁅F.U,zpowers b⁆ r.conjugator}
    rw [←hfamily]
    exact ⟨hC,hCb⟩
  obtain ⟨_,b',hb',hCe⟩ := hreverse
  have hn' : ⁅F.U,zpowers b'⁆ ≠ ⊥ := by
    intro hz
    apply hC
    rw [hCe,hz]
    exact map_bot _
  obtain ⟨a,ha⟩ := source_commutator_seed_conjugate c h r.path hrplace i ⟨hi,hs.1⟩
    m E he q hrA hrpoint b' hb' hn'
  have hsecond : ∃ g : G, C ⊔ path.Zα = conjugate V g := by
    refine ⟨(a:G)*r.conjugator,?_⟩
    have hh := congrArg (fun D : Subgroup G => conjugate D r.conjugator) ha
    change (⁅F.U,zpowers b'⁆ ⊔ F.Vi 1).map _ = _ at hh
    rw [Subgroup.map_sup] at hh
    change conjugate ⁅F.U,zpowers b'⁆ r.conjugator ⊔
      conjugate (F.Vi 1) r.conjugator = _ at hh
    rw [r.base_point,←hCe] at hh
    refine hh.trans ?_
    change (V.conjBy (a:G)⁻¹).conjBy r.conjugator⁻¹ = V.conjBy ((a:G)*r.conjugator)⁻¹
    rw [←conjBy_mul,mul_inv_rev]
  obtain ⟨b,hb,rfl⟩ := hCb
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hθ : (path.Uα.subgroupOf F.H).map (i.comp (starMap F)) =
      fullCentralizer m.singularMap m.action p := by rw [←map_map]; exact hA
  obtain ⟨_,_,_,hc⟩ := source_commutator_line c h path hplace m E
    (i.comp (starMap F)) (fun a v => he (starMap F a) v) p
    (derivedActorLift (i.comp (starMap F)) path.Uα) (derivedActorLift_le _ _) hpoint
    (derivedActorLift_image _ m p _ hθ) b hb hC
  have hbA := zpowers_le.mpr (derivedActorLift_le _ _ hb)
  exact ⟨hc,le_normalizer_iff_commutator_le_left.mp ((hbA.trans hAH).trans c.normalized),
    (commutator_mono le_rfl hbA).trans
      (le_normalizer_iff_commutator_le_right.mp (normalizes_partner h path)),
    source_commutator_seed_conjugate c h path hplace i ⟨hi,hs.1⟩ m E he p hA hpoint b hb hC,
    hsecond⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
