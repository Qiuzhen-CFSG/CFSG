module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceContainedIncidence
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.G2Core

/-!
# The critical G₂ offender on the original flag

The hyperplane displacement calculation puts the nonoffender point
in V, contrary to the preceding exclusion. Thus the selected actor
is an offender; the reciprocal symmetry also excludes its point from U.

Only Structural1222At at the original G,T is used. The source producers
qt-d-1222-source and qt-d-1434-source retain the earlier structural and
faithful inputs. Original residual alternatives, uniqueness, relative
component and alternating recognition retain qt-d-14763-source-data.
Final source 14.7.75 discharge remains with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.53–63, pp.1065–1069; F.9.18, pp.325–326.
The reused concrete model calculations retain LICENSES/ATLAS.txt attribution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
section ModelIncidence
open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
private theorem line_in_distinguishedPlane_incident_at (L : ZeroProductLine (ZMod 2))
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

private theorem root_mem_natural_at (a b : ZMod 2) : rootActor a b 0 ∈ BinaryCore.natural := by
  rw [← elementary_inf_derived]
  exact ⟨⟨⟨a,b,0,0,0⟩,⟨rfl,rfl⟩,rfl⟩,(rootActor_mem_derived a b 0).mpr rfl⟩

private theorem model_fixed_line_incident_at (m : BinaryG2Module) (L : ZeroProductLine (ZMod 2))
    (hL : m.singularMap.line L ≤ fixedSpace m.action BinaryCore.natural) :
    pointOnLine firstPoint L := by
  apply line_in_distinguishedPlane_incident_at L
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
  have ha := hfixed (rootActor 1 0 0) (root_mem_natural_at 1 0)
  have hb := hfixed (rootActor 0 1 0) (root_mem_natural_at 0 1)
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
private def modelNaturalProjection_at :
    (m : BinaryG2Module) → m.Space →ₗ[ZMod 2] Natural.Space (ZMod 2)
  | .natural => LinearMap.id
  | .weyl => Natural.mk (ZMod 2)

private theorem model_lift_at (m : BinaryG2Module) (v : m.Space) :
    ∃ x : TraceZero (ZMod 2), m.singularMap.linear x = v := by
  cases m with
  | natural => exact mk_surjective (ZMod 2) v
  | weyl => exact ⟨v,rfl⟩

private theorem model_hyperplane_displacement_at (m : BinaryG2Module)
    (g : Model (ZMod 2)) (hg : g ∈ BinaryCore.natural) (v : m.Space)
    (hv : Restricted.NaturalCoordinates.equiv (ZMod 2) (modelNaturalProjection_at m v) ∈
      Natural.BinaryPointFlag.hyperplane) :
    m.action g v - v ∈ m.singularMap.point firstPoint := by
  obtain ⟨x,rfl⟩ := model_lift_at m v
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
end ModelIncidence
open Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

private theorem source_point_le_seed_of_hyperplane_at
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
    (hproj : ∀ v, q (E v) = modelNaturalProjection_at m v) : path.Zα ≤ V := by
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
  have hlpoint := (m.singularMap.incidence Atlas.G2.firstPoint l).mp (model_fixed_line_incident_at m l hlf)
  have himage : c.imageSpace C ≤ c.imageSpace V := by
    rw [hCi]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,hv,rfl⟩
    have hvhyper : r v ∈ Atlas.G2.Natural.BinaryPointFlag.hyperplane :=
      hhyper ▸ Submodule.mem_map_of_mem hv
    have hmhyper : Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)
        (modelNaturalProjection_at m (E.symm v)) ∈ Atlas.G2.Natural.BinaryPointFlag.hyperplane := by
      rw [←hproj,E.apply_symm_apply]
      exact hvhyper
    have hdisp := model_hyperplane_displacement_at m (f a)
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

include c in
theorem source_critical_offender_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
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
    source_nonoffender_core_hyperplane_at c h hab hcomponent hfit eK structural hf hcomm
      P hP orbit path hplace selection hn
  have hZV : path.Zα ≤ V := by
    rcases source_cover_on_marking c h hcomponent hfit eK f hf' q hq heq hfix with
      ⟨E,he,hproj⟩ | ⟨E,he,hproj⟩
    · exact source_point_le_seed_of_hyperplane_at c h path hplace f hf' hJ q heq hA hhyper
        .natural E he hproj
    · exact source_point_le_seed_of_hyperplane_at c h path hplace f hf' hJ q heq hA hhyper
        .weyl E he hproj
  exact source_critical_point_not_le_seed_at c h hab hcomponent hfit eK structural hf hcomm
    P hP orbit path hplace selection hZV

include c in
theorem source_critical_point_not_le_span_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) : ¬ path.Zα ≤ F.U := by
  have ho := source_critical_offender_at c h hab hcomponent hfit eK structural hf hcomm
    P hP orbit path hplace selection
  obtain ⟨hq,hb⟩ := source_selected_critical_bound_at c h hab structural hf path selection
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
  exact (source_full_actor_reciprocity_at c h hab hcomponent hfit eK structural hf hcomm
    path hplace selection m E f hf' he p hA).2.1

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
