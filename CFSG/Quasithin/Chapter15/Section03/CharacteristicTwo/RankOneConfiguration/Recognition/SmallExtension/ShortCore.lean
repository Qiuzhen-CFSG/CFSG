module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Models
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.ElementaryAbelian.Injective

/-!
# Shortness prerequisites from the original component source

Relative normality and characteristic two give the component's generalized
Fitting condition; the original commutator identity makes it perfect. If the
Sylow-central component module exhausts [O₂(L),L], that entire core is elementary
and centralized by O₂(L). Only irreducibility of its central quotient then
remains for shortness. The core equality is a genuine reconstruction input,
not a consequence of merely knowing a natural constituent.

Source: Aschbacher–Smith C.1.7 and the proof of 15.3.31, pp.123,1132.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover CentralCover.BlockModels EightGeometry EightGeometry.NaturalModule
namespace SourceData
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

/-- Relative normality inherits the characteristic-two generalized Fitting condition. -/
theorem component_fitting (s : SourceData κ d c) :
    generalizedFitting c.L = pCore 2 c.L := by
  let K := c.L.subgroupOf I
  let : K.Normal := s.normal
  have hK : generalizedFitting K = pCore 2 K := by
    apply le_antisymm _ ((pCore_le_fitting K 2).trans (fitting_le_generalizedFitting K))
    rw [pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal]
    apply map_le_iff_le_comap.mp
    rw [← s.characteristicTwo]
    exact generalizedFitting_map_subtype_le_of_isSubnormal K (inferInstance : K.Normal).isSubnormal
  let e : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
  rw [map_generalizedFitting_equiv, pCore_map_iso, hK]

/-- The source component is perfect, hence two-perfect. -/
theorem component_twoPerfect (s : SourceData κ d c) :
    IsPPerfect 2 c.L := by
  let := component_isPerfect_of_containment d c s.contains
  intro N hn hq
  let := hn
  have hs : Subsingleton (c.L ⧸ N) := by
    by_contra! hnt
    exact Group.IsPerfect.not_isNilpotent (c.L ⧸ N) hq.isNilpotent
  apply eq_top_iff.mpr
  intro l _
  exact (QuotientGroup.eq_one_iff l).mp (Subsingleton.elim _ _)

/-- Exhaustion by the Sylow-central component module makes the whole core elementary. -/
theorem core_elementary_of_eq_componentModule
    (s : SourceData κ d c)
    (hQ : extensionCore c.L = d.componentModule I c.L) :
    IsElementaryAbelian 2 (ChapterC.blockU c.L) := by
  let := componentModule_elementary d c s.characteristicTwo s.sylow s.sylow_eq
  let e : ChapterC.blockU c.L ≃* d.componentModule I c.L :=
    ((ChapterC.blockU c.L).equivMapOfInjective c.L.subtype c.L.subtype_injective).trans
      (MulEquiv.subgroupCongr ((blockU_map c.L).trans hQ))
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

omit [Finite G] in
/-- Exhaustion also makes the intrinsic two-core centralize the entire commutator core. -/
theorem core_central_of_eq_componentModule
    (s : SourceData κ d c)
    (hQ : extensionCore c.L = d.componentModule I c.L) :
    ChapterC.blockU c.L ≤ centralizer (pCore 2 c.L : Set c.L) := by
  have hc := (le_centralizer_iff.mp
    (component_core_centralizes_span d c s.normal s.sylow s.sylow_eq))
  intro x hx y hy
  apply Subtype.ext
  have hx' : (x : G) ∈ d.componentModule I c.L := by
    rw [← hQ, ← blockU_map]
    exact mem_map_of_mem c.L.subtype hx
  exact hc (componentModule_le_span d c hx') y (mem_map_of_mem c.L.subtype hy)

/-- All source shortness clauses apart from the three module conditions are automatic. -/
theorem short_of_core (s : SourceData κ d c)
    (he : IsElementaryAbelian 2 (ChapterC.blockU c.L))
    (hc : ChapterC.blockU c.L ≤ centralizer (pCore 2 c.L : Set c.L))
    (hi : ChapterC.BlockModuleIrreducible c.L) : ChapterC.IsShort c.L :=
  ⟨inferInstance, s.component_twoPerfect, s.component_fitting,
    he, hc, Or.inl c.core_quotient_quasisimple, hi⟩

/-- Literal source application of the core-exhaustion hypothesis. -/
theorem short_of_eq_componentModule (s : SourceData κ d c)
    (hQ : extensionCore c.L = d.componentModule I c.L)
    (hi : ChapterC.BlockModuleIrreducible c.L) : ChapterC.IsShort c.L :=
  s.short_of_core (s.core_elementary_of_eq_componentModule hQ)
    (s.core_central_of_eq_componentModule hQ) hi

end SourceData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
