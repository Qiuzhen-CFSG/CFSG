module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore.Reduced
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore.Automorphism
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The ordinary root-core decomposition and its terminal application

Reducedness places the second two-core inside the root core and makes the
root core centralize it. A root-core element lies in T and normalizes L.
The marked plane-local isomorphism transports its conjugation action to the
full-cover calculation: it acts on W as a concrete upper-unipotent Levi lift
in the second two-core. Dividing by that lift leaves an element of the literal
centralizer of W. This proves Q_Z = O₂(K₂) C_{Q_Z}(W), the equality (**).

The final theorem applies the constructed geometry, generation and core
decomposition to the existing terminal contradiction. It retains precisely
the FF equality and secondary-component premises owned by the final assembly.

Source: Aschbacher--Smith 4.3.6, printed pp.614--615, especially (*) and (**).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Theory.SpecificGroups.SymplecticFour
namespace OrdinarySymplecticMarking
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- Every root-core element induces on the full module the action of an
actual element of the second subgroup's two-core. -/
theorem rootCore_action (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (x : G) (hx : x ∈ m.rootCore) :
    ∃ y ∈ m.second.pCoreIn 2, ∀ w ∈ c.ordinaryModule,
      x * w * x⁻¹ = y * w * y⁻¹ := by
  let : Algebra (ZMod 2) m.Field := ZMod.algebra m.Field 2
  have hxL : x ∈ normalizer (L : Set G) :=
    D.sylow_normalizes_component (m.rootCore_le_sylow hn D hx)
  let e : planeLocal (F := m.Field) ≃* L :=
    ((planeLocal (F := m.Field)).equivMapOfInjective m.modelEmbedding
      m.modelEmbedding_injective).trans (MulEquiv.subgroupCongr m.planeLocal_image)
  let aL : MulAut L := L.normalizerMonoidHom ⟨x, hxL⟩
  let α : MulAut (planeLocal (F := m.Field)) := e.trans (aL.trans e.symm)
  have he (g : planeLocal (F := m.Field)) : (e g : G) = m.modelEmbedding g := rfl
  have hα (g : planeLocal (F := m.Field)) :
      m.modelEmbedding (α g) = x * m.modelEmbedding g * x⁻¹ := by
    have hh : e (α g) = aL (e g) := e.apply_symm_apply _
    exact congrArg Subtype.val hh
  have hfix (q : Plane.radical (F := m.Field))
      (hq : q.val.val ∈ (pointRadical (F := m.Field)).map pointLocal.subtype) :
      α q.val = q.val := by
    apply Subtype.ext
    apply m.modelEmbedding_injective
    rw [hα]
    have hqB : m.modelEmbedding q.val.val ∈ m.second.pCoreIn 2 :=
      (m.pointRadical_image hn).le (mem_map_of_mem m.modelEmbedding hq)
    have hcomm := m.rootCore_le_centralizer_rootSpan hn D h hx
      (m.modelEmbedding q.val.val) (m.second_core_le_rootSpan hn hqB)
    rw [← hcomm, mul_inv_cancel_right]
  obtain ⟨t, ht⟩ := OrdinaryRootCoreMatrix.plane_automorphism_fixing_point_radical
    m.card hn α hfix
  let y : G := m.modelEmbedding (Plane.levi (Representation.SL2OrthogonalCover.upper t)).val
  have hy : y ∈ m.second.pCoreIn 2 :=
    (m.pointRadical_image hn).le (mem_map_of_mem m.modelEmbedding
      (OrdinaryRootCoreMatrix.levi_upper_mem_point_radical t))
  refine ⟨y, hy, ?_⟩
  intro w hw
  obtain ⟨g, hg, rfl⟩ := (m.planeRadical_image hn).ge hw
  obtain ⟨q, hq, rfl⟩ := hg
  have hh := congrArg (fun g : planeLocal (F := m.Field) => m.modelEmbedding g.val)
    (ht ⟨q, hq⟩)
  rw [hα] at hh
  simpa only [y, Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    map_mul, map_inv] using hh

/-- The source equality (**) for the literal root core and full source module. -/
theorem rootCore_decomposition (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)) := by
  have hBQ : m.second.pCoreIn 2 ≤ m.rootCore :=
    (m.second_core_le_rootSpan hn).trans (m.rootSpan_le_rootCore hn D h)
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, ha⟩ := m.rootCore_action hn D h x hx
    have hz : y⁻¹*x ∈ m.rootCore ⊓ centralizer (c.ordinaryModule : Set G) := by
      refine ⟨m.rootCore.mul_mem (m.rootCore.inv_mem (hBQ hy)) hx, ?_⟩
      intro w hw
      have hzconj : (y⁻¹*x)*w*(y⁻¹*x)⁻¹ = w := by
        calc
          _ = y⁻¹*(x*w*x⁻¹)*y := by group
          _ = y⁻¹*(y*w*y⁻¹)*y := by rw [ha w hw]
          _ = w := by group
      calc
        w*(y⁻¹*x) = ((y⁻¹*x)*w*(y⁻¹*x)⁻¹)*(y⁻¹*x) := by rw [hzconj]
        _ = (y⁻¹*x)*w := by group
    simpa only [mul_inv_cancel_left] using
      (m.second.pCoreIn 2 ⊔ (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G))).mul_mem
        (mem_sup_left hy) (mem_sup_right hz)
  · exact sup_le hBQ inf_le_left

end OrdinarySymplecticMarking

/-- All root geometry and module calculations in the ordinary branch are
constructed. Only the FF equality and secondary-component premises remain. -/
theorem SourceConfiguration.ordinary_false_of_calculated_root_module
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n) (m : OrdinarySymplecticMarking c n) (KZ : Subgroup G)
    (hU : m.rootSpan = m.second.pCoreIn 2)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (himage : KZ ≤ m.second ⊔ m.rootCore)
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) : False :=
  c.ordinary_false_of_root_module D hn m KZ (m.sylow_le_rootNormalizer hn D)
    (m.fullModule_conjugateSpan_second hn) hU (m.rootCore_decomposition hn D h)
    hKZ himage hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
