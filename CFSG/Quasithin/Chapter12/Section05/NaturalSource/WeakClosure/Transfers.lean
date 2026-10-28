module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointGeometry
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure.ConjugateSpan
public import Theory.GroupTheory.TINormalizerControl

/-!
# TI normalization and the elementary point span

The nontrivial line inside V₆ makes the source TI property in M apply to
G₆ ≤ M, so G₆ normalizes V. This supplies the final TI step of 12.5.7;
the statement does not infer normalization from containment in M alone.
The genuine zeroth weak closure then makes ⟨Vᴳ¹⟩ elementary abelian,
using precisely V ≤ O₂(G₁) and the marked Sylow subgroup of G₁.

Source: Aschbacher--Smith, 12.2.6, 12.5.7 and 12.5.8(2), pp.797,820.
The earlier structural source input and the local core/weak-closure
conclusions remain explicit. Their existence is not asserted here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The TI step in 12.5.7: containment in M alone does not normalize V. -/
theorem normalizes_of_G₆_le (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    s.marking.Gi 6 ≤ normalizer (V : Set G) := by
  have hTI := ((structural L h).2.2 V D).2.2.1
  exact (le_inf hG₆ le_rfl).trans
    (inf_normalizer_le_of_trivial_intersections hTI
      s.marking.V₆_ne_bot (s.marking.subspace_le _))

/-- A conjugator in G₆ fixes the original V, after the source TI step. -/
theorem conjugate_eq_of_mem_G₆ (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M) {g : G} (hg : g ∈ s.marking.Gi 6) :
    V.map (MulAut.conj g).toMonoidHom = V :=
  mem_normalizer_iff_map_conj_eq.mp (normalizes_of_G₆_le s h structural hG₆ hg)

omit [Finite G] in
/-- Original 12.5.8(2), conditional exactly on 12.5.7 and 12.5.8(1). -/
theorem elementary_point_span (s : SylowExteriorMarking D)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G)) :
    IsElementaryAbelian 2 s.marking.U := by
  let := D.elementary
  have hQT : (s.marking.Gi 1).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le s.sylow_le_G₁] using
      pCoreIn_le_sylow (s.marking.Gi 1) (T.subtype s.sylow_le_G₁)
  apply ChapterE.conjugateSpanBy_elementary_of_weakClosure_zero V (T : Subgroup G)
    ((s.marking.Gi 1).pCoreIn 2) (s.marking.Gi 1) hcore hQT ?_ hW
  exact (s.marking.Gi 1).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (s.marking.Gi 1)))

omit [Finite G] in
/-- The final step of 12.5.10(2). Fixing the literal V₆ puts its ambient
centralizer above C_G(C₁), and 12.5.4 bounds that centralizer by M. -/
theorem centralizer_weakCentralizer_one_le (a : ExteriorMarking D)
    (hG₆ : a.Gi 6 ≤ a.M)
    (hW₁ : ChapterE.indexedWeakClosure V (T : Subgroup G) 1 ≤
      centralizer (a.Vi 6 : Set G)) :
    centralizer (ChapterE.weakCentralizer V (T : Subgroup G) 1 : Set G) ≤ a.M := by
  have h6 : a.Vi 6 ≤ ChapterE.weakCentralizer V (T : Subgroup G) 1 :=
    le_inf ((a.subspace_le _).trans D.le_sylow) (le_centralizer_iff.mp hW₁)
  exact (Subgroup.centralizer_le h6).trans ((Subgroup.centralizer_le_normalizer _).trans hG₆)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
