module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinarySourceApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.KernelControl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CenterCommutators
public import Theory.GroupTheory.AmalgamGraph.PathSupplement

/-!
# The exact center-span kernel in the binary Chapter 13 branch

Both original binary quotient markings make the full reduced Borel a
two-group. Every edge stabilizer is its conjugate, so the full radius-one
kernel U equals Q in this branch. This equality is proved here rather
than imposed as a convention for arbitrary source graphs.

If the radius-one span is Z_a Z_c, the centralizer of that span in the
middle stabilizer is exactly Q_a ∩ Q_c. The source span-centralizer theorem
first puts it in U = Q. Faithfulness of the two actual natural-center
sections then puts it in each neighboring core. Conversely those cores
centralize their respective centers and hence their product.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(13.1)(e,f), printed p.191. Binary markings, the natural centers and their
span equality remain the original Chapter 9 inputs. BinarySpanRecognition
uses this literal kernel in the symmetric-four quotient recognition.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Reduction ReducedLayer Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph CommutingNontrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Only in the both-binary branch, the full local kernel equals its two-core. -/
theorem source_both_binary_kernel_eq_core (h : HypothesisF11 L S)
    (e : ∀ j, (L j ⧸ pCore 2 (L j)) ≃* SL(2,ZMod 2))
    {v w : Vertex (reducedFamily L S)} (he : (graph (reducedFamily L S)).Adj v w) :
    U (reducedFamily L S) v = Q (reducedFamily L S) v := by
  let F := reducedFamily L S
  have hbase : IsPGroup 2 (F false ⊓ F true : Subgroup (G₀ L S)) := by
    change IsPGroup 2 (((P₀ L S 0).subgroupOf (G₀ L S)) ⊓
      ((P₀ L S 1).subgroupOf (G₀ L S)) : Subgroup (G₀ L S))
    rw [(reduced_triple h).intersection]
    rw [(both_binary_reduction_eq_original h e).1]
    exact h.S_isP.comap_subtype
  obtain ⟨g,hg⟩ := edgeStabilizer_map_base F he
  have hedge : IsPGroup 2 (stabilizer F v ⊓ stabilizer F w : Subgroup (G₀ L S)) := by
    rw [hg]
    exact hbase.map _
  have hU : IsPGroup 2 (U F v) := hedge.to_le (ballKernel_one_le_edge F he)
  obtain ⟨T,hT⟩ := reduced_kernel_sylow h v
  have ht : (T : Subgroup (U F v)) = ⊤ := (T.is_maximal' (hU.to_subgroup ⊤) le_top).symm
  rw [ht, ← MonoidHom.range_eq_map, range_subtype] at hT
  exact hT

/-- The actual natural coordinates detect every actor outside the named core. -/
theorem natural_center_centralizer_le_core (A Z R : Subgroup G)
    (hnat : Noncommuting.HasNaturalCenter A Z R) :
    A ⊓ centralizer (Z : Set G) ≤ R := by
  obtain ⟨k,_,_,_,π,hπ,hker,⟨d⟩⟩ := hnat
  intro x hx
  have hxπ : π ⟨x,hx.1⟩ = 1 := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    obtain ⟨z,hz⟩ := d.onto (Multiplicative.ofAdd v)
    have hc : (⟨x*z*x⁻¹,
        (mem_normalizer_iff.mp (d.normalized hx.1) z).mp z.property⟩ : Z) = z := by
      apply Subtype.ext
      change x * (z : G) * x⁻¹ = (z : G)
      rw [← hx.2 z z.property, mul_inv_cancel_right]
    have hh := d.equivariant ⟨x,hx.1⟩ z
    rw [hc,hz] at hh
    change v = Matrix.mulVec (π ⟨x,hx.1⟩).val v at hh
    simpa only [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] using hh.symm
  exact (show (⟨x,hx.1⟩ : A) ∈ R.subgroupOf A from
    hker ▸ MonoidHom.mem_ker.mpr hxπ)

/-- The kernel on the original center span is the literal neighboring-core intersection. -/
theorem source_binary_span_centralizer (h : HypothesisF11 L S)
    (e : ∀ j, (L j ⧸ pCore 2 (L j)) ≃* SL(2,ZMod 2))
    {a v c : Vertex (reducedFamily L S)}
    (ha : (graph (reducedFamily L S)).Adj v a)
    (hc : (graph (reducedFamily L S)).Adj v c)
    (hspan : V (reducedFamily L S) v 1 =
      Z (reducedFamily L S) a ⊔ Z (reducedFamily L S) c)
    (hna : Noncommuting.HasNaturalCenter (stabilizer (reducedFamily L S) a)
      (Z (reducedFamily L S) a) (Q (reducedFamily L S) a))
    (hnc : Noncommuting.HasNaturalCenter (stabilizer (reducedFamily L S) c)
      (Z (reducedFamily L S) c) (Q (reducedFamily L S) c)) :
    stabilizer (reducedFamily L S) v ⊓ centralizer (V (reducedFamily L S) v 1 : Set (G₀ L S)) =
      Q (reducedFamily L S) a ⊓ Q (reducedFamily L S) c := by
  let F := reducedFamily L S
  have hZ := fun w => (source_Z_Q_U (reduced_triple h) w).1
  have hQU := fun w => (source_Z_Q_U (reduced_triple h) w).2
  have hCC : stabilizer F v ⊓ centralizer (V F v 1 : Set (G₀ L S)) ≤ Q F v :=
    (source_span_centralizer_le_kernel (reduced_triple h) ha).trans_eq
      (source_both_binary_kernel_eq_core h e ha)
  apply le_antisymm
  · intro x hx
    have hxv := hQU v (hCC hx)
    refine ⟨natural_center_centralizer_le_core _ _ _ hna ⟨?_,?_⟩,
      natural_center_centralizer_le_core _ _ _ hnc ⟨?_,?_⟩⟩
    · exact (ballKernel_one_le_edge F ha hxv).2
    · exact centralizer_le (Z_neighbor_le_V F ha) hx.2
    · exact (ballKernel_one_le_edge F hc hxv).2
    · exact centralizer_le (Z_neighbor_le_V F hc) hx.2
  · intro x hx
    refine ⟨(ballKernel_one_le_edge F ha.symm (hQU a hx.1)).2,?_⟩
    have hz : V F v 1 ≤ centralizer ({x} : Set (G₀ L S)) := by
      rw [hspan]
      apply sup_le
      · intro z hz
        exact mem_centralizer_singleton_iff.mpr
          ((le_centralizer_iff.mp (Z_centralizes_Q F a (hZ a)) hx.1) z hz)
      · intro z hz
        exact mem_centralizer_singleton_iff.mpr
          ((le_centralizer_iff.mp (Z_centralizes_Q F c (hZ c)) hx.2) z hz)
    intro z hzmem
    exact mem_centralizer_singleton_iff.mp (hz hzmem)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
