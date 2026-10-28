module
public import CFSG.Quasithin.Chapter10.SourceNonnormalCoveringObstructions
public import CFSG.Quasithin.Chapter10.SourceNonnormalIntersectionQuotient

/-!
# The marked A₅ component in the genuine covering counterexample

The original contrary covering configuration retains an A₅ marking of
its literal component LH = (L ∩ H)^∞. Although the pushing relation
need not give I ≤ J, it does give I ∩ L₀ ≤ J. That intersection still
covers L₀ modulo its two-core, so the quotient transfer applies to the
same H, J and Sylow witnesses supplied by the genuine C.2.8 construction.

Source: Aschbacher–Smith, 4.2.12–13, printed pp.610–611, specialized
to the original A₅ setup of 10.2, printed p.744 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section02.Unitary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The genuine contrary C.2.8 configuration has an A₅-marked component,
with the marking induced by the original L and its literal inclusion. -/
theorem source_a5_covering_counterexample
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {I : Subgroup G} (hIM : I ≤ D.maximalLocal)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G))
    (hcore : I.pCoreIn 2 ≠ ⊥)
    (horbit : componentOrbit L I = localOrbit T L)
    (hnot : ¬ UniqueMaximalOvergroup I D.maximalLocal) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn D.maximalLocal (localOrbit T L))),
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let M0 := conjugateSpanBy LH (H ⊓ D.maximalLocal)
      PushLE (localOrbit T L) I J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ D.maximalLocal < H ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ D.maximalLocal)
        LH (J.pCoreIn 2)
        (fullModule (localOrbit T L)
          ((S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
            (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype)) ∧
      ¬ H ⊓ D.maximalLocal ≤ normalizer (LH : Set G) ∧
      ¬ (LH.subgroupOf H).IsCComponent ∧ ¬ IsQuasisimple (M0 ⧸ pCore 2 M0) ∧
      ∃ eH : (LH ⧸ pCore 2 LH) ≃* alternatingGroup (Fin 5),
        ∀ x : LH, eH (QuotientGroup.mk' (pCore 2 LH) x) =
          e (QuotientGroup.mk' (pCore 2 L)
            ⟨x.val, ((map_subtype_le _).trans inf_le_left) x.property⟩) := by
  obtain ⟨J,H,S,hIJ,hH,hJH,hlt,hC28,hnorm,hcomp,hq⟩ :=
    source_covering_counterexample_obstructions D hn hIM hcover hcore horbit hnot
  refine ⟨J,H,S,hIJ,hH,hJH,hlt,hC28,hnorm,hcomp,hq,?_⟩
  have hcover' : (localOrbit T L : Set G) ⊆
      (I ⊓ localOrbit T L : Set G) * ((localOrbit T L).pCoreIn 2 : Set G) := by
    intro x hx
    obtain ⟨i,hi,n,hn,he⟩ := hcover hx
    refine ⟨i,⟨hi,?_⟩,n,hn,he⟩
    have hi : i = x * n⁻¹ := eq_mul_inv_iff_mul_eq.mpr he
    rw [hi]
    exact (localOrbit T L).mul_mem hx
      ((localOrbit T L).inv_mem (pCoreIn_le 2 (localOrbit T L) hn))
  exact source_a5_covering_intersection_quotient D e (inf_le_left.trans hIM)
    ((hIJ.2.trans inf_le_left).trans hJH) hcover'
end CFSG.Quasithin.Chapter10
