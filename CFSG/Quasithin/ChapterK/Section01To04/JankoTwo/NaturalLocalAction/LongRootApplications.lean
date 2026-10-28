module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.InvolutionImages

/-!
# The literal long-root fixer in the J₂ rank-two exclusion

The particular 2-central J₂ involution is long-root by InvolutionImages. This
module specializes the universal displacement and pointwise-fixer clauses of
B.4.6(4) to that actual embedded involution. The root line is a literal conjugate
of the one-parameter A-root subgroup. Its centrality in the full involution
centralizer follows from the universal centralizer equality at every nonzero
parameter. These data discharge the particular embedding premises of
MarkedApplications.carrier_rank_two_exclusion.

B46LongRootModuleFacts contains only the universal earlier-source module
clauses, with no J₂ embedding or actor conclusion. Its producer is qt-b-04-g2;
qt-k-01-04 retains their final discharge. Source: Aschbacher–Smith, B.4.6(4)
and K.4.5, printed pp.88 and 460/PDF pp.99 and 471.
-/

open Atlas.G2 Atlas.G2.Explicit Subgroup
open Representation Representation.BinaryOffender
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction
variable {K : Type*} [Field K]

/-- The literal one-parameter long-root group in the marked coordinates. -/
def longRootLineHom : Multiplicative K →* Model K where
  toFun x := rootA x.toAdd
  map_one' := rootA_zero
  map_mul' x y := (Atlas.G2.rootA_add x.toAdd y.toAdd).symm

def longRootLine (g : Model K) : Subgroup (Model K) :=
  (longRootLineHom (K := K)).range.map (MulAut.conj g).toMonoidHom

variable [CharP K 2] [Algebra (ZMod 2) K]

/-- The universal natural-module clauses of B.4.6(4). The J₂ embedding is
absent from these inputs; its particular root placement is proved separately. -/
structure B46LongRootModuleFacts (K : Type*) [Field K] [CharP K 2]
    [Algebra (ZMod 2) K] : Prop where
  displacement : ∀ (g : Model K) (r : K), r ≠ 0 →
    fixedCodim (naturalAction K) (zpowers (MulAut.conj g (rootA r))) =
      2 * Module.finrank (ZMod 2) K
  pointwiseFixer : ∀ (g : Model K) (r : K), r ≠ 0 →
    subspaceKernel (naturalAction K)
      (fixedSpace (naturalAction K) (zpowers (MulAut.conj g (rootA r)))) ⊤ = longRootLine g

omit [Algebra (ZMod 2) K] in
/-- The root line centralizes the entire centralizer, using the literal
B.4.6 long-root centralizer equality for every nonzero parameter. -/
theorem longRootLine_le_doubleCentralizer
    (h : InvolutionImages.B46RootFacts K) (g : Model K) (r : K) (hr : r ≠ 0) :
    longRootLine g ≤ centralizer
      (centralizer ({MulAut.conj g (rootA r)} : Set (Model K)) : Set (Model K)) := by
  rintro _ ⟨_,⟨s,rfl⟩,rfl⟩
  apply mem_centralizer_iff.mpr
  intro x hx
  have hx' : MulAut.conj g⁻¹ x ∈ centralizer ({rootA r} : Set (Model K)) := by
    have hc := (mem_centralizer_singleton_iff.mp hx)
    have he := congrArg (MulAut.conj g⁻¹) hc
    apply mem_centralizer_singleton_iff.mpr
    simpa [MulAut.conj_apply, mul_assoc] using he
  by_cases hs : s.toAdd = 0
  · simp [longRootLineHom,hs]
  · rw [h.longCentralizer r hr, ← h.longCentralizer s.toAdd hs] at hx'
    have he := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp hx')
    simpa [longRootLineHom, MulAut.conj_apply, mul_assoc] using he

end CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction

namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
open NaturalLocalAction
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)

/-- The actual 2-central carrier involution has displacement four, and its
pointwise fixer is a literal conjugate long-root line, central in its full
ambient involution centralizer. -/
theorem carrier_longRoot_data
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K) :
    fixedCodim (naturalAction K) (zpowers (D.carrierEmbedding FirstFusion.t)) = 4 ∧
    ∃ g : Model K,
      subspaceKernel (naturalAction K)
        (fixedSpace (naturalAction K) (zpowers (D.carrierEmbedding FirstFusion.t))) ⊤ =
        longRootLine g ∧
      longRootLine g ≤ centralizer
        (centralizer ({D.carrierEmbedding FirstFusion.t} : Set (Model K)) : Set (Model K)) := by
  obtain ⟨g,r,hr,he⟩ := D.carrierEmbedding_t_isLongRootElement h
  rw [he]
  refine ⟨?_,g,hV.pointwiseFixer g r hr,longRootLine_le_doubleCentralizer h g r hr⟩
  rw [hV.displacement g r hr,D.fieldDegree]

/-- The concrete rank-two K.4.5 exclusion now has only universal B.4.6 inputs. -/
theorem carrier_rank_two_exclusion_of_B46 [FiniteDimensional (ZMod 2) V]
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K)
    (A : Subgroup Carrier) (hA : rank A = 2) (hzA : FirstFusion.t ∈ A) :
    2 * rank A < fixedCodim D.carrierAction A := by
  obtain ⟨hd,g,hroot,hR⟩ := D.carrier_longRoot_data h hV
  exact D.carrier_rank_two_exclusion A hA hzA (longRootLine g) hd hroot hR

end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
