module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.Intersections
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.Geometry
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.SourceAssembly

/-!
# Center calculations for the marked parabolic

All six clauses of Lemma 12.8.10 are assembled from the precise preceding
12.8.3–9 inputs. The commutator form on the literal U/Z(U) gives
Z(W)=V₂Z(U), the centralizer hyperplane and the moved-rank bound. The S₃
quotient and its fixed-space calculation identify Z(I₂). Subgroup modularity
then gives the intersections, the central involution in the original Sylow T,
the internal multiplication isomorphism, and the full quotient-kernel chain.

For centralization by L, the full natural action constructs the ordered
minimal parabolics and their successive residual conjugators. The corrected
induction makes each new residual centralize Z(U) and the accumulated group
centralize Z(I₂). Rank two uses the original O² residual equality directly;
it does not require the full L-action of the higher-rank alternatives.

No clause of 12.8.10, centralizer-center identity, generation witness or
induction premise is assumed. The earlier source discharge remains with the
parent Parabolic assembly: Hypothesis 12.8.1 supplies two-perfectness and
T-normalization of L and the natural-action kernel; 12.8.3(1) supplies the
full actions; 12.8.4(3–4) supplies the commutator, square and local-kernel
inputs; 12.8.8(2–3,6) supplies the evaluated symplectic form, center
intersection and plane span; and 12.8.9(3,5) supplies the fixed-space and
two quotient-action kernels. Binary generation already proves the needed
12.8.9(1) conclusions from those earlier inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.10, printed pp.853–854, PDF pp.870–871.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
  [IsElementaryAbelian 2 V] {n : ℕ}

/-- Every clause of Lemma 12.8.10, conditional only on the specified preceding
source results. Products are subgroup joins of commuting factors; clause (5)
also supplies disjointness and the multiplication isomorphism with both
original factor embeddings. Clause (4) uses the generator rank of the actual
moved subgroup for the action on U/Z(U), and clause (6) retains the literal
actions on U/Z(U) and the image of U in H/V₁. -/
theorem center_calculations_of_binary_source
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hperfect : IsPPerfect 2 L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfullLT : Function.Surjective (F.binarySeedAction L hL))
    (hfullL : 3 ≤ n → ∀ a : MulAut V,
      ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hnaturalCore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hfix : ∀ a ∈ F.U, a ∉ F.W → ∀ z ∈ (F.I₂ L).pCoreIn 2,
      ⁅z, a⁆ ∈ F.E g → z ∈ F.W)
    (hhat : F.X g ⊓ F.uhatAction.ker.map F.H.subtype = F.E g)
    (htilde : F.X g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype = F.E g)
    (hcore : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H)
    (B : F.UhatCommutatorForm hcomm) :
    F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 ∧
    F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L) ∧
    (F.Vi 1 < F.ZU ⊓ conjugate F.U g →
      sylowOmega T ⊓ centerIn (F.I₂ L) ≠ ⊥) ∧
    (⁅F.W, conjugate F.ZU g⁆ ≤ F.ZU ⊔ F.Vi 2 ∧
      ∀ x : conjugate F.ZU g,
        Group.rank (F.uhatMoved (F.conjugateCenterActor hn L hL g hgP x)) ≤ 2) ∧
    (conjugate F.ZU g ≤ F.U →
      (F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
        Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
        ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
          ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
      ⁅L, centerIn (F.I₂ L)⁆ = ⊥) ∧
    (conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype =
        conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype ∧
      conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype =
        conjugate F.ZU g ⊓ QH F.H ∧
      conjugate F.ZU g ⊓ QH F.H = conjugate F.ZU g ⊓ F.U ∧
      conjugate F.ZU g ⊓ F.U =
        (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g ∧
      (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g =
        centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ∧
      centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ≤ F.U) := by
  obtain ⟨e, _, hgen, _, hIG, hIN, _⟩ :=
    F.binary_generation hn L hL hfullLT hnaturalCore hcomm hsquare hspan hne g hgP hgH
  have hUT := F.binary_U_le_sylow (by omega) hsquare
  have hI := (normal_subgroupOf_iff_le_normalizer hIG).mp hIN
  obtain ⟨hfirst, hsecond, homega, hcommutator, _, hchain⟩ :=
    F.center_and_kernel_calculations_of_commutator_form hn L hL hcenter hcomm
      hUT hI g hgP hgH hgen e hfix hhat htilde hcore B
  refine ⟨hfirst, hsecond, homega, ⟨hcommutator, ?_⟩, ?_, hchain⟩
  · exact F.conjugate_center_moved_rank_le_two hn L hL hcenter B g hgP hgH
  · exact F.center_product_and_centralization_of_binary_source hn L hL hperfect hTL
      hfullLT hfullL hnaturalCore hcenter hcomm hsquare hspan hne g hgP hgH
      hfix hhat htilde hcore (F.plane_centralizer_center B)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
