module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubicSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoDihedralExclusionSource
public import Theory.Frattini.Intersection
public import Theory.ElementaryAbelian.Injective

/-!
# Exceptional Frattini structure on the original full endpoint

The actual reduced-completion inclusion transports non-elementarity of
Q_alpha and Phi(Q_alpha) = Z_alpha to the full original parabolic core.
The exceptional D equality uses the intersection of the full original
beta core with the opposite core image, and the linear marking is the
original L_beta/O_2(L_beta) quotient.

The exhaustive original beta catalogue feeds this calculation, retaining
both PSU_3(2) and SU_3(2) as alternatives. No nonsolvability assumption
removes them. The final application discharges beta centrality from the
earlier critical-center family and retains normalization by the full
reduced alpha endpoint and Borel. It does not assert the field bounds,
exceptional parabolic recognition, or regular-path parameters.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (10.9), printed p.163; original endpoint markings, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance frattiniSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The original full alpha core is non-elementary, with its literal Frattini image equal to the original center image. -/
theorem original_bTwo_exceptional_linear_frattini
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    ¬ IsElementaryAbelian 2 Q₀ ∧
      (frattini Q₀).map Q₀.subtype = (Z F₀ α).map (G₀ L S).subtype := by
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  have hneQ := c.exceptional_linear_core_not_elementary (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
    ht hne hcomm hnot eβ hD' E
  have hphi := c.exceptional_linear_frattini (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
    ht hne hcomm hnot eβ hD' E
  constructor
  · intro he
    let := he
    let eQ : Q F₀ α ≃* (parabolic L S 0).pCoreIn 2 :=
      ((Q F₀ α).equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective).trans
        (MulEquiv.subgroupCongr (reduced_base_Q_map h false))
    exact hneQ (IsElementaryAbelian.of_injective eQ.toMonoidHom eQ.injective)
  · have hh := frattini_image_map (Q F₀ α) (G₀ L S).subtype (G₀ L S).subtype_injective
    rw [reduced_base_Q_map h false] at hh
    exact hh.trans (congrArg (map (G₀ L S).subtype) hphi)

/-- The original beta catalogue supplies the Frattini calculation while retaining both small-unitary alternatives. -/
theorem original_bTwo_exceptional_frattini_or_small_unitary
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
        ¬ IsElementaryAbelian 2 Q₀ ∧
        (frattini Q₀).map Q₀.subtype = (Z F₀ α).map (G₀ L S).subtype := by
  rcases original_bTwo_beta_linear_or_small_unitary h hb c hactor hcentral ht hne
    hcomm hnot E with ⟨n,hn,hm⟩ | hp | hs
  · obtain ⟨K,hK,hfin,hcard,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact Or.inr (Or.inr ⟨n,hn,⟨K,hK,hfin,hcard,⟨e⟩⟩,
      original_bTwo_exceptional_linear_frattini h hb c hactor hcentral
        ht hne hcomm.le hnot e hD E⟩)
  · exact Or.inl hp
  · exact Or.inr (Or.inl hs)

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- The earlier critical-center family supplies centrality for the original exceptional-core consumer; full endpoint and Borel normalization are retained. -/
theorem original_bTwo_exceptional_frattini_of_center_family
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F₀).Adj y α →
      ¬ stabilizer F₀ α ≤ normalizer
        ((Q F₀ y ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F₀).Adj y α → IsCriticalPair F₀ β y →
      ⁅Z F₀ β,Z F₀ y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F₀ β α y k₁ W₁))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    P₀ L S 0 ≤ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (D₀ : Set G) ∧
      (ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
        IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
        ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
          ¬ IsElementaryAbelian 2 Q₀ ∧
          (frattini Q₀).map Q₀.subtype = (Z F₀ α).map (G₀ L S).subtype) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne
    hnot hcenters
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right,
    original_bTwo_exceptional_frattini_or_small_unitary h hb c hactor hcentral
      ht htne hcomm (hnot β c.middle.symm) hD E⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
