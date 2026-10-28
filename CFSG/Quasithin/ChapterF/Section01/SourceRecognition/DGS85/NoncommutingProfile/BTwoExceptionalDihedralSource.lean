module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalDihedral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoDihedralSeedSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubicSource

/-!
# Exceptional beta selection on the original F1.11 quotient

The genuine enlargement dichotomy sends an original D10 beta marking to
D10 or Sz(2) on the graph. The existing Suzuki exclusion removes the second
case, and the exceptional core calculation removes the first. The D = Z
condition is transported from the literal intersection of the original
full beta core and the opposite core image under the completion inclusion.

Combining this with the earlier original catalogue exclusions leaves only
linear, PSU3(2), and SU3(2). The two small unitary rows remain explicit:
their graph enlargement is not supplied by the nonbinary unitary adapters.
The surviving linear marking feeds the existing construction of a cubic
acting freely on the original alpha core; its literal ambient conjugation
formula is retained. This does not assert exceptional parabolic recognition
or path parameters.
Source: DGS, Groups and Graphs (1985), (6.1), pp.118--119,
(10.7), pp.158--159, and (10.9), pp.162--163; F1.11 endpoint markings.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance exceptionalDihedralAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The exceptional equality on the original full cores excludes the original
D10 quotient, including its possible small-Suzuki enlargement. -/
theorem original_bTwo_exceptional_not_dihedral_beta
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5) : False := by
  obtain ⟨_,⟨f⟩⟩ := original_bTwo_dihedral_graph_marking h hb c hactor hcentral
    ht hne hcomm.le hnot e
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  exact c.not_exceptional_dihedral_beta (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot hD' E f

/-- The original exceptional beta catalogue after all currently proved
exclusions, retaining exactly the two unresolved small-unitary rows. -/
theorem original_bTwo_exceptional_beta_quotient_remaining
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
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n)) ∨
      ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 := by
  rcases original_bTwo_beta_quotient_remaining h hb c hactor hcentral ht hne hcomm.le hnot
    with he | he | he | he
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)
  · obtain ⟨e⟩ := he
    exact (original_bTwo_exceptional_not_dihedral_beta h hb c hactor hcentral
      ht hne hcomm hnot hD E e).elim

/-- Actual source consumer: the exhaustive original row split constructs the
cubic on the full alpha core, unless one of the unresolved small-unitary
enlargements occurs. No saturation, index or linear-beta premise is supplied. -/
theorem original_bTwo_exceptional_cubic_or_small_unitary
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
    (∃ a : c.actor, orderOf ((a : G₀ L S) : G) = 3 ∧ orderOf (c.quotient a) = 3 ∧
      ∃ φ : MulAut ((parabolic L S 0).pCoreIn 2), orderOf φ = 3 ∧
        (∀ x, (φ x : G) = ((a : G₀ L S) : G) * (x : G) * ((a : G₀ L S) : G)⁻¹) ∧
        (∀ x, φ x = x → x = 1)) ∨
      ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 := by
  rcases original_bTwo_exceptional_beta_quotient_remaining h hb c hactor hcentral ht hne
    hcomm hnot hD E with he | he
  · obtain ⟨n,hn,K,hK,hfin,hcard,⟨e⟩⟩ := he
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    have hD' : D F₀ β t = Z F₀ α := by
      apply map_injective (G₀ L S).subtype_injective
      change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
      rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
      exact hD
    exact Or.inl (original_bTwo_exceptional_linear_cubic h hb c hactor hcentral
      ht hne hcomm.le hnot e hD')
  · exact Or.inr he

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
