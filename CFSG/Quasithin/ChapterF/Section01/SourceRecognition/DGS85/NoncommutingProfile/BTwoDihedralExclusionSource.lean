module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoDihedralExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoDihedralSeedSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearModuleSource

/-!
# The original beta catalogue after the full dihedral exclusion

An original D10 marking enlarges to D10 or Sz(2). The existing Suzuki
obstruction and the new regular/exceptional dihedral exclusion remove both
possibilities. The original beta quotient is consequently binary linear,
PSU3(2), or SU3(2), with both small-unitary kernels and alternatives retained.

In the linear alternative the existing source calculations now construct
saturation, the actual elementary quotient Q_alpha/D_alpha of order q_beta²,
and q_beta = q_alpha^r for some positive r. The full reduced endpoint and
Borel normalize the literal original layers. No linear model, saturation,
or index premise is supplied to this consumer, and no restriction r=1 or 3
is asserted. The source setup owner retains the small-unitary enlargement;
(10.8)--(10.10) and final Chapter 10 assembly remain with this family.

Source: DGS, Groups and Graphs (1985), (6.1), pp.118--119, and
(10.7), pp.158--159; original F1.11 endpoint and Borel markings.
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
local instance dihedralExclusionSourceAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The original beta quotient cannot be dihedral, in either D_alpha branch. -/
theorem original_bTwo_not_dihedral_beta
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5) : False := by
  obtain ⟨_,⟨f⟩⟩ := original_bTwo_dihedral_graph_marking h hb c hactor hcentral
    ht hne hcomm.le hnot e
  exact c.not_dihedral_beta (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot E f

/-- Exhaustive original beta selection, retaining both unresolved small-unitary rows. -/
theorem original_bTwo_beta_linear_or_small_unitary
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
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
    exact (original_bTwo_not_dihedral_beta h hb c hactor hcentral ht hne hcomm hnot E e).elim

/-- The actual original quotient, field power and saturation follow from the
remaining catalogue, with the small-unitary alternatives kept explicit. -/
theorem original_bTwo_central_core_field_or_small_unitary
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
        (∃ r : ℕ, 0 < r ∧ 2^n = Nat.card k ^ r) ∧
        (centralSeed F₀ α β t).map (G₀ L S).subtype = Q₀ ∧
        P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
          IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
          Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^n)^2 := by
  rcases original_bTwo_beta_linear_or_small_unitary h hb c hactor hcentral ht hne
    hcomm hnot E with ⟨n,hn,hm⟩ | hp | hs
  · obtain ⟨K,hK,hfin,hcard,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    have hpower := original_bTwo_linear_field_power h hb c hactor hcentral
      ht hne hcomm.le hnot e
    rw [hcard] at hpower
    have hsat := (original_bTwo_linear_seed_and_indices h hb c ht hne hnot e).1
    have hnorm := original_bTwo_seed_layers_normalized h hb c ht hne
    dsimp only at hnorm
    rw [hsat] at hnorm
    obtain ⟨_,hN,hE,hq⟩ := original_bTwo_linear_central_core h hb c hactor hcentral
      ht hne hcomm.le hnot e
    rw [hcard] at hq
    exact Or.inr (Or.inr ⟨n,hn,⟨K,hK,hfin,hcard,⟨e⟩⟩,hpower,hsat,
      hnorm.1,hnorm.2,hN,hE,hq⟩)
  · exact Or.inl hp
  · exact Or.inr (Or.inl hs)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
