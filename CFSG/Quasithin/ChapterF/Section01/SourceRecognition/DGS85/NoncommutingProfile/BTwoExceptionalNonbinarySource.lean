module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalNonbinary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalFrattiniSource

/-!
# Nonbinary exceptional-core constraints at the original endpoints

Transport the natural commutator calculation through the actual inclusion of
the reduced completion. If the alpha field is nonbinary, the exceptional
linear branch has an abelian alpha core of exponent exactly four and the
specified Frattini image. Both small unitary rows remain in the original
catalogue. The earlier center family supplies centrality, and the full
endpoint and Borel normalizers retain their original markings.

These constraints do not yet exclude the abelian exponent-four case and
therefore do not prove q_alpha = 2. Source: DGS, Groups and Graphs (1985),
proof of (10.9), printed p.163, and original endpoint markings, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance nonbinarySourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The original nonbinary exceptional core is abelian of exponent exactly four, with its literal Frattini image. -/
theorem original_bTwo_exceptional_nonbinary_core
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hk : 2 < Nat.card k) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    IsMulCommutative Q₀ ∧
      (frattini Q₀).map Q₀.subtype = (Z F₀ α).map (G₀ L S).subtype ∧
      (∀ x : Q₀, x ^ 4 = 1) ∧ ∃ x : Q₀, orderOf x = 4 := by
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  obtain ⟨hm,hphi,hfour,x,hx⟩ := c.exceptional_nonbinary_core_exponent_four
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    hb hactor hcentral ht hne hcomm hnot eβ hD' E hk
  change IsMulCommutative (Q F₀ α) at hm
  change ∀ x : Q F₀ α, x ^ 4 = 1 at hfour
  let := hm
  let eQ : Q F₀ α ≃* (parabolic L S 0).pCoreIn 2 :=
    ((Q F₀ α).equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_base_Q_map h false))
  refine ⟨?_,?_,?_,eQ x,(eQ.orderOf_eq x).trans hx⟩
  · refine ⟨⟨?_⟩⟩
    intro y z
    obtain ⟨y,rfl⟩ := eQ.surjective y
    obtain ⟨z,rfl⟩ := eQ.surjective z
    rw [←map_mul,←map_mul]
    exact congrArg eQ (mul_comm y z)
  · have hh := frattini_image_map (Q F₀ α) (G₀ L S).subtype (G₀ L S).subtype_injective
    rw [reduced_base_Q_map h false] at hh
    exact hh.trans (congrArg (map (G₀ L S).subtype) hphi)
  · intro y
    obtain ⟨y,rfl⟩ := eQ.surjective y
    exact (map_pow eQ y 4).symm.trans ((congrArg eQ (hfour y)).trans eQ.map_one)

/-- The original beta catalogue supplies the nonbinary core constraint while retaining both small-unitary alternatives. -/
theorem original_bTwo_exceptional_nonbinary_or_small_unitary
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hk : 2 < Nat.card k) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
        IsMulCommutative Q₀ ∧
        (frattini Q₀).map Q₀.subtype = (Z F₀ α).map (G₀ L S).subtype ∧
        (∀ x : Q₀, x ^ 4 = 1) ∧ ∃ x : Q₀, orderOf x = 4 := by
  rcases original_bTwo_beta_linear_or_small_unitary h hb c hactor hcentral ht hne
    hcomm hnot E with ⟨n,hn,hm⟩ | hp | hs
  · obtain ⟨K,hK,hfin,hcard,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact Or.inr (Or.inr ⟨n,hn,⟨K,hK,hfin,hcard,⟨e⟩⟩,
      original_bTwo_exceptional_nonbinary_core h hb c hactor hcentral
        ht hne hcomm.le hnot e hD E hk⟩)
  · exact Or.inl hp
  · exact Or.inr (Or.inl hs)

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- Earlier center actions supply centrality for the original nonbinary consumer, retaining the full endpoint and Borel normalizers. -/
theorem original_bTwo_exceptional_nonbinary_of_center_family
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
      (Z F₀ α).map (G₀ L S).subtype) (hk : 2 < Nat.card k) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    P₀ L S 0 ≤ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (D₀ : Set G) ∧
      (ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
        IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
        ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
          IsMulCommutative Q₀ ∧
          (frattini Q₀).map Q₀.subtype = (Z F₀ α).map (G₀ L S).subtype ∧
          (∀ x : Q₀, x ^ 4 = 1) ∧ ∃ x : Q₀, orderOf x = 4) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne
    hnot hcenters
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right,
    original_bTwo_exceptional_nonbinary_or_small_unitary h hb c hactor hcentral
      ht htne hcomm (hnot β c.middle.symm) hD E hk⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
