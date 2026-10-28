module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearModuleSource

/-!
# Exceptional core calculations on the original F1.11 endpoints

The literal reduced-completion inclusion transports Q_beta = V_beta,
both core orders, and the common core-product order to the original full
endpoint cores. The constructed cubic remains an ambient element of order
three, and its conjugation on the original alpha core gives an automorphism
of exact order three fixing only the identity. Nontriviality of that core
comes from the actual source center span.

The final application uses the earlier center-action family to discharge
centrality and retains the full endpoint and Borel normalizers. The actual
linear beta quotient and exceptional equality D_alpha = Z_alpha remain
explicit branch hypotheses. No exceptional model recognition, field bound,
path parameter, or equality with the original unreduced Sylow is asserted.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (10.9), printed pp.162--163; reduced/original markings, pp.95--96.
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
local instance cubicSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

private def betaCubicQuotient (h : HypothesisF11 L S)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    (graphLocalGroup F₀ β ⧸ pCore 2 (graphLocalGroup F₀ β)) ≃* SL(2,K) :=
  (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm

/-- The beta core at the original full endpoint is the original radius-one image. -/
theorem original_bTwo_exceptional_beta_core
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (ht : (graph F₀).Adj α t) (hne : t ≠ β) (hD : D F₀ β t = Z F₀ α) :
    (parabolic L S 1).pCoreIn 2 = (V F₀ β 1).map (G₀ L S).subtype := by
  have he : Q F₀ β = V F₀ β 1 :=
    c.exceptional_beta_core (reduced_triple h) (reduced_kernel_sylow h) hb ht hne hD
  have hh := congrArg (map (G₀ L S).subtype) he
  simpa only [reduced_base_Q_map h true,↓reduceIte] using hh

/-- Both original full-core orders, with the alpha and beta field markings kept distinct. -/
theorem original_bTwo_exceptional_linear_core_orders
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : D F₀ β t = Z F₀ α) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card ((parabolic L S 0).pCoreIn 2) = Nat.card k ^ 2 * Nat.card K ^ 2 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) = Nat.card k ^ 3 * Nat.card K := by
  have hc := c.exceptional_linear_core_orders (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot (betaCubicQuotient h e) hD E
  have hcard (i : Bool) :
      Nat.card ((parabolic L S (if i then 1 else 0)).pCoreIn 2) =
        Nat.card (Q F₀ (base F₀ i)) := by
    rw [←reduced_base_Q_map h i]
    exact (Nat.card_congr ((Q F₀ (base F₀ i)).equivMapOfInjective
      (G₀ L S).subtype (G₀ L S).subtype_injective).toEquiv).symm
  exact ⟨(hcard false).trans hc.1,(hcard true).trans hc.2⟩

/-- The constructed cubic acts by literal ambient conjugation on the original
full core; its fixed-point-free property is transported through that inclusion. -/
theorem original_bTwo_exceptional_linear_cubic
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hD : D F₀ β t = Z F₀ α) :
    ∃ a : c.actor, orderOf ((a : G₀ L S) : G) = 3 ∧ orderOf (c.quotient a) = 3 ∧
      ∃ φ : MulAut ((parabolic L S 0).pCoreIn 2), orderOf φ = 3 ∧
        (∀ x, (φ x : G) = ((a : G₀ L S) : G) * (x : G) * ((a : G₀ L S) : G)⁻¹) ∧
        (∀ x, φ x = x → x = 1) := by
  obtain ⟨a,ha,hqa,hcube,hfree⟩ := c.exceptional_linear_cubic (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht hne
    hcomm hnot (betaCubicQuotient h e) hD
  change ∀ x : Q F₀ α, c.coreConjugation a x = x → x = 1 at hfree
  let ι := (G₀ L S).subtype
  let eQ : Q F₀ α ≃* (parabolic L S 0).pCoreIn 2 :=
    ((Q F₀ α).equivMapOfInjective ι (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_base_Q_map h false))
  let ψ : MulAut (Q F₀ α) := c.coreConjugation a
  let φ : MulAut ((parabolic L S 0).pCoreIn 2) := MulAut.congr eQ ψ
  have hao : orderOf ((a : G₀ L S) : G) = 3 := by
    exact (orderOf_injective ι (G₀ L S).subtype_injective (a : G₀ L S)).trans
      ((orderOf_injective c.actor.subtype c.actor.subtype_injective a).trans ha)
  have hφcube : φ^3 = 1 :=
    (map_pow (MulAut.congr eQ) ψ 3).symm.trans
      ((congrArg (MulAut.congr eQ) hcube).trans (MulAut.congr eQ).map_one)
  have hφfree : ∀ x, φ x = x → x = 1 := by
    intro x hx
    obtain ⟨y,rfl⟩ := eQ.surjective x
    have hy : c.coreConjugation a y = y := by
      apply eQ.injective
      change eQ (c.coreConjugation a (eQ.symm (eQ y))) = eQ y at hx
      simpa only [eQ.symm_apply_apply] using hx
    exact (congrArg eQ (hfree y hy)).trans eQ.map_one
  have hφne : φ ≠ 1 := by
    intro hφ
    have hZ : Z F₀ α ≠ ⊥ := base_Z_ne_bot (reduced_triple h) false
    obtain ⟨z,hz,hz1⟩ := (Z F₀ α).bot_or_exists_ne_one.resolve_left hZ
    have hzQ : z ∈ Q F₀ α :=
      ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U (reduced_triple h) α).1 hz)).1
    let x : Q F₀ α := ⟨z,hzQ⟩
    have hx : eQ x = 1 := hφfree _ (by rw [hφ]; rfl)
    have hx1 : x = 1 := eQ.injective (hx.trans eQ.map_one.symm)
    exact hz1 (congrArg (fun y : Q F₀ α => (y : G₀ L S)) hx1)
  refine ⟨a,hao,hqa,φ,orderOf_eq_prime hφcube hφne,?_,hφfree⟩
  intro x
  obtain ⟨y,rfl⟩ := eQ.surjective x
  change (eQ (ψ (eQ.symm (eQ y))) : G) = _
  rw [eQ.symm_apply_apply]
  change ι (ψ y : G₀ L S) = _
  have he : (ψ y : G₀ L S) = (a : G₀ L S) * (y : G₀ L S) * (a : G₀ L S)⁻¹ :=
    c.coreConjugation_apply a y
  exact (congrArg ι he).trans (by simp only [map_mul,map_inv]; rfl)

/-- The original core product has the exact source Sylow order. It need not
be identified with the unreduced Sylow given in F1.11. -/
theorem original_bTwo_exceptional_linear_sylow_order
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : D F₀ β t = Z F₀ α) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card ((parabolic L S 1).pCoreIn 2 ⊔ (parabolic L S 0).pCoreIn 2 : Subgroup G) =
      Nat.card k ^ 3 * Nat.card K ^ 2 := by
  have hc := c.exceptional_linear_sylow_order (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht hne
    hcomm hnot (betaCubicQuotient h e) hD E
  have hm : (Q F₀ β ⊔ Q F₀ α).map (G₀ L S).subtype =
      (parabolic L S 1).pCoreIn 2 ⊔ (parabolic L S 0).pCoreIn 2 := by
    rw [Subgroup.map_sup,reduced_base_Q_map h true,reduced_base_Q_map h false]
    rfl
  rw [←hm]
  exact (Nat.card_congr ((Q F₀ β ⊔ Q F₀ α).equivMapOfInjective
    (G₀ L S).subtype (G₀ L S).subtype_injective).toEquiv).symm.trans hc

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- Apply the exceptional core calculations to the original F1.11 pair.
The earlier center family discharges beta centrality; full endpoint and
Borel normalizers and literal ambient cubic conjugation are retained. -/
theorem original_bTwo_exceptional_linear_of_center_family
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
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hD : D F₀ β t = Z F₀ α) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F₀ t).map (G₀ L S).subtype
    Q₁ = (V F₀ β 1).map (G₀ L S).subtype ∧
      Nat.card Q₀ = Nat.card k ^ 2 * Nat.card K ^ 2 ∧
      Nat.card Q₁ = Nat.card k ^ 3 * Nat.card K ∧
      Nat.card (Q₁ ⊔ Q₀ : Subgroup G) = Nat.card k ^ 3 * Nat.card K ^ 2 ∧
      P₀ L S 0 ≤ normalizer (D₀ : Set G) ∧ B₀ L S ≤ normalizer (D₀ : Set G) ∧
      ∃ a : c.actor, orderOf ((a : G₀ L S) : G) = 3 ∧ orderOf (c.quotient a) = 3 ∧
        ∃ φ : MulAut Q₀, orderOf φ = 3 ∧
          (∀ x, (φ x : G) = ((a : G₀ L S) : G) * (x : G) * ((a : G₀ L S) : G)⁻¹) ∧
          (∀ x, φ x = x → x = 1) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  have hobs := hnot β c.middle.symm
  have horders := original_bTwo_exceptional_linear_core_orders h hb c hactor hcentral
    ht htne hcomm hobs e hD E
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨original_bTwo_exceptional_beta_core h hb c ht htne hD,horders.1,horders.2,
    original_bTwo_exceptional_linear_sylow_order h hb c hactor hcentral ht htne hcomm hobs e hD E,
    hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right,
    original_bTwo_exceptional_linear_cubic h hb c hactor hcentral ht htne hcomm hobs e hD⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
