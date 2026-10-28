module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearModule
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearSeedSource

/-!
# The full alpha-core module on the original F1.11 endpoints

The actual original beta quotient marking supplies the linear branch.
Transport the proved natural-copy consequences through the literal inclusion
of the reduced completion: the beta field order is a positive power of the
alpha field order, and a nonidentity odd-order quotient actor fixes no
original core element outside the original neighboring-core denominator.
The same inclusion identifies the W_alpha centralizer inside the whole
original alpha core with its centralizer inside D_alpha.

The final application uses the earlier center family to discharge the
central-branch hypothesis and retains the full endpoint and Borel
normalizers. No saturation premise, new action witness, field equality,
or exceptional recognition is supplied as an assumption. The genuine
earlier Chapter 6--7 inputs and the actual linear beta marking remain;
general beta-model selection and (10.8)--(10.10) remain source obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7)--(10.10), pp.158--165, and the reduced/original markings, pp.95--96.
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

private def betaModuleQuotient (h : HypothesisF11 L S)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    (graphLocalGroup F₀ β ⧸ pCore 2 (graphLocalGroup F₀ β)) ≃* SL(2,K) :=
  (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm

/-- The actual beta field is a positive power of the alpha field, with no restriction
of the multiplicity to one or three. -/
theorem original_bTwo_linear_field_power
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    ∃ n : ℕ, 0 < n ∧ Nat.card K = Nat.card k ^ n :=
  c.linear_core_field_power (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot (betaModuleQuotient h e)

/-- The odd-actor fixed-point calculation on the original full alpha core,
with the original inclusion and the literal neighboring-core denominator. -/
theorem original_bTwo_linear_odd_fixed
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (a : c.actor) (ho : Odd (orderOf (c.quotient a))) (ha : c.quotient a ≠ 1)
    (x : G) (hx : x ∈ (parabolic L S 0).pCoreIn 2)
    (hax : ⁅x,((a : G₀ L S) : G)⁆ ∈
      (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype) :
    x ∈ (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype := by
  let ι := (G₀ L S).subtype
  have hDm : (D F₀ β t).map ι =
      (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map ι := by
    change (Q F₀ β ⊓ Q F₀ t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hQm : (Q F₀ α).map ι = (parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  rw [←hQm] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  have hya : ⁅y,(a : G₀ L S)⁆ ∈ D F₀ β t := by
    have hh : ι ⁅y,(a : G₀ L S)⁆ ∈ (D F₀ β t).map ι := by
      rw [map_commutatorElement,hDm]
      exact hax
    exact (mem_map_iff_mem (G₀ L S).subtype_injective).mp hh
  rw [←hDm]
  exact mem_map_of_mem ι (c.linear_core_odd_fixed (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht hne
    hcomm hnot (betaModuleQuotient h e) a ho ha y hy hya)

/-- The source W_alpha centralizer computed inside the original full core is
exactly its centralizer inside the original D_alpha. -/
theorem original_bTwo_linear_residual_centralizer
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    ∃ g : c.actor, (g : G₀ L S) • β = t ∧
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
      let W₀ := (Z F₀ u).map (G₀ L S).subtype ⊔
        (Z F₀ ((g : G₀ L S) • u)).map (G₀ L S).subtype
      (parabolic L S 0).pCoreIn 2 ⊓ centralizer (W₀ : Set G) =
        D₀ ⊓ centralizer (W₀ : Set G) := by
  obtain ⟨g,hg,he⟩ := c.linear_core_residual_centralizer (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht hne
    hcomm hnot (betaModuleQuotient h e)
  have hh := congrArg (map (G₀ L S).subtype) he
  change (Q F₀ α ⊓ centralizer ((Z F₀ u ⊔ Z F₀ ((g : G₀ L S) • u) :
    Subgroup (G₀ L S)) : Set (G₀ L S))).map (G₀ L S).subtype =
      ((Q F₀ β ⊓ Q F₀ t) ⊓ centralizer ((Z F₀ u ⊔ Z F₀ ((g : G₀ L S) • u) :
        Subgroup (G₀ L S)) : Set (G₀ L S))).map (G₀ L S).subtype at hh
  rw [←map_inf_centralizer_of_injective (G₀ L S).subtype (G₀ L S).subtype_injective,
    ←map_inf_centralizer_of_injective (G₀ L S).subtype (G₀ L S).subtype_injective,
    Subgroup.map_sup,map_inf _ _ _ (G₀ L S).subtype_injective,
    reduced_base_Q_map h false,reduced_base_Q_map h true] at hh
  exact ⟨g,hg,hh⟩

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance linearModuleSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-- Apply the whole-core module calculation after the earlier center family has
supplied the central branch. Keep the literal original core, D, both full
normalizers, and every earlier source input. -/
theorem original_bTwo_linear_module_of_center_family
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F₀ α u) (hnoncomm : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F₀).Adj y α →
      ¬ stabilizer F₀ α ≤ normalizer
        ((Q F₀ y ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F₀).Adj y α → IsCriticalPair F₀ β y →
      ⁅Z F₀ β,Z F₀ y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F₀ β α y k₁ W₁))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    (∃ n : ℕ, 0 < n ∧ Nat.card K = Nat.card k ^ n) ∧
      P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      (∀ a : c.actor, Odd (orderOf (c.quotient a)) → c.quotient a ≠ 1 →
        ∀ x ∈ Q₀, ⁅x,((a : G₀ L S) : G)⁆ ∈ D₀ → x ∈ D₀) ∧
      ∃ g : c.actor, (g : G₀ L S) • β = t ∧
        let W₀ := (Z F₀ u).map (G₀ L S).subtype ⊔
          (Z F₀ ((g : G₀ L S) • u)).map (G₀ L S).subtype
        Q₀ ⊓ centralizer (W₀ : Set G) = D₀ ⊓ centralizer (W₀ : Set G) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc
    hnoncomm hnot hcenters
  have hlocal := hnot β c.middle.symm
  have hs := (original_bTwo_linear_seed_and_indices h hb c ht hne hlocal e).1
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht hne
  dsimp only at hnorm
  rw [hs] at hnorm
  exact ⟨original_bTwo_linear_field_power h hb c hactor hcentral ht hne hcomm hlocal e,
    hnorm.1,hnorm.2,
    fun a ho ha x hx hax => original_bTwo_linear_odd_fixed h hb c hactor hcentral ht hne
      hcomm hlocal e a ho ha x hx hax,
    original_bTwo_linear_residual_centralizer h hb c hactor hcentral ht hne hcomm hlocal e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
