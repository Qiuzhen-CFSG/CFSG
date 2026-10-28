module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearSeedSource
public import Theory.Frattini.OmegaProducts

/-!
# Clause (10.7)(c) on the original F1.11 beta core

The reduced-completion inclusion maps the beta-core product to the original
full endpoint core and the literal neighboring-core intersection D_alpha.
Frattini subgroups are transported by its induced subgroup equivalence,
so both the Frattini and derived subgroups are the original beta-center
image. The exact commutator identity is the earlier (7.4)(d) conclusion,
proved in Noncommuting.CenterCommutators and EpsilonTwoCenters.

The center-family application discharges centrality with the proved
characteristic-two exclusion and retains the full endpoint and Borel
normalizers. In the actual linear beta branch, the final layer calculation
also uses the proved saturation and beta-field index. General beta-model
selection, saturation and (10.8)--(10.10) remain source obligations; no
parabolic recognition or field equality is assumed here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(7.4)(d), p.128, (10.7), pp.158--159, and the original/reduced markings,
pp.95--96.
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

private theorem frattini_image_map {H : Type*} [Group H] (A : Subgroup H)
    (f : H →* G) (hf : Function.Injective f) :
    (frattini (A.map f)).map (A.map f).subtype =
      ((frattini A).map A.subtype).map f := by
  let e := A.equivMapOfInjective f hf
  have hh := congrArg (map (A.map f).subtype) (frattini_map_equiv e)
  rw [map_map] at hh
  have he : (A.map f).subtype.comp e.toMonoidHom = f.comp A.subtype := by ext; rfl
  rw [he,←map_map] at hh
  exact hh.symm

/-- The beta-core product on the literal original full endpoint. -/
theorem original_bTwo_beta_core_product
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (ht : (graph F₀).Adj α t) (hne : t ≠ β) :
    (parabolic L S 1).pCoreIn 2 =
      (V F₀ β 1).map (G₀ L S).subtype ⊔
        ((parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype) := by
  have hh := congrArg (map (G₀ L S).subtype)
    (c.beta_core_product (reduced_triple h) (reduced_kernel_sylow h) hb ht hne)
  change (Q F₀ β).map (G₀ L S).subtype =
    (V F₀ β 1 ⊔ (Q F₀ β ⊓ Q F₀ t)).map (G₀ L S).subtype at hh
  simpa only [Subgroup.map_sup,map_inf _ _ _ (G₀ L S).subtype_injective,
    reduced_base_Q_map h true,↓reduceIte] using hh

/-- The Frattini and derived subgroups of the original beta core are its marked center. -/
theorem original_bTwo_beta_core_frattini
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β) :
    let Q₁ := (parabolic L S 1).pCoreIn 2
    (frattini Q₁).map Q₁.subtype = (Z F₀ β).map (G₀ L S).subtype ∧
      ⁅Q₁,Q₁⁆ = (Z F₀ β).map (G₀ L S).subtype := by
  obtain ⟨hPhi,hder⟩ := c.beta_core_frattini_eq (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm
  change (frattini (Q F₀ β)).map (Q F₀ β).subtype = Z F₀ β at hPhi
  change ⁅Q F₀ β,Q F₀ β⁆ = Z F₀ β at hder
  have hp := frattini_image_map (Q F₀ β) (G₀ L S).subtype (G₀ L S).subtype_injective
  rw [hPhi,reduced_base_Q_map h true] at hp
  have hd := congrArg (map (G₀ L S).subtype) hder
  rw [map_commutator,reduced_base_Q_map h true] at hd
  exact ⟨hp,hd⟩

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- Apply both core calculations to the actual linear beta quotient. The numerical
parameter is the beta field; the alpha field only supplies the stated bound. -/
theorem original_bTwo_linear_core_layers
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F₀ t).map (G₀ L S).subtype
    let Z₁ := (Z F₀ β).map (G₀ L S).subtype
    Q₁ = (V F₀ β 1).map (G₀ L S).subtype ⊔ D₀ ∧
      (frattini Q₁).map Q₁.subtype = Z₁ ∧ ⁅Q₁,Q₁⁆ = Z₁ ∧
      Nat.card k ≤ Nat.card K ∧
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
        Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = Nat.card K ^ 2 := by
  have hbeta := original_bTwo_beta_core_frattini h hb c hactor hcentral ht hne hcomm
  exact ⟨original_bTwo_beta_core_product h hb c ht hne,hbeta.1,hbeta.2,
    original_bTwo_linear_central_core h hb c hactor hcentral ht hne hcomm.le hnot e⟩

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance betaCoreAlgebra {F : Type*} [Field F] [CharP F 2] : Algebra (ZMod 2) F :=
  ZMod.algebra F 2

/-- The earlier center family supplies centrality and hence the original beta-core
structure, with the full reduced endpoint and Borel normalizing the same D_alpha. -/
theorem original_bTwo_beta_core_of_center_family
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
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β) :
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F₀ t).map (G₀ L S).subtype
    let Z₁ := (Z F₀ β).map (G₀ L S).subtype
    Q₁ = (V F₀ β 1).map (G₀ L S).subtype ⊔ D₀ ∧
      (frattini Q₁).map Q₁.subtype = Z₁ ∧ ⁅Q₁,Q₁⁆ = Z₁ ∧
      P₀ L S 0 ≤ normalizer (D₀ : Set G) ∧ B₀ L S ≤ normalizer (D₀ : Set G) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  have hbeta := original_bTwo_beta_core_frattini h hb c hactor hcentral ht htne hcomm
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨original_bTwo_beta_core_product h hb c ht htne,hbeta.1,hbeta.2,
    hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
