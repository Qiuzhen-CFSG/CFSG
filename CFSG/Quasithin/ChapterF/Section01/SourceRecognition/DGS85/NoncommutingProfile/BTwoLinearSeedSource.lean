module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearSeed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntersectionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement

/-!
# The linear branch of (10.7) on the original F1.11 endpoints

The beta quotient is marked on the original local factor. Its proved
transport to the reduced graph supplies the actual quotient map used by
seed saturation. The resulting core and factor indices use q_beta, while
the alpha field supplies only a lower bound. Injectivity of the literal
reduced-completion inclusion transports the elementary quotient to the
original full alpha core and the original neighboring-core intersection D.

The final center-family application discharges centrality using the proved
characteristic-two exclusion. It retains the full reduced endpoint and
Borel normalizers and the genuine earlier 6.5/7.1/7.4 inputs. The general
beta-model selection and the (10.8)--(10.10) classification remain separate
source obligations; no exceptional recognition is assumed or asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7), pp.158--159, with the original/reduced markings on pp.95--96.
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

private def betaLinearEquiv (h : HypothesisF11 L S)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    (graphLocalGroup F₀ β ⧸ pCore 2 (graphLocalGroup F₀ β)) ≃* SL(2,K) :=
  (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm

/-- Saturation and the two beta-field indices, with the original full endpoint cores. -/
theorem original_bTwo_linear_seed_and_indices
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    (centralSeed F₀ α β t).map (G₀ L S).subtype = (parabolic L S 0).pCoreIn 2 ∧
      ((parabolic L S 1).pCoreIn 2).relIndex ((parabolic L S 0).pCoreIn 2) = Nat.card K ∧
      ((parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype).relIndex
        ((parabolic L S 0).pCoreIn 2 ⊓ (parabolic L S 1).pCoreIn 2) = Nat.card K := by
  obtain ⟨hs,hi⟩ := c.linear_seed_eq_core_and_index (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) (reduced_kernel_sylow h)
    hb ht hne hnot (betaLinearEquiv h e)
  have hf := c.linear_seed_factor_index (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) (reduced_kernel_sylow h)
    hb ht hne hnot (betaLinearEquiv h e)
  have hs' : centralSeed F₀ α β t = Q F₀ α := hs
  refine ⟨?_,?_,?_⟩
  · rw [hs',reduced_base_Q_map h false]
    rfl
  · have hh := relIndex_map_map_of_injective (f := (G₀ L S).subtype)
      (Q F₀ β) (Q F₀ α) (G₀ L S).subtype_injective
    rw [reduced_base_Q_map h false,reduced_base_Q_map h true] at hh
    exact hh.trans hi
  · have hh := relIndex_map_map_of_injective (f := (G₀ L S).subtype)
      (D F₀ β t) (Q F₀ α ⊓ Q F₀ β) (G₀ L S).subtype_injective
    change ((Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype).relIndex
      ((Q F₀ α ⊓ Q F₀ β).map (G₀ L S).subtype) = _ at hh
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,
      map_inf _ _ _ (G₀ L S).subtype_injective,
      reduced_base_Q_map h false,reduced_base_Q_map h true] at hh
    exact hh.trans hf

private theorem map_elementary_section {H : Type*} [Group H]
    (A D : Subgroup H) (hDA : D ≤ A) [(D.subgroupOf A).Normal]
    [IsElementaryAbelian 2 (A ⧸ D.subgroupOf A)] (f : H →* G) (hf : Function.Injective f) :
    ∃ hN : ((D.map f).subgroupOf (A.map f)).Normal,
      letI := hN
      IsElementaryAbelian 2 (A.map f ⧸ (D.map f).subgroupOf (A.map f)) ∧
      Nat.card (A.map f ⧸ (D.map f).subgroupOf (A.map f)) = Nat.card (A ⧸ D.subgroupOf A) := by
  let e := A.equivMapOfInjective f hf
  have he : (D.subgroupOf A).map e.toMonoidHom = (D.map f).subgroupOf (A.map f) := by
    apply map_injective (A.map f).subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (map_mono hDA)]
    change (D.subgroupOf A).map (f.comp A.subtype) = D.map f
    rw [←map_map,map_subgroupOf_eq_of_le hDA]
  have hN : ((D.map f).subgroupOf (A.map f)).Normal :=
    he ▸ (inferInstance : (D.subgroupOf A).Normal).map e.toMonoidHom e.surjective
  let := hN
  let eqv := QuotientGroup.congr (D.subgroupOf A) ((D.map f).subgroupOf (A.map f)) e he
  exact ⟨hN,IsElementaryAbelian.of_surjective eqv.toMonoidHom eqv.surjective,
    (Nat.card_congr eqv.toEquiv).symm⟩

/-- The elementary quotient of the ORIGINAL alpha core has order q_beta squared.
The original beta quotient marking discharges saturation and the numerical index. -/
theorem original_bTwo_linear_central_core
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    Nat.card k ≤ Nat.card K ∧
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
        Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = Nat.card K ^ 2 := by
  obtain ⟨hbound,hN,hE,hcard⟩ := c.linear_central_core_structure (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht hne
    hcomm hnot (betaLinearEquiv h e)
  let : ((D F₀ β t).subgroupOf (Q F₀ α)).Normal := hN
  let : IsElementaryAbelian 2 (Q F₀ α ⧸ (D F₀ β t).subgroupOf (Q F₀ α)) := hE
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift (reduced_triple h) ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry (reduced_triple h)
    (reduced_kernel_sylow h) hb g hg hop
  have hh := map_elementary_section (Q F₀ α) (D F₀ β t)
    d.separated (G₀ L S).subtype (G₀ L S).subtype_injective
  have hDm : (D F₀ β t).map (G₀ L S).subtype =
      (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype := by
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  rw [hDm,reduced_base_Q_map h false] at hh
  obtain ⟨hN',hE',hcard'⟩ := hh
  exact ⟨hbound,hN',hE',hcard'.trans hcard⟩


variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance linearSeedAlgebra {F : Type*} [Field F] [CharP F 2] : Algebra (ZMod 2) F :=
  ZMod.algebra F 2

/-- Apply the linear beta marking and the earlier center-action family to
the literal original core quotient. Characteristic-two exclusion supplies
centrality; the original reduced endpoint and full Borel normalize both layers. -/
theorem original_bTwo_linear_core_of_center_family
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F₀).Adj y α →
      ¬ stabilizer F₀ α ≤ normalizer ((Q F₀ y ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F₀).Adj y α → IsCriticalPair F₀ β y →
      ⁅Z F₀ β,Z F₀ y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F₀ β α y k₁ W₁))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    (centralSeed F₀ α β t).map (G₀ L S).subtype = Q₀ ∧
      P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      Nat.card k ≤ Nat.card K ∧
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
        Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = Nat.card K ^ 2 := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  have hs := (original_bTwo_linear_seed_and_indices h hb c ht htne (hnot β c.middle.symm) e).1
  have hlayers := original_bTwo_seed_layers_normalized h hb c ht htne
  dsimp only at hlayers
  rw [hs] at hlayers
  exact ⟨hs,hlayers.1,hlayers.2,original_bTwo_linear_central_core h hb c hactor
    hcentral ht htne hcomm (hnot β c.middle.symm) e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
