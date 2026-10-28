module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntrinsic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCentralApplication

/-!
# Moving central seed layers with the original F1.11 markings

Transport the full core-to-seed residual displacement and the nontrivial
seed-to-D displacement through the actual reduced-completion inclusion.
The embedded residual becomes exactly O^2 of the original enlarged
endpoint, and the denominator retains the original neighboring core.
Only local finiteness is used in this residual transport.

The intrinsic layer descriptions give normalization by the entire
reduced endpoint and its full Borel. The final application constructs the
quadratic, fixed-generated moving seed representation after discharging
centrality by the proved characteristic-two 10.6 exclusion. The earlier
6.5 obstruction and Chapter 7 action/commutator inputs remain explicit.
Seed saturation, the field parameter and 10.8--10.10 remain obligations.
Source: DGS, Groups and Graphs (1985), 10.4 and10.7, pp.155--159,
and the source-to-reduced markings on pp.95--96.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

private theorem map_local_residual {H : Type*} [Group H]
    (M : Subgroup H) [Finite M] (f : H →* G) :
    ((pResidual 2 M).map M.subtype).map f =
      (pResidual 2 (M.map f)).map (M.map f).subtype := by
  calc
    _ = ((pResidual 2 M).map (f.subgroupMap M)).map (M.map f).subtype := by
      rw [map_map,map_map]
      rfl
    _ = _ := by
      rw [map_pResidual_of_surjective 2 (f.subgroupMap M) (f.subgroupMap_surjective M)]

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- The original full endpoint residual moves its original core into the
marked seed, and moves that seed nontrivially modulo the literal D. -/
theorem original_bTwo_seed_residual_movement
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    let J₀ := (centralSeed F₀ α β t).map (G₀ L S).subtype
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    let R₀ := (pResidual 2 (enlargedEndpoint L S 0)).map (enlargedEndpoint L S 0).subtype
    ⁅(parabolic L S 0).pCoreIn 2,R₀⁆ ≤ J₀ ∧ ¬ ⁅J₀,R₀⁆ ≤ D₀ := by
  let : ∀ i, Finite (F₀ i) := finite_endpoints (reduced_triple h)
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  let ι := (G₀ L S).subtype
  have hAm : c.actor.map ι = enlargedEndpoint L S 0 := by
    rw [hactor,reduced_graphLocalGroup_image h false]
    rfl
  have hRm : ((pResidual 2 c.actor).map c.actor.subtype).map ι =
      (pResidual 2 (enlargedEndpoint L S 0)).map (enlargedEndpoint L S 0).subtype := by
    rw [map_local_residual,hAm]
  have hDm : (D F₀ β t).map ι =
      (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map ι := by
    change (Q F₀ β ⊓ Q F₀ t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift (reduced_triple h) ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry (reduced_triple h)
    (reduced_kernel_sylow h) hb g hg hop
  have hmove := d.core_residual_le_seed (reduced_triple h) (reduced_kernel_sylow h)
    hb (hd.symm ▸ c.actor_le)
  rw [hd] at hmove
  change ⁅Q F₀ α,(pResidual 2 c.actor).map c.actor.subtype⁆ ≤ centralSeed F₀ α β t at hmove
  constructor
  · have hm := map_mono (f := ι) hmove
    rwa [map_commutator,hRm,reduced_base_Q_map h false] at hm
  · intro htriv
    apply c.seed_residual_not_le_D (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb ht hne hnot
    change ⁅centralSeed F₀ α β t,(pResidual 2 c.actor).map c.actor.subtype⁆ ≤ D F₀ β t
    apply (Subgroup.map_le_map_iff_of_injective (G₀ L S).subtype_injective).mp
    rw [map_commutator,hRm,hDm]
    exact htriv

/-- Both literal seed layers are normalized by the entire reduced endpoint
inside the original completion, with its full reduced Borel retained. -/
theorem original_bTwo_seed_layers_normalized
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (ht : (graph F₀).Adj α t) (hne : t ≠ β) :
    let J₀ := (centralSeed F₀ α β t).map (G₀ L S).subtype
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    P₀ L S 0 ≤ normalizer (J₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (J₀ : Set G) ⊓ normalizer (D₀ : Set G) := by
  let ι := (G₀ L S).subtype
  have hPm : (stabilizer F₀ α).map ι = P₀ L S 0 := by
    rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    change ((P₀ L S 0).subgroupOf (G₀ L S)).map ι = P₀ L S 0
    exact map_subgroupOf_eq_of_le le_sup_left
  have hDm : (D F₀ β t).map ι =
      (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map ι := by
    change (Q F₀ β ⊓ Q F₀ t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hnD := c.D_stabilizer_normalized (reduced_triple h) (reduced_kernel_sylow h) hb ht hne
  have hnJ := c.seed_stabilizer_normalized (reduced_triple h) (reduced_kernel_sylow h) hb ht hne
  change stabilizer F₀ α ≤ normalizer (D F₀ β t : Set (G₀ L S)) at hnD
  change stabilizer F₀ α ≤ normalizer (centralSeed F₀ α β t : Set (G₀ L S)) at hnJ
  have hD := (map_mono (f := ι) hnD).trans (le_normalizer_map ι)
  have hJ := (map_mono (f := ι) hnJ).trans (le_normalizer_map ι)
  rw [hPm,hDm] at hD
  rw [hPm] at hJ
  exact ⟨le_inf hJ hD,(show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans (le_inf hJ hD)⟩

local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The actual F1.11 central seed module has the corrected fixed-generation
property and nontrivial residual action. The proved 10.6 exclusion supplies
centrality; only the earlier 6.5/7.1/7.4 source inputs remain explicit. -/
theorem original_bTwo_seed_moving_module_of_center_family
    {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
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
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β) :
    ∃ hN : ((D F₀ β t).subgroupOf (centralSeed F₀ α β t)).Normal,
      letI := hN
      ∃ hE : IsElementaryAbelian 2 (centralSeed F₀ α β t ⧸
        (D F₀ β t).subgroupOf (centralSeed F₀ α β t)),
      letI := hE
      ∃ ρ : Representation (ZMod 2) c.actor (Additive (centralSeed F₀ α β t ⧸
        (D F₀ β t).subgroupOf (centralSeed F₀ α β t))),
        Nonempty (BinaryConjugationSection c.actor
          (centralSeed F₀ α β t) (D F₀ β t) ρ) ∧
        IsQuadratic ρ ((V F₀ β 1).subgroupOf c.actor) ∧
        GeneratedByFixedSpace ρ ((V F₀ β 1).subgroupOf c.actor) ∧
        fixedSpace ρ (pResidual 2 c.actor) ≠ ⊤ ∧
        ¬ ⁅(centralSeed F₀ α β t).map (G₀ L S).subtype,
          (pResidual 2 (enlargedEndpoint L S 0)).map (enlargedEndpoint L S 0).subtype⁆ ≤
          (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  obtain ⟨hN,hE,ρ,e,hq,hgen,hmove⟩ := c.central_seed_moving_representation
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor
    hcentral ht htne hcomm (hnot β c.middle.symm)
  exact ⟨hN,hE,ρ,e,hq,hgen,hmove,(original_bTwo_seed_residual_movement h hb c hactor ht htne
    (hnot β c.middle.symm)).2⟩

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
