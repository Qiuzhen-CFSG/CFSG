module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSuzukiSeed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntersectionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SuzukiEnlargement

/-!
# The nonlinear seed obstruction on the original F1.11 cores

The original Suzuki beta quotient is carried to the reduced graph by the
proved literal starred-inclusion map. Injectivity of the reduced-completion
inclusion then transports all the seed, adjacent-core and D indices to the
original full cores. The seed is a proper subgroup of the original alpha
core, of index q_beta, and its D index is q_beta squared; the full alpha
core has D index q_beta cubed.

The center-family application discharges beta centrality through the
characteristic-two noncentral exclusion and retains both full endpoint and
Borel normalizers. Earlier (6.5), (7.1), and (7.4) inputs remain explicit.
These statements describe the hypothetical nonbinary Suzuki branch; they
do not exclude it or prove the general saturation needed in (10.7).

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (10.7), pp.158--159, and the original/reduced markings, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- The nonlinear seed calculation on the original full cores, retaining
the actual original Suzuki quotient and the neighboring-core denominator. -/
theorem original_bTwo_suzuki_seed_structure
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    {n : ℕ} (hn : 0 < n) (e : (L 1 ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup n) :
    let q := 2^(2*n+1)
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F₀ t).map (G₀ L S).subtype
    let J₀ := (centralSeed F₀ α β t).map (G₀ L S).subtype
    Nat.card k ≤ q ∧ D₀.relIndex (Q₀ ⊓ Q₁) = q ∧
      D₀.relIndex J₀ = q^2 ∧ J₀.relIndex Q₀ = q ∧
      D₀.relIndex Q₀ = q^3 ∧ J₀ < Q₀ := by
  obtain ⟨hbound,hiI,hiJ,hiQ,hiD,hneJ⟩ := c.suzuki_seed_structure (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot hn
    (reduced_graphSuzukiQuotient h true hn e)
  let ι := (G₀ L S).subtype
  have hDm : (D F₀ β t).map ι =
      (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map ι := by
    change (Q F₀ β ⊓ Q F₀ t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hIm : (Q F₀ α ⊓ Q F₀ β).map ι =
      (parabolic L S 0).pCoreIn 2 ⊓ (parabolic L S 1).pCoreIn 2 := by
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,
      reduced_base_Q_map h false,reduced_base_Q_map h true]
    rfl
  have map_index (A C : Subgroup (G₀ L S)) :
      (A.map ι).relIndex (C.map ι) = A.relIndex C :=
    relIndex_map_map_of_injective A C (G₀ L S).subtype_injective
  have hI := (map_index (D F₀ β t) (Q F₀ α ⊓ Q F₀ β)).trans hiI
  have hJ := (map_index (D F₀ β t) (centralSeed F₀ α β t)).trans hiJ
  have hQ := (map_index (centralSeed F₀ α β t) (Q F₀ α)).trans hiQ
  have hD := (map_index (D F₀ β t) (Q F₀ α)).trans hiD
  rw [hDm,hIm] at hI
  rw [hDm] at hJ
  rw [reduced_base_Q_map h false] at hQ
  rw [hDm,reduced_base_Q_map h false] at hD
  refine ⟨hbound,hI,hJ,hQ,hD,?_⟩
  have hseed := c.seed_eq_core_intersections (reduced_triple h) (reduced_kernel_sylow h) hb ht hne
  change centralSeed F₀ α β t = (Q F₀ α ⊓ Q F₀ β) ⊔ (Q F₀ α ⊓ Q F₀ t) at hseed
  have hle : centralSeed F₀ α β t ≤ Q F₀ α := by
    rw [hseed]
    exact sup_le inf_le_left inf_le_left
  apply lt_of_le_of_ne
  · exact (map_mono hle).trans_eq (reduced_base_Q_map h false)
  · intro he
    apply hneJ
    apply map_injective (f := ι) (G₀ L S).subtype_injective
    exact he.trans (reduced_base_Q_map h false).symm

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance suzukiSeedAlgebra {F : Type*} [Field F] [CharP F 2] : Algebra (ZMod 2) F :=
  ZMod.algebra F 2

/-- The earlier center-action family supplies centrality. Both original
endpoint and full Borel markings are retained with the proper seed. -/
theorem original_bTwo_suzuki_seed_of_center_family
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
    {n : ℕ} (hn : 0 < n) (e : (L 1 ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup n) :
    let q := 2^(2*n+1)
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F₀ t).map (G₀ L S).subtype
    let J₀ := (centralSeed F₀ α β t).map (G₀ L S).subtype
    P₀ L S 0 ≤ normalizer (J₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (J₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      Nat.card k ≤ q ∧ D₀.relIndex (Q₀ ⊓ Q₁) = q ∧
      D₀.relIndex J₀ = q^2 ∧ J₀.relIndex Q₀ = q ∧
      D₀.relIndex Q₀ = q^3 ∧ J₀ < Q₀ := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  have hlayers := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨hlayers.1,hlayers.2,original_bTwo_suzuki_seed_structure h hb c hactor hcentral
    ht htne hcomm (hnot β c.middle.symm) hn e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
