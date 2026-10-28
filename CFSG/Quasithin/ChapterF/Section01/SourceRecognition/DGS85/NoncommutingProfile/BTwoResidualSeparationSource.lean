module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidualSeparation
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Original-source center and residual separation calculations

Transport the critical center/core identities, neighboring-center direct
factors and beta-center order through the actual reduced-completion inclusion.
The two full original parabolic cores retain their literal markings.

The source subgroup tested in (10.8) is constructed inside the original
intersection D_alpha, with its centralizer taken on both original critical
center images. Its terminal displacement and centralization conclusions use
the image of the actual terminal O²-actor. No beta-model selection, saturation,
residual vanishing or exceptional recognition is assumed or asserted.

Source: DGS, Groups and Graphs (1985), (10.2)(c), p.154, and the first steps
of (10.8), pp.159--160. Earlier Chapter 7 marked center actions remain explicit
inputs for the source-assembly owner.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup
open scoped Pointwise commutatorElement
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance residualSeparationSourceAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The original center identities and (10.2)(c) splitting retain both
full endpoint cores and the chosen opposite-neighbor inclusion. -/
theorem original_bTwo_central_center_intersections
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β) :
    let Z₀ := (Z F₀ α).map (G₀ L S).subtype
    let Z₁ := (Z F₀ β).map (G₀ L S).subtype
    let Z' := (Z F₀ u).map (G₀ L S).subtype
    let Zt := (Z F₀ t).map (G₀ L S).subtype
    Z₀ ⊓ (Q F₀ u).map (G₀ L S).subtype = Z₁ ∧
      Z' ⊓ (parabolic L S 0).pCoreIn 2 = Z₁ ∧ Z₀ ⊓ Z' = Z₁ ∧
      Z₀ = Z₁ ⊔ Zt ∧ Disjoint Z₁ Zt ∧ Nat.card Z₁ = Nat.card k ∧
      Z₁ ≤ (parabolic L S 1).pCoreIn 2 := by
  obtain ⟨h0,h1,h2⟩ := c.central_critical_intersections (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hcentral
  obtain ⟨hs,hd⟩ := c.central_neighbor_centers (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht hne
  have hc := c.central_middle_center_card (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral E
  change Z F₀ α ⊓ Q F₀ u = Z F₀ β at h0
  change Z F₀ u ⊓ Q F₀ α = Z F₀ β at h1
  change Z F₀ α ⊓ Z F₀ u = Z F₀ β at h2
  change Z F₀ α = Z F₀ β ⊔ Z F₀ t at hs
  dsimp only
  refine ⟨?_,?_,?_,?_,Subgroup.disjoint_map (G₀ L S).subtype_injective hd,?_,?_⟩
  · simpa only [map_inf _ _ _ (G₀ L S).subtype_injective] using
      congrArg (map (G₀ L S).subtype) h0
  · have hh := congrArg (map (G₀ L S).subtype) h1
    simpa only [map_inf _ _ _ (G₀ L S).subtype_injective,
      reduced_base_Q_map h false,Bool.false_eq_true,↓reduceIte] using hh
  · simpa only [map_inf _ _ _ (G₀ L S).subtype_injective] using
      congrArg (map (G₀ L S).subtype) h2
  · simpa only [Subgroup.map_sup] using congrArg (map (G₀ L S).subtype) hs
  · exact (card_map_of_injective (G₀ L S).subtype_injective).trans hc
  · have hh := map_mono (f := (G₀ L S).subtype)
      (show Z F₀ β ≤ Q F₀ β from fun _ hz =>
        ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U (reduced_triple h) β).1 hz)).1)
    simpa only [reduced_base_Q_map h true,↓reduceIte] using hh

/-- The first separation and displacement steps of (10.8), on the
literal original residual/core intersection. The normalizing part of the
terminal O²-actor centralizes this intersection. Triviality of the whole
intersection is still required for the full source theorem. -/
theorem original_bTwo_residual_separation_control
    {k' W' : Type*} [Field k'] [Finite k'] [CharP k' 2]
    [AddCommGroup W'] [Module (ZMod 2) W']
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t y : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (c' : BTwoCenterActionData F₀ u β α k' W')
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hy : (graph F₀).Adj u y) (hyne : y ≠ β) :
    ∃ g : c.actor, (g : G₀ L S) • β = t ∧
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
      let W₀ := (Z F₀ u).map (G₀ L S).subtype ⊔
        (Z F₀ ((g : G₀ L S) • u)).map (G₀ L S).subtype
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      let J₀ := R₀ ⊓ (Q F₀ y).map (G₀ L S).subtype
      let A₀ := ((pResidual 2 c'.actor).map c'.actor.subtype).map (G₀ L S).subtype
      let Z' := (Z F₀ u).map (G₀ L S).subtype
      J₀ ≤ (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ y).map (G₀ L S).subtype ∧
        Disjoint J₀ Z' ∧ ⁅J₀,A₀⁆ ≤ Z' ∧
        J₀ ≤ centralizer ((A₀ ⊓ normalizer (J₀ : Set G) : Subgroup G) : Set G) := by
  obtain ⟨g,hg,hJD,hJZ,hmove,_⟩ := c.residual_separation_control (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb c' hactor hcentral ht hne hy hyne
  let ι := (G₀ L S).subtype
  let R := bTwoResidual F₀ β t u ((g : G₀ L S) • u)
  let J := R ⊓ Q F₀ y
  let A := (pResidual 2 c'.actor).map c'.actor.subtype
  let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map ι
  let W₀ := (Z F₀ u).map ι ⊔ (Z F₀ ((g : G₀ L S) • u)).map ι
  let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
  let J₀ := R₀ ⊓ (Q F₀ y).map ι
  let A₀ := A.map ι
  let Z' := (Z F₀ u).map ι
  change J ≤ D F₀ β y at hJD
  change Disjoint J (Z F₀ u) at hJZ
  change ⁅J,A⁆ ≤ Z F₀ u at hmove
  have hDm : (D F₀ β t).map ι = D₀ := by
    change ((Q F₀ β ⊓ Q F₀ t).map ι) = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hRm : R.map ι = R₀ := by
    change ((D F₀ β t ⊓ centralizer
      ((Z F₀ u ⊔ Z F₀ ((g : G₀ L S) • u) : Subgroup (G₀ L S)) : Set (G₀ L S))).map ι) = _
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,
      hDm,Subgroup.map_sup]
  have hJm : J.map ι = J₀ := by
    change (R ⊓ Q F₀ y).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hRm]
  have hdis : Disjoint J₀ Z' := by
    rw [←hJm]
    exact Subgroup.disjoint_map (G₀ L S).subtype_injective hJZ
  have hcomm : ⁅J₀,A₀⁆ ≤ Z' := by
    have hh := map_mono (f := ι) hmove
    rwa [map_commutator,hJm] at hh
  refine ⟨g,hg,?_,hdis,hcomm,?_⟩
  · change J₀ ≤ _
    exact le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right
  · change J₀ ≤ centralizer ((A₀ ⊓ normalizer (J₀ : Set G) : Subgroup G) : Set G)
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply hdis.le_bot.trans'
    exact le_inf (le_normalizer_iff_commutator_le_left.mp inf_le_right)
      ((commutator_mono le_rfl inf_le_left).trans hcomm)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
