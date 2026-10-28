module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Overlap
public import Theory.GroupTheory.Amalgam.AutomorphismTransport

/-!
# Faithful original-overlap action on the reduced amalgam

Conjugation by the whole original Borel preserves the reduced overlap
and both reduced endpoints. Its kernel centralizes both reduced endpoints
and is normalized by the original Borel. The supplement formula therefore
makes this kernel normal in both original endpoints, so F.1.1 faithfulness
makes it trivial. A marked reduced comparison transports this faithful
action, and hence automorphism bounds, to the concrete model.

This is the action step in DGS, Groups and Graphs (1985), Chapter 15,
printed pp.226–231. It constructs no model comparison and imposes no
unproved bound on the model automorphism group. Both odd Borel factors
and both inclusion squares are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Both reduced endpoint inclusions retain the full reduced Borel. -/
@[expose] def reducedAmalgam (L : Fin 2 → Subgroup G) (S : Subgroup G) :=
  RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) 0)
    (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) 1)
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)

@[expose] def reducedEndpointAction (h : HypothesisF11 L S) (i : Fin 2) :
    commonBorel L S →* MulAut (parabolic L (reducedSylow L S) i) :=
  (parabolic L (reducedSylow L S) i).normalizerMonoidHom.comp
    (inclusion ((commonBorel_le_parabolic i).trans (parabolic_normalizes_reduced h i)))

/-- Keep the group-law check at an abstract subgroup boundary. -/
private def overlapAction (P₀ B₀ P₁ B : Subgroup G)
    (h₀ : B₀ ≤ P₀) (h₁ : B₀ ≤ P₁)
    (n₀ : B ≤ normalizer (P₀ : Set G))
    (nB : B ≤ normalizer (B₀ : Set G))
    (n₁ : B ≤ normalizer (P₁ : Set G)) :
    B →* RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₀ B₀ P₁ h₀ h₁)
      (RankTwoAmalgam.ofSubgroups P₀ B₀ P₁ h₀ h₁) where
  toFun b := {
    left := P₀.normalizerMonoidHom (inclusion n₀ b)
    middle := B₀.normalizerMonoidHom (inclusion nB b)
    right := P₁.normalizerMonoidHom (inclusion n₁ b)
    left_commutes := fun _ => Subtype.ext rfl
    right_commutes := fun _ => Subtype.ext rfl }
  map_one' := by
    apply RankTwoAmalgam.Iso.ext <;> apply MulEquiv.ext <;> intro x <;> apply Subtype.ext
    all_goals change (1 : G) * (x : G) * 1⁻¹ = (x : G); simp only [one_mul, inv_one, mul_one]
  map_mul' b c := by
    apply RankTwoAmalgam.Iso.ext <;> apply MulEquiv.ext <;> intro x <;> apply Subtype.ext
    all_goals
      change ((b : G) * (c : G)) * (x : G) * ((b : G) * (c : G))⁻¹ =
        (b : G) * ((c : G) * (x : G) * (c : G)⁻¹) * (b : G)⁻¹
      simp only [mul_inv_rev, mul_assoc]

/-- Conjugation by the original Borel gives compatible automorphisms of the reduced amalgam. -/
def reducedOverlapAction (h : HypothesisF11 L S) :
    commonBorel L S →* RankTwoAmalgam.Iso (reducedAmalgam L S) (reducedAmalgam L S) :=
  overlapAction _ _ _ _ (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    ((commonBorel_le_parabolic 0).trans (parabolic_normalizes_reduced h 0))
    (borel_normalizes_reduced h)
    ((commonBorel_le_parabolic 1).trans (parabolic_normalizes_reduced h 1))

theorem reducedOverlapAction_left (h : HypothesisF11 L S) (b : commonBorel L S) :
    (reducedOverlapAction h b).left = reducedEndpointAction h 0 b := by rfl

theorem reducedOverlapAction_right (h : HypothesisF11 L S) (b : commonBorel L S) :
    (reducedOverlapAction h b).right = reducedEndpointAction h 1 b := by rfl

/-- The original full Borel is detected by its two simultaneous reduced endpoint actions. -/
theorem reducedOverlapAction_injective (h : HypothesisF11 L S) :
    Function.Injective (reducedOverlapAction h) := by
  let f := reducedOverlapAction h
  let K := f.ker.map (commonBorel L S).subtype
  have hKB : K ≤ commonBorel L S := map_subtype_le _
  have hBK : commonBorel L S ≤ normalizer (K : Set G) := by
    have hh := f.ker.le_normalizer_map (commonBorel L S).subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hcentral (i : Fin 2) : K ≤ centralizer (parabolic L (reducedSylow L S) i : Set G) := by
    rintro k ⟨b, hb, rfl⟩
    apply mem_centralizer_iff.mpr
    intro x hx
    have hfix : reducedEndpointAction h i b ⟨x, hx⟩ = ⟨x, hx⟩ := by
      fin_cases i
      · have hh := congrArg (fun a : RankTwoAmalgam.Iso (reducedAmalgam L S)
          (reducedAmalgam L S) => a.left ⟨x, hx⟩) hb
        change (reducedOverlapAction h b).left ⟨x, hx⟩ = ⟨x, hx⟩ at hh
        rwa [reducedOverlapAction_left] at hh
      · have hh := congrArg (fun a : RankTwoAmalgam.Iso (reducedAmalgam L S)
          (reducedAmalgam L S) => a.right ⟨x, hx⟩) hb
        change (reducedOverlapAction h b).right ⟨x, hx⟩ = ⟨x, hx⟩ at hh
        rwa [reducedOverlapAction_right] at hh
    have he := congrArg Subtype.val hfix
    change (b : G) * x * (b : G)⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hK : K = ⊥ := h.common_normal_eq_bot K hKB (fun i => by
    rw [← reduced_parabolic_supplement h i]
    exact sup_le ((le_centralizer_iff.mp (hcentral i)).trans (Subgroup.centralizer_le_normalizer _)) hBK)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  exact (map_eq_bot_iff_of_injective f.ker (commonBorel L S).subtype_injective).mp hK

variable {A D C : Type*} [Group A] [Group D] [Group C]
  {α : RankTwoAmalgam A D C}

/-- Transport the actual original Borel action through both marked inclusion squares. -/
@[expose] def markedOverlapAction (h : HypothesisF11 L S)
    (e : RankTwoAmalgam.Iso (reducedAmalgam L S) α) :
    commonBorel L S →* RankTwoAmalgam.Iso α α :=
  (RankTwoAmalgam.automorphismConjEquiv e).toMonoidHom.comp (reducedOverlapAction h)

theorem markedOverlapAction_injective (h : HypothesisF11 L S)
    (e : RankTwoAmalgam.Iso (reducedAmalgam L S) α) :
    Function.Injective (markedOverlapAction h e) :=
  (RankTwoAmalgam.automorphismConjEquiv e).injective.comp (reducedOverlapAction_injective h)

/-- A bound on compatible model automorphisms controls the full original Borel. -/
theorem original_borel_card_le_model_automorphisms (h : HypothesisF11 L S)
    (e : RankTwoAmalgam.Iso (reducedAmalgam L S) α)
    [Finite (RankTwoAmalgam.Iso α α)] :
    Nat.card (commonBorel L S) ≤ Nat.card (RankTwoAmalgam.Iso α α) :=
  Nat.card_le_card_of_injective _ (markedOverlapAction_injective h e)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
