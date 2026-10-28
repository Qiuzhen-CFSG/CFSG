module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.FiveExclusion.Transport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.BinaryHigher.FlagRecognition
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions

/-!
# Excluding a single-node binary five-dimensional component intersection

An inner Sylow image is contained in every larger flag stabilizer over the
local intersection. Maximality excludes this case by retaining just one of
the three remaining cuts. An outside Sylow element gives an outer automorphism
of the actual component, since its centralizer in the quotient is trivial.
Such an automorphism can preserve a single-node parabolic only in dimension
four. Thus no single-node parabolic survives in dimension five.

Intrinsic flag recognition supplies the single-node placement from the solvable
prime-to-three residual and three-subgroup order bound. Transport proves these
inputs for the literal source intersection. The final theorem discharges the
recognition premise and excludes the binary degree-five source branch.

Source: Aschbacher--Smith, 15.3.43, the n = 1 paragraph on printed p.1140,
with 1.1.5(3)(a), p.501, and A.2.3--4, p.33. The invariant-overgroup argument
adapts the independent binary-node argument for 15.3.28.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions

variable {G : Type*} [Group G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

namespace FiveExclusion
variable {H : Type*} [Group H] (e : c.toComponentAction.image L ≃* H)

/-- Maximality applies to every proper invariant enlargement in model coordinates. -/
theorem invariant_overgroup_eq (P : Subgroup H) (hP : intersection c e ≤ P)
    (hproper : P ≠ ⊤)
    (hn : c.toComponentAction.image S ≤ normalizer
      (P.map (embedding c e) : Set c.toComponentAction.Quotient)) :
    P = intersection c e := by
  have hPL : P.map (embedding c e) ≤ c.toComponentAction.image L := by
    rw [← top_map_embedding c e]
    exact map_mono le_top
  have hne : P.map (embedding c e) ≠ c.toComponentAction.image L := by
    rw [← top_map_embedding c e]
    exact fun hh => hproper (map_injective (embedding_injective c e) hh)
  have hMP : c.toComponentAction.image M ⊓ c.toComponentAction.image L ≤
      P.map (embedding c e) := by
    rw [← quotient_intersection_eq c, ← intersection_map_embedding c e]
    exact map_mono hP
  have hle := invariant_overgroup_le c (P.map (embedding c e))
    (lt_of_le_of_ne hPL hne) hMP hn
  apply le_antisymm ?_ hP
  apply (map_le_map_iff_of_injective (embedding_injective c e)).mp
  rwa [intersection_map_embedding, quotient_intersection_eq c]

/-- A single-node intersection forces an actual outside Sylow element. -/
theorem outer_of_minimalParabolic {m : ℕ} (hm : 3 ≤ m)
    (f : c.toComponentAction.image L ≃* LinearGroup (m + 1)) (b : Basis m)
    (i : Fin m) (hi : intersection c f = minimalParabolic b i) :
    ¬ c.toComponentAction.image S ≤ c.toComponentAction.image L := by
  classical
  intro hs
  have hex : (Finset.univ.erase i : Finset (Fin m)).Nontrivial := by
    rw [← Finset.one_lt_card_iff_nontrivial, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj, k, hk, hjk⟩ := hex
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hki : k ≠ i := (Finset.mem_erase.mp hk).1
  let P := cutStabilizer b ({k} : Set (Fin m))
  have hle : intersection c f ≤ P := by
    rw [hi]
    exact (cutStabilizer_le_iff _ _ _).mpr (by simpa using hki.symm)
  have hproper : P ≠ ⊤ := by
    intro he
    have ht : cutStabilizer b (∅ : Set (Fin m)) = ⊤ := by simp [cutStabilizer]
    have hh := (cutStabilizer_le_iff b ∅ {k}).mp
      (show cutStabilizer b ∅ ≤ P by rw [ht, he])
    exact hh (Set.mem_singleton k)
  have hSP : c.toComponentAction.image S ≤ P.map (embedding c f) := by
    intro s hsS
    let sL : c.toComponentAction.image L := ⟨s, hs hsS⟩
    have hsf : f sL ∈ sylowIntersection c f := mem_map.mpr ⟨sL, hsS, rfl⟩
    refine mem_map.mpr ⟨f sL, hle (sylowIntersection_le_intersection c f hsf), ?_⟩
    exact congrArg Subtype.val (f.symm_apply_apply sL)
  have he := invariant_overgroup_eq c f P hle hproper
    (hSP.trans (P.map (embedding c f)).le_normalizer)
  have hh : ({i} : Set (Fin m))ᶜ ⊆ {k} :=
    (cutStabilizer_le_iff b {k} {i}ᶜ).mp (he.trans hi).le
  exact hjk (hh hji)

/-- Faithfulness on the actual quotient component detects outer Sylow action. -/
theorem exists_outer_preserving
    (hs : ¬ c.toComponentAction.image S ≤ c.toComponentAction.image L) :
    ∃ α : MulAut H, α ∉ MulAut.innerSubgroup H ∧
      (intersection c e).map α.toMonoidHom = intersection c e := by
  let : Group.IsPerfect L := SporadicModels.reduced_component_perfect c
  have hc := SporadicModels.component_image_centralizer_eq_bot c.toComponentAction
  obtain ⟨s, hsS, hsL⟩ := SetLike.not_le_iff_exists.mp hs
  refine ⟨componentAction (c.toComponentAction.image L) e s, ?_, ?_⟩
  · exact fun hh => hsL ((componentAction_mem_inner _ e hc s).mp hh)
  · apply componentAction_map_subgroup _ e _
      (map_mono (comap_mono inf_le_right)) s
    change s ∈ normalizer (c.toComponentAction.image (M ⊓ L) :
      Set c.toComponentAction.Quotient)
    rw [quotient_intersection_eq c]
    exact ParabolicInspection.quotient_sylow_normalizes_intersection c hsS

end FiveExclusion

/-- No actual single-node component intersection survives in binary degree five. -/
theorem not_linear_five_of_minimalParabolic
    (e : c.toComponentAction.image L ≃* LinearGroup 5)
    (b : Basis 4) (i : Fin 4)
    (hi : FiveExclusion.intersection c e = minimalParabolic b i) : False := by
  have hout := FiveExclusion.outer_of_minimalParabolic c (by decide : 3 ≤ 4) e b i hi
  obtain ⟨α, hα, hP⟩ := FiveExclusion.exists_outer_preserving c e hout
  rw [hi] at hP
  have hm := outer_preserves_minimalParabolic_middle (by decide : 2 ≤ 4)
    (by decide : 4 ≤ 4) b i α hα hP
  omega

variable [Finite G]

/-- The source exclusion conditional only on the intrinsic single-node recognition
calculation. All of its hypotheses are discharged on the actual quotient images. -/
theorem not_linear_five_of_recognition (hs : IsSimpleGroup L)
    (iso : ClassicalGroup.IsPSL L 5 2)
    (recognition : ∀ (U : Sylow 2 (LinearGroup 5)) (b : Basis 4),
      (U : Subgroup (LinearGroup 5)) = cutStabilizer b Set.univ →
      ∀ P : Subgroup (LinearGroup 5), (U : Subgroup (LinearGroup 5)) ≤ P → P ≠ ⊤ →
      Group.IsSolvable (primeToResidual 3 P) → 3 ∣ Nat.card P →
      (∀ X : Subgroup (LinearGroup 5), X ≤ P → IsPGroup 3 X → Nat.card X ≤ 3) →
      ∃ i : Fin 4, P = minimalParabolic b i) : False := by
  obtain ⟨e⟩ := exists_component_linearEquiv c hs (by decide : 0 < 5) iso
  obtain ⟨U, hU⟩ := FiveExclusion.exists_modelSylow c e
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer U
  obtain ⟨i, hi⟩ := recognition U b hb (FiveExclusion.intersection c e)
    (hU ▸ FiveExclusion.sylowIntersection_le_intersection c e)
    (FiveExclusion.intersection_ne_top c e)
    (FiveExclusion.intersection_residual_solvable c e hs)
    (FiveExclusion.intersection_three_dvd c e hs)
    (FiveExclusion.intersection_three_subgroup_bound c e hs)
  exact not_linear_five_of_minimalParabolic c e b i hi

/-- The binary degree-five branch of the source parabolic inspection is impossible.
The reduced configuration already supplies the residual and maximality used here. -/
theorem not_linear_five_of_parabolic {z : G} (_hz : SourceInvolution S M z)
    (hs : IsSimpleGroup L) (iso : ClassicalGroup.IsPSL L 5 2)
    (_hi : ActsInner L z) (_hp : ParabolicInspection.QuotientParabolic c) : False := by
  exact not_linear_five_of_recognition c hs iso
    CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.BinaryHigher.FlagRecognition.five

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
