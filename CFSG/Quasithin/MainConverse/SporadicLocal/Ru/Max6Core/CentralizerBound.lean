module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core.NormalSeed
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core.CentralizerData
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Level3

/-!
# A two-power bound for the intrinsic seed centralizer

A permutation centralizing the seed preserves five point colors. The color of
point zero has 128 possible points. If it fixes zero, it fixes every seed-word
image of zero; two short adjacency profiles then force it to fix one and two.
The existing certified max6 three-point rigidity proves it is the identity.
Thus the centralizer has at most 128 elements. It contains the abelian seed,
a two-group with at least 64 elements, so it too is a two-group.

Source: the degree-4060 Rudvalis model and GLS3 Table 5.3r, p.279, used for
Aschbacher--Smith Theorem 0.1.2(5). All point and word witnesses are checked
against the unchanged ATLAS carrier; no structure label is used as a premise.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuEven.Max6Core
open Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.OuterNormalizer Rudvalis.OuterNormalizer.InvarianceCertificate
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate
open CentralizerCertificate

@[expose] public def seedCentralizer : Subgroup max6 :=
  Subgroup.centralizer (normalSeed : Set max6)

@[expose] public def centralizerPerm : seedCentralizer →* Equiv.Perm (Fin 4060) :=
  modelSubgroup.subtype.comp (max6.subtype.comp seedCentralizer.subtype)

private theorem perm_injective : Function.Injective centralizerPerm :=
  Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)

private theorem preserves_relation (g : seedCentralizer) : centralizerPerm g ∈ relationAut :=
  model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.val.val.property

private theorem preserves_cachedAdj (g : seedCentralizer) (x y : Fin 4060) :
    cachedAdj (centralizerPerm g x) (centralizerPerm g y) ↔ cachedAdj x y :=
  (cachedAdj_iff_adj _ _).trans ((preserves_relation g x y).trans (cachedAdj_iff_adj _ _).symm)

private theorem point_commutes_word (g : seedCentralizer) (t : Fin 64) (x : Fin 4060) :
    centralizerPerm g (wordMap t x) = wordMap t (centralizerPerm g x) := by
  have h := Subgroup.mem_centralizer_iff.mp g.property
    (⟨seedWord t, seed_le_max6 (seedWord_mem t)⟩ : max6) (seedWord_mem t)
  have hp := congrArg (fun w : max6 => w.val.val x) h
  change (seedWord t).val (centralizerPerm g x) =
    centralizerPerm g ((seedWord t).val x) at hp
  simpa only [wordMap_eq] using hp.symm

private theorem feature_preserved (g : seedCentralizer) (t : Fin 64) (x : Fin 4060) :
    feature t (centralizerPerm g x) = feature t x := by
  have hf : wordMap t (centralizerPerm g x) = centralizerPerm g x ↔ wordMap t x = x := by
    rw [← point_commutes_word]
    exact (centralizerPerm g).injective.eq_iff
  have ha : cachedAdj (centralizerPerm g x) (wordMap t (centralizerPerm g x)) ↔
      cachedAdj x (wordMap t x) := by
    rw [← point_commutes_word]
    exact preserves_cachedAdj g _ _
  simp only [feature, hf, ha]

private theorem color_preserved (g : seedCentralizer) (x : Fin 4060) :
    color (centralizerPerm g x) = color x := by
  simp only [color_recipe, feature_preserved]

private theorem profile_preserved (g : seedCentralizer)
    (h0 : centralizerPerm g 0 = 0) (ts : List (Fin 64)) (x : Fin 4060) :
    profile ts (centralizerPerm g x) = profile ts x := by
  apply List.map_congr_left
  intro t _
  have ht : centralizerPerm g (wordMap t 0) = wordMap t 0 := by
    rw [point_commutes_word, h0]
  have h := preserves_cachedAdj g (wordMap t 0) x
  rw [ht] at h
  exact decide_eq_decide.mpr h

set_option maxRecDepth 30000 in
private theorem fixes_zero_eq_one (g : seedCentralizer) (h0 : centralizerPerm g 0 = 0) :
    g = 1 := by
  have h1 : centralizerPerm g 1 = 1 := separate1 _ (color_preserved g 1)
    (profile_preserved g h0 separatingWords1 1)
  have h2 : centralizerPerm g 2 = 2 := separate2 _ (color_preserved g 2)
    (profile_preserved g h0 separatingWords2 2)
  have hz (x : Fin 4060) :
      centralizerPerm g (AlignmentData.involutionPerm x) =
        AlignmentData.involutionPerm (centralizerPerm g x) := by
    have h := congrArg (fun w : Model => w.val x)
      (Subgroup.mem_centralizer_singleton_iff.mp (max6_le_centralizer g.val.property))
    change centralizerPerm g (centralInvolution.val x) =
      centralInvolution.val (centralizerPerm g x) at h
    simpa only [centralInvolution_val] using h
  have he : centralizerPerm g = 1 := by
    apply fix_three_eq_one _ (preserves_relation g) hz
    intro x hx
    have hh : x = 0 ∨ x = 1 ∨ x = 2 := by
      have hv : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
      rcases hv with hv | hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Or.inl (Fin.ext hv))
      · exact Or.inr (Or.inr (Fin.ext hv))
    rcases hh with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  apply perm_injective
  simpa only [map_one] using he

private theorem point_image_injective : Function.Injective (fun g : seedCentralizer =>
    centralizerPerm g 0) := by
  intro g h hh
  change centralizerPerm g 0 = centralizerPerm h 0 at hh
  have h0 : centralizerPerm (g⁻¹ * h) 0 = 0 := by
    rw [map_mul, map_inv]
    change (centralizerPerm g).symm (centralizerPerm h 0) = 0
    rw [← hh]
    exact (centralizerPerm g).symm_apply_apply 0
  have he := fixes_zero_eq_one (g⁻¹ * h) h0
  exact inv_mul_eq_one.mp he

public theorem seedCentralizer_card_le : Nat.card seedCentralizer ≤ 128 := by
  let f : seedCentralizer → Fin 128 := fun g => candidateInverse (centralizerPerm g 0)
  have hf : Function.Injective f := by
    intro g h he
    apply point_image_injective
    have hi := congrArg candidate he
    change candidate (candidateInverse (centralizerPerm g 0)) =
      candidate (candidateInverse (centralizerPerm h 0)) at hi
    rw [candidate_decode _ (color_preserved g 0), candidate_decode _ (color_preserved h 0)] at hi
    exact hi
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

public theorem normalSeed_le_seedCentralizer : normalSeed ≤ seedCentralizer := by
  intro g hg h hh
  have he := mul_comm' (⟨g.val, hg⟩ : seed) ⟨h.val, hh⟩
  exact Subtype.ext (congrArg (fun z : seed => (z : Model)) he.symm)

public theorem seedCentralizer_isPGroup : IsPGroup 2 seedCentralizer := by
  obtain ⟨n, hn⟩ := normalSeed_isPGroup.exists_card_eq
  have hn6 : 6 ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2 ^ 6 ≤ 2 ^ n by simpa only [← hn] using normalSeed_card_ge)
  have hd : 64 ∣ Nat.card seedCentralizer :=
    (show 64 ∣ Nat.card normalSeed by rw [hn]; exact pow_dvd_pow 2 hn6).trans
      (Subgroup.card_dvd_of_le normalSeed_le_seedCentralizer)
  obtain ⟨k, hk⟩ := hd
  have hp : 0 < Nat.card seedCentralizer := Nat.card_pos
  have hb := seedCentralizer_card_le
  have he : k = 1 ∨ k = 2 := by omega
  rcases he with rfl | rfl
  · exact IsPGroup.of_card (n := 6) hk
  · exact IsPGroup.of_card (n := 7) hk

end CFSG.Quasithin.MainConverse.SporadicLocal.RuEven.Max6Core
