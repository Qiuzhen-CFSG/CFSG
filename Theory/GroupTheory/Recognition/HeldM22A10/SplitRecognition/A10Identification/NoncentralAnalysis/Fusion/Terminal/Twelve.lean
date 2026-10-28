module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.Conjugacy

/-!
# A twelve-element lambda orbit contains tau

The elementary group S has twelve elements outside <pi,mu>. Under pi--mu
fusion none of the three nonidentity elements of <pi,mu> is conjugate to
lambda. Consequently a twelve-element lambda orbit contained in S is exactly
that complement, and contains tau. The proof enumerates only sixteen binary
coordinates and transports them through the actual model embedding.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.229.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

private abbrev TwelveCode := {a : BaseCode // a.2.2 ≠ 0}
private def twelveWord (a : TwelveCode) : H := elementaryWord 1 a.1
private theorem twelveWord_injective : Function.Injective twelveWord := by
  decide +kernel
private theorem twelveCode_card : Nat.card TwelveCode = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem four_word : ∀ a : BaseCode, a.2.2 = 0 →
    elementaryWord 1 a = 1 ∨ elementaryWord 1 a = pi ∨
      elementaryWord 1 a = mu ∨ elementaryWord 1 a = pi * mu := by
  decide +kernel
private theorem mu_isConj_pi_mu : IsConj mu (pi * mu) := by
  apply isConj_iff.mpr
  exact ⟨taup, by decide +kernel⟩

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem terminal_tau_mem_of_twelve (K : Subgroup G)
    (hKN : K ≤ normalizer (ambientElementary D e 1 : Set G))
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hsize : Nat.card (terminalOrbit K (D.a10ModelEmbedding e lam)) = 12) :
    D.a10ModelEmbedding e tau ∈ terminalOrbit K (D.a10ModelEmbedding e lam) := by
  let f := D.a10ModelEmbedding e
  let T : Set G := Set.range (fun a : TwelveCode => f (twelveWord a))
  have hT : T.ncard = 12 := by
    exact (Set.ncard_range_of_injective ((D.a10ModelEmbedding_injective e).comp
      twelveWord_injective)).trans twelveCode_card
  have hlamS : f lam ∈ ambientElementary D e 1 :=
    mem_map_of_mem _ (elementaryGenerators_mem 1 3)
  have hsub : terminalOrbit K (f lam) ⊆ T := by
    rintro x ⟨g, hg⟩
    have hxS : x ∈ ambientElementary D e 1 := by
      rw [← hg]
      exact (mem_normalizer_iff.mp (hKN g.property) _).mp hlamS
    obtain ⟨w, hw, rfl⟩ := hxS
    obtain ⟨a, rfl⟩ := (mem_elementary 1 w).mp hw
    have hconj : IsConj (f lam) (f (elementaryWord 1 a)) := isConj_iff.mpr ⟨g, hg⟩
    have ha : a.2.2 ≠ 0 := by
      intro ha
      rcases four_word a ha with he | he | he | he
      · rw [he, map_one, isConj_one_left] at hconj
        have hne : lam ≠ 1 := by decide +kernel
        exact hne ((map_eq_one_iff f (D.a10ModelEmbedding_injective e)).mp hconj)
      · rw [he, D.a10ModelEmbedding_central e] at hconj
        exact hlam hconj.symm
      · rw [he] at hconj
        exact hlam (hmu.trans hconj.symm)
      · rw [he] at hconj
        exact hlam ((hmu.trans (f.map_isConj mu_isConj_pi_mu)).trans hconj.symm)
    exact ⟨⟨a, ha⟩, rfl⟩
  have heq : terminalOrbit K (f lam) = T :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hT]; exact hsize.ge)
  rw [heq]
  exact ⟨⟨(0, 0, 1, 0), by decide⟩, rfl⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
