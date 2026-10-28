module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts

/-!
# Conjugacy on the punctured distinguished coset

The nonidentity elements of `A = ⟨Z ∩ M⟩` are precisely `Z ∩ M`.
Consequently every nonidentity element of `C_A(v)` is a distinguished
involution in the local closure `Lᵥ`. Strong embedding inside this proper
local group conjugates any two of them by `M ∩ Lᵥ`. Such a conjugator
centralizes v, so it also conjugates the corresponding elements of
`C_A(v)v − {v}`. The proof retains the source inverse-conjugation convention
when passing to the public `MulAut.conj` equality.

Source: GLS4, Chapter 2, Lemma 12.4(d), using Lemma 12.2(b),
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Lemma 12.4(d), with a conjugator in the literal subgroup `M ∩ Lᵥ`.
This proves the `punctured_coset_conjugacy` clause of the local contract. -/
public theorem proper_pair_involution_punctured_coset_conjugacy
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    {a b : G} (haA : a ∈ closure (Z ∩ (M : Set G)))
    (hav : Commute a v) (ha1 : a ≠ 1)
    (hbA : b ∈ closure (Z ∩ (M : Set G))) (hbv : Commute b v) (hb1 : b ≠ 1) :
    ∃ g ∈ M ⊓ centralizerClosure Z v, MulAut.conj g (a * v) = b * v := by
  obtain ⟨n, hn, hmodels, hAL, hDN, hlocal, hcore, hnormal, hA, hcard, hZ, hrest⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  have haZM : a ∈ Z ∩ (M : Set G) := by rw [hZ]; exact ⟨haA, ha1⟩
  have hbZM : b ∈ Z ∩ (M : Set G) := by rw [hZ]; exact ⟨hbA, hb1⟩
  let F := centralizerClosure Z v
  have haF : a ∈ F := mem_centralizerClosure haZM.1 hav
  have hbF : b ∈ F := mem_centralizerClosure hbZM.1 hbv
  have hs := (pair_involution_centralizerClosure_local h.disconnected r htM hvD hv).2.2
  obtain ⟨g, hgM, hg⟩ := hs.involutions_conjugate_in
    (a := ⟨a, haF⟩) haZM.2 (IsInvolution.subtype (h.disconnected.involutions a haZM.1) haF)
    (b := ⟨b, hbF⟩) hbZM.2 (IsInvolution.subtype (h.disconnected.involutions b hbZM.1) hbF)
  have hga : MulAut.conj ((g : G)⁻¹) a = b := by
    simpa only [rightConjugateElem, MulAut.conj_apply, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val hg
  have hgv : Commute ((g : G)⁻¹) v := mem_centralizer_singleton_iff.mp
    (centralizerClosure_le Z v (F.inv_mem g.property))
  have hfix : MulAut.conj ((g : G)⁻¹) v = v := by
    simp only [MulAut.conj_apply]
    rw [hgv.eq, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨(g : G)⁻¹, ⟨M.inv_mem hgM, F.inv_mem g.property⟩, ?_⟩
  rw [map_mul, hga, hfix]

end BenderSuzuki.ZD
