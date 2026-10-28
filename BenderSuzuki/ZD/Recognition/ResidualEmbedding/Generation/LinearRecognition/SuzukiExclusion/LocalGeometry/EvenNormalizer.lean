module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Setup
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.Conjugation

/-!
# Normalizer control for even subgroups of the centralizer

Let Y ≤ J have even order, and choose an involution u in Y. Every element
normalizing Y carries u to another involution in J ≤ D. Both distinguished
centralizer closures are L by the source inputs, and conjugation transports
one closure to the other. Therefore the element normalizes L.

This proves the even-order branch of GLS4, Chapter 2, Lemma 14.2(d).
The remaining odd-order branch needs the local recognition argument in the
source; it is not inferred from Cauchy's theorem.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

public theorem Context.normalizer_control_even (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hY : Even (Nat.card Y)) :
    normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G) := by
  obtain ⟨n, hn, hmodels, hAL, hDN, h1, h2, hAN, hAE, hAC, hZ, hprod, hN, hJD, hrest⟩ :=
    proper_residualGenerated_structure d.minimal d.reduction d.action
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 hY.two_dvd
  have hui : PFAppendixIII.IsInvolution (u : G) := IsInvolution.map_of_injective
    (orderOf_eq_prime_iff.mp hu).symm Y.subtype Subtype.val_injective
  intro g hg
  have hguY : MulAut.conj g (u : G) ∈ Y := (mem_normalizer_iff.mp hg _).mp u.property
  have hgui := BenderSuzuki.IsInvolution.map_of_injective hui
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have huL := d.centralizers (u : G) (hJD (hYJ u.property)) hui
  have hguL := d.centralizers (MulAut.conj g (u : G)) (hJD (hYJ hguY)) hgui
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro x ⟨y, hy, rfl⟩
    rw [← hguL]
    exact centralizerClosure_conj_mem d.minimal.disconnected g (u : G) (huL.symm ▸ hy)
  · rw [card_map_of_injective (MulAut.conj g).injective]

end BenderSuzuki.ZD.SuzukiExclusion
