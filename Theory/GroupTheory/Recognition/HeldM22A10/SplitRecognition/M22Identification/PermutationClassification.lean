module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.JankoModel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.RejectedCandidates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Normalization
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Enumeration

/-!
# Classification of Janko's degree-22 permutation image

A faithful action with the order/fixed-point profiles and normalizer generators
in `PermutationData`, ambient order 443520, and Sylow-three normalizers of
order 72 has image conjugate to the concrete subgroup `JankoModel.model`.

The proved coordinate normalization produces the eleven- and five-generators
and adjusts the order-four generator. The kernel-certified enumeration leaves
four candidates. The first and third contain an order-nine subgroup whose
relative normalizer has at least 144 elements, contradicting the supplied
Sylow-normalizer order after embedding. The second generates `model`; the
fourth does so after the corrected relabeling in `JankoModel`. Its proved
order 443520 turns subgroup containment into equality in both surviving cases.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1–19, Section 9, pp.17–18,
DOI 10.1016/0021-8693(68)90002-1. The action, ambient order, and Sylow-normalizer
orders are explicit inputs here; their construction from involution-centralizer
hypotheses belongs to the surrounding recognition argument.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification

open Subgroup JankoModel

universe u

variable {G : Type u} [Group G]

private theorem fixed_card_eq_sub_support (g : Equiv.Perm (Fin 22)) :
    (Finset.univ.filter (fun x => g x = x)).card = 22 - g.support.card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => g x = x)
  change (Finset.univ.filter (fun x => g x = x)).card + g.support.card =
    (Finset.univ : Finset (Fin 22)).card at h
  simpa using Nat.eq_sub_of_add_eq h

/-- Relabeling preserves the exact order/fixed-point profile. -/
private theorem hasAllowedProfile_conj (p g : Equiv.Perm (Fin 22))
    (h : HasAllowedProfile g) : HasAllowedProfile ((MulAut.conj p) g) := by
  unfold HasAllowedProfile at h ⊢
  rw [MulEquiv.orderOf_eq, fixed_card_eq_sub_support, MulAut.conj_apply,
    Equiv.Perm.card_support_conj, ← fixed_card_eq_sub_support]
  exact h

/-- Every element of a relabeled faithful image inherits its source profile. -/
private theorem range_map_hasAllowedProfile (R : PermutationData G)
    (p : Equiv.Perm (Fin 22)) (g : Equiv.Perm (Fin 22))
    (hg : g ∈ R.rho.range.map (MulAut.conj p).toMonoidHom) : HasAllowedProfile g := by
  obtain ⟨x, ⟨a, rfl⟩, rfl⟩ := hg
  apply hasAllowedProfile_conj
  unfold HasAllowedProfile
  rw [orderOf_injective R.rho R.faithful]
  exact R.order_fixed a

private theorem map_conj_map_conj (H : Subgroup (Equiv.Perm (Fin 22)))
    (p q : Equiv.Perm (Fin 22)) :
    (H.map (MulAut.conj p).toMonoidHom).map (MulAut.conj q).toMonoidHom =
      H.map (MulAut.conj (q * p)).toMonoidHom := by
  rw [map_map]
  congr 1

private theorem not_le_of_no_embedding {K H : Subgroup (Equiv.Perm (Fin 22))}
    (e : G ≃* H) (h : ∀ f : K →* G, ¬ Function.Injective f) : ¬ K ≤ H := by
  intro hle
  apply h (e.symm.toMonoidHom.comp (inclusion hle))
  intro x y hxy
  exact inclusion_injective hle (e.symm.injective hxy)

private theorem card_map_conj (H : Subgroup (Equiv.Perm (Fin 22)))
    (p : Equiv.Perm (Fin 22)) : Nat.card (H.map (MulAut.conj p).toMonoidHom) =
      Nat.card H :=
  Nat.card_congr ((MulAut.conj p).subgroupMap H).symm.toEquiv

variable [Finite G]

/-- Once one of the four printed candidates occurs in normalized coordinates,
the two rejected candidates contradict the three-normalizer bound; the other
two contain a conjugate of the known concrete group of the full ambient order.
This theorem does not assert the coordinate normalization or enumeration. -/
private theorem range_conjugacy_of_four_candidates
    (R : PermutationData G) (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (p : Equiv.Perm (Fin 22))
    (D : NormalizedGenerators (R.rho.range.map (MulAut.conj p).toMonoidHom))
    (hcandidates : D.n = n1 ∨ D.n = n2 ∨ D.n = n3 ∨ D.n = n4) :
    ∃ q : Equiv.Perm (Fin 22),
      R.rho.range.map (MulAut.conj q).toMonoidHom = model := by
  let H := R.rho.range.map (MulAut.conj p).toMonoidHom
  let e : G ≃* H := (MonoidHom.ofInjective R.faithful).trans
    ((MulAut.conj p).subgroupMap R.rho.range)
  have hH : Nat.card H = 443520 := (Nat.card_congr e.symm.toEquiv).trans hcard
  have hgen : closure ({ell, m, D.n} : Set (Equiv.Perm (Fin 22))) ≤ H := by
    rw [closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact D.ell_mem
    · exact D.m_mem
    · exact D.n_mem
  rcases hcandidates with hn | hn | hn | hn
  · rw [hn] at hgen
    exact False.elim (not_le_of_no_embedding e (firstModel_not_embed hcard hN3) hgen)
  · rw [hn] at hgen
    have heq : model = H := eq_of_le_of_card_ge hgen (by rw [model_card, hH])
    exact ⟨p, heq.symm⟩
  · rw [hn] at hgen
    exact False.elim (not_le_of_no_embedding e (thirdModel_not_embed hcard hN3) hgen)
  · rw [hn] at hgen
    have hle : model ≤ H.map (MulAut.conj fourthRelabeling).toMonoidHom := by
      rw [← map_fourth_model_eq_model]
      exact map_mono hgen
    have heq : model = H.map (MulAut.conj fourthRelabeling).toMonoidHom :=
      eq_of_le_of_card_ge hle (by
        rw [card_map_conj, model_card, hH])
    refine ⟨fourthRelabeling * p, ?_⟩
    rw [← map_conj_map_conj]
    exact heq.symm

/-- The faithful degree-22 action is conjugate to Janko's concrete M22 model.
The normalization and four-candidate enumeration are proved from the action
data; the rejected candidates contradict the supplied Sylow-normalizer order. -/
public theorem range_conjugacy [IsSimpleGroup G]
    (R : PermutationData G) (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72) :
    ∃ p : Equiv.Perm (Fin 22),
      R.rho.range.map (MulAut.conj p).toMonoidHom = model := by
  obtain ⟨p, ⟨D⟩⟩ := exists_normalizedGenerators R
  apply range_conjugacy_of_four_candidates R hcard hN3 p D
  apply eq_one_of_four D.n D.n_order D.n_fixed D.square_fixed
    D.conjugates_m D.square_normalized
  intro i
  apply range_map_hasAllowedProfile R p
  exact (R.rho.range.map (MulAut.conj p).toMonoidHom).mul_mem
    ((R.rho.range.map (MulAut.conj p).toMonoidHom).pow_mem D.ell_mem i.val) D.n_mem

end Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
