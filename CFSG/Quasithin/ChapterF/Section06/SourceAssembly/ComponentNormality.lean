module

public import CFSG.Quasithin.ChapterF.Section06.Elementary
public import Theory.GroupTheory.GeneralizedFitting.LayerRankOrbit
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.PResidual.Quotient
public import Mathlib.GroupTheory.IndexNormal
/-!
# Normality of components with at most two conjugates in a Goldschmidt triple

Suppose a component is moved by the common Sylow subgroup. The ambient
two-residual normalizes it. Each local residual normalizes the component's
Sylow intersection: either F.6.7 identifies that intersection with the
local one, or the residual lies in two distinct components and centralizes
them. The Sylow conjugate span of this intersection is then normalized by
both generators. Triviality of the ambient two-core kills that span,
forcing the nontrivial perfect component to have odd order, a contradiction.

Source: Aschbacher–Smith, F.6.10, printed p.306. This formulation also handles
a local residual contained in the shared center of conjugate components.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

omit [Finite G] in
private theorem normalizes_span (A S T : Subgroup G)
    (hAS : A ≤ normalizer (S : Set G)) (hTA : T ≤ normalizer (A : Set G)) :
    A ≤ normalizer (conjugateSpanBy S T : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨t, ht, s, hs, rfl⟩
  have hta : t⁻¹ * a * t ∈ A := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp (hTA (T.inv_mem ht)) a).mp ha
  have hs' := (mem_normalizer_iff.mp (hAS hta) s).mp hs
  exact subset_closure ⟨t, ht, (t⁻¹ * a * t) * s * (t⁻¹ * a * t)⁻¹, hs', by group⟩

omit [Finite G] in
private theorem residual_normalizes_of_index_two (K : Subgroup G)
    (hi : (normalizer (K : Set G)).index = 2) :
    pResidual 2 G ≤ normalizer (K : Set G) := by
  let N := normalizer (K : Set G)
  let : N.Normal := normal_of_index_eq_two hi
  exact sInf_le ⟨inferInstance, IsPGroup.of_card (p := 2) (n := 1) hi⟩

private theorem local_normalizes_component_intersection
    (h : IsGoldschmidtTriple G₁ G₂) {K : Subgroup G} (hK : IsComponent G K)
    (hN : pResidual 2 G ≤ normalizer (K : Set G))
    (t : G) (ht : t ∈ G₁ ⊓ G₂)
    (hm : K.map (MulAut.conj t).toMonoidHom ≠ K) :
    (pResidual 2 G₁).map G₁.subtype ≤ normalizer (((G₁ ⊓ G₂) ⊓ K : Subgroup G) : Set G) := by
  let A := (pResidual 2 G₁).map G₁.subtype
  have hAN : A ≤ normalizer (K : Set G) := (map_pResidual_le 2 G₁.subtype).trans hN
  by_cases hAK : A ≤ K
  · have hAt : A.map (MulAut.conj t).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp (h.intersection_normalizes_left_residual ht)
    have hAC : A ≤ K.map (MulAut.conj t).toMonoidHom := by
      rw [← hAt]
      exact map_mono hAK
    have hCA : A ≤ centralizer (K : Set G) :=
      hAC.trans (commutator_eq_bot_iff_le_centralizer.mp
        ((hK.map_conj t).commutator_eq_bot_of_ne hK hm))
    exact (hCA.trans (centralizer_le inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  · have hi := h.left_intersection_eq_core_intersection K
      ((h.left_subnormal_core_iff_not_residual_le K hK.1).mpr hAK)
    rw [← hi.2, ← hi.1]
    exact (le_inf ((map_subtype_le _).trans G₁.le_normalizer) hAN).trans
      inf_normalizer_le_normalizer_inf

/-- The general triple forbids a component with a two-point conjugacy orbit. -/
theorem component_normal_of_orbit_two (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) {K : Subgroup G} (hK : IsComponent G K)
    (horbit : K.Normal ∨ (normalizer (K : Set G)).index = 2) : K.Normal := by
  rcases horbit with hn | hi
  · exact hn
  by_contra hn
  obtain ⟨T, hT⟩ := h.intersection_sylow
  have hTN : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
    intro hle
    apply T.not_dvd_index
    simpa only [hi] using index_dvd_of_le hle
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hTN
  have htt : t ∈ G₁ ⊓ G₂ := by change t ∈ (T : Subgroup G) at ht; rwa [hT]
  have hm : K.map (MulAut.conj t).toMonoidHom ≠ K :=
    fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he)
  have hNR := residual_normalizes_of_index_two K hi
  let S := (G₁ ⊓ G₂) ⊓ K
  let R := conjugateSpanBy S (G₁ ⊓ G₂)
  have h₁ : (pResidual 2 G₁).map G₁.subtype ≤ normalizer (R : Set G) :=
    normalizes_span _ _ _ (local_normalizes_component_intersection h hK hNR t htt hm)
      h.intersection_normalizes_left_residual
  have h₂ : (pResidual 2 G₂).map G₂.subtype ≤ normalizer (R : Set G) := by
    apply normalizes_span _ _ _
      ?_ h.intersection_normalizes_right_residual
    simpa only [inf_comm G₂ G₁] using
      local_normalizes_component_intersection h.symm hK hNR t
        (show t ∈ G₂ ⊓ G₁ by simpa only [inf_comm G₂ G₁] using htt) hm
  have hTR : G₁ ⊓ G₂ ≤ normalizer (R : Set G) := le_normalizer_conjugateSpanBy _ _
  have hRN : R.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← h.generated]
    apply sup_le
    · rw [← h.left_residual_sup_intersection]
      exact sup_le h₁ hTR
    · rw [← h.right_residual_sup_intersection]
      exact sup_le h₂ hTR
  let : R.Normal := hRN
  have hRT : R ≤ (T : Subgroup G) := hT ▸ conjugateSpanBy_le_self (show S ≤ G₁ ⊓ G₂ from inf_le_left)
  have hRbot : R = ⊥ := le_bot_iff.mp
    ((show R ≤ pCore 2 G from le_sSup ⟨hRN, T.isPGroup'.to_le hRT⟩).trans hcore.le)
  have hSbot : S = ⊥ := le_bot_iff.mp ((le_conjugateSpanBy _ _).trans hRbot.le)
  obtain ⟨P, hP⟩ := h.subnormal_intersection_sylow K hK.1
  have hPbot : (P : Subgroup K) = ⊥ := by
    apply map_injective K.subtype_injective
    rw [hP, subgroupOf_map_subtype]
    simpa only [Subgroup.map_bot] using hSbot
  have hodd : Odd (Nat.card K) := by
    have hind := P.not_dvd_index
    rw [hPbot, index_bot] at hind
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hind)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K hodd)
end CFSG.Quasithin.ChapterF.SourceAssembly
