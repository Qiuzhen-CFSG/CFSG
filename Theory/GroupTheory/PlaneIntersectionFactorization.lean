module
public import Theory.GroupTheory.PlaneCoreNormalClosure
public import Theory.GroupTheory.PResidual.NormalClosureCover
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-!
# Residual intersections in a plane action

Let a finite group act onto S₃, with normal two-perfect L having cubic image
and a two-group action kernel. Let Q be a two-subgroup normalized by the action
kernel. If Q ∩ I has nontrivial image and I escapes Q ker(f), then I has full
image. The I-conjugate span of Q ∩ I has full image as well; its two-residual
lies in L ∩ I and covers the cubic image. Thus O²(L ∩ I) covers L modulo its
kernel. Adjoining T ∩ I gives the analogous cover of LT whenever Q ≤ T is
a two-subgroup. Both kernels remain literal intersections with ker(f).

The Chapter 14 consumer identifies these with the original two-cores and
converts the joins to products. Source: Aschbacher–Smith, refs/quasithin.pdf,
Lemma 14.6.6(3), printed p.1023.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem two_subgroup_permThree_card (Q : Subgroup (Equiv.Perm (Fin 3)))
    (hp : IsPGroup 2 Q) (hne : Q ≠ ⊥) : Nat.card Q = 2 := by
  have hd : Nat.card Q ∣ 2 * 3 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using
      Q.card_subgroup_dvd_card
  have hc : Nat.Coprime (Nat.card Q) 3 := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  rcases (Nat.dvd_prime Nat.prime_two).mp (hc.dvd_mul_right.mp hd) with h | h
  · exact (hne (card_eq_one.mp h)).elim
  · exact h

private theorem permThree_overgroup_two_eq_top
    (A X : Subgroup (Equiv.Perm (Fin 3))) (hA : Nat.card A = 2)
    (hAX : A ≤ X) (hout : ¬ X ≤ A) : X = ⊤ := by
  have hd : Nat.card X ∣ 6 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using
      X.card_subgroup_dvd_card
  have hd2 : 2 ∣ Nat.card X := hA ▸ card_dvd_of_le hAX
  have he : Nat.card X ≠ 2 := by
    intro hc
    exact hout (eq_of_le_of_card_ge hAX (by omega)).ge
  have hp := Nat.card_pos (α := X)
  have hb : Nat.card X ≤ 6 := Nat.le_of_dvd (by decide) hd
  have hc : Nat.card X = 6 := by
    interval_cases hc : Nat.card X <;> norm_num at *
  apply X.eq_top_of_card_eq
  simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hc

/-- Both residual intersection covers in the original S₃ action. -/
theorem plane_intersection_factorization
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (L Q T I : Subgroup G) [L.Normal]
    (hL : IsPPerfect 2 L) (hQ : IsPGroup 2 Q)
    (hLc : Nat.card (L.map f) = 3)
    (hLk : IsPGroup 2 (L ⊓ f.ker : Subgroup G))
    (hkQ : f.ker ≤ normalizer (Q : Set G))
    (hQT : Q ≤ T) (hT : IsPGroup 2 T)
    (hQI : ¬ Q ⊓ I ≤ f.ker) (hout : ¬ I ≤ Q ⊔ f.ker) :
    let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
    L = R ⊔ (L ⊓ f.ker) ∧
      L ⊔ T = R ⊔ (T ⊓ I) ⊔ ((L ⊔ T) ⊓ f.ker) := by
  let A := Q ⊓ I
  have hAc : Nat.card (A.map f) = 2 := two_subgroup_permThree_card _
    ((hQ.to_le inf_le_left).map f) (fun hh => hQI ((Subgroup.map_eq_bot_iff _).mp hh))
  have hQc : Nat.card (Q.map f) = 2 := two_subgroup_permThree_card _ (hQ.map f)
    (fun hh => hQI (inf_le_left.trans ((Subgroup.map_eq_bot_iff _).mp hh)))
  have hAQ : A.map f = Q.map f := eq_of_le_of_card_ge (map_mono inf_le_left) (by omega)
  have hIc : I.map f = ⊤ := by
    apply permThree_overgroup_two_eq_top (Q.map f) _ hQc
    · rw [← hAQ]
      exact map_mono inf_le_right
    · intro hh
      apply hout
      simpa only [comap_map_eq] using (le_comap_map f I).trans (comap_mono hh)
  have hQP := join_inf_ker_isPGroup_of_disjoint_images f L Q le_normalizer_of_normal hLk hQ
    ((IsPGroup.of_card (p := 3) (n := 1) (by simpa using hLc)).disjoint_of_ne
      3 2 (by decide) _ _ (hQ.map f))
  have hspan := conjugateSpan_eq_join_of_permThree f hf L Q hL
    (permThree_join_image_eq_top f L Q hLc hQc) hQc hQP hkQ
  have hn : (L ⊔ Q).Normal := by
    rw [← hspan]
    exact normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy Q ⊤))
  let := hn
  let N := conjugateSpanBy A I
  have hNP : N ≤ L ⊔ Q := conjugateSpanBy_le (inf_le_left.trans le_sup_right)
    le_normalizer_of_normal
  have hNI : N ≤ I := conjugateSpanBy_le_self inf_le_right
  have hNf : N.map f = ⊤ := by
    change (conjugateSpanBy A I).map f = ⊤
    rw [map_conjugateSpanBy, hIc]
    exact permThree_conjugateSpan_eq_top _ hAc
  let D := (pResidual 2 N).map N.subtype
  have hDL : D ≤ L := embedded_pResidual_le_of_normal_sup_pGroup L Q N hQ hNP
  have hDI : D ≤ I := (map_subtype_le _).trans hNI
  have hDf : D.map f = alternatingGroup (Fin 3) := by
    rw [show D = (pResidual 2 N).map N.subtype from rfl, map_embedded_pResidual, hNf]
    rw [map_pResidual_of_surjective 2 _ (by intro x; exact ⟨⟨x,mem_top x⟩,rfl⟩)]
    exact Equiv.Perm.twoResidual_eq_alternating _
  have hLD : L.map f ≤ D.map f := by
    apply le_of_eq (eq_of_le_of_card_ge (map_mono hDL) ?_).symm
    rw [hDf, hLc, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  have hDR : D ≤ R := by
    have hh := embedded_pResidual_mono 2 (le_inf hDL hDI)
    have hp := (pResidual_eq_top_iff 2 D).mpr (isPPerfect_embedded_pResidual 2 N)
    simpa only [hp, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hRL : R ≤ L := (map_subtype_le _).trans inf_le_left
  have hLfR : L.map f ≤ R.map f := hLD.trans (map_mono hDR)
  have hcover : L = R ⊔ (L ⊓ f.ker) := by
    apply le_antisymm _ (sup_le hRL inf_le_left)
    intro l hl
    obtain ⟨r, hr, he⟩ := hLfR (mem_map_of_mem f hl)
    have hkr : r⁻¹ * l ∈ L ⊓ f.ker := ⟨L.mul_mem (L.inv_mem (hRL hr)) hl, by
      change f (r⁻¹ * l) = 1
      simp only [map_mul, map_inv, he, inv_mul_cancel]⟩
    simpa only [mul_inv_cancel_left] using (R ⊔ (L ⊓ f.ker)).mul_mem
      (mem_sup_left hr) (mem_sup_right hkr)
  refine ⟨hcover, ?_⟩
  have hRf : Nat.card (R.map f) = 3 := by
    rw [le_antisymm (map_mono hRL) hLfR, hLc]
  have hTIc : Nat.card ((T ⊓ I).map f) = 2 := two_subgroup_permThree_card _
    ((hT.to_le inf_le_left).map f) (fun hh => hQI (fun a ha =>
      (Subgroup.map_eq_bot_iff _).mp hh ⟨hQT ha.1, ha.2⟩))
  have hfull := permThree_join_image_eq_top f R (T ⊓ I) hRf hTIc
  have hsub : R ⊔ (T ⊓ I) ≤ L ⊔ T := sup_le (hRL.trans le_sup_left)
    (inf_le_left.trans le_sup_right)
  apply le_antisymm _ (sup_le hsub inf_le_left)
  intro x hx
  obtain ⟨r, hr, he⟩ := (show f x ∈ (R ⊔ (T ⊓ I)).map f by rw [hfull]; trivial)
  have hk : r⁻¹ * x ∈ (L ⊔ T) ⊓ f.ker := ⟨(L ⊔ T).mul_mem
    ((L ⊔ T).inv_mem (hsub hr)) hx, by
      change f (r⁻¹ * x) = 1
      simp only [map_mul, map_inv, he, inv_mul_cancel]⟩
  simpa only [mul_inv_cancel_left] using
    ((R ⊔ (T ⊓ I)) ⊔ ((L ⊔ T) ⊓ f.ker)).mul_mem (mem_sup_left hr) (mem_sup_right hk)

end Subgroup
