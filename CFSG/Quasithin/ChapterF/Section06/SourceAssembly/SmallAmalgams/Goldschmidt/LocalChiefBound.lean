module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalResidual
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalAlternatingCore
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients

/-!
# The local chief-factor bound in Goldschmidt's argument

The local pushing-up hypotheses make the actual two-residual cubic or A₄.
In the cubic case it centralizes the two-core by coprimeness. In the A₄ case
the two-core is its central four-group times the residual centralizer.
Every cubic subgroup lies in the two-residual, so its centralizer in the
two-core has index at most four. The symmetric-three chief-count formula
then gives at most one noncentral binary chief factor.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.14),
printed pp.384--385, as used in (5.3), printed p.394.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_le_twoResidual (X : Subgroup G) (hX : Nat.card X = 3) :
    X ≤ pResidual 2 G := by
  intro x hx
  let q := QuotientGroup.mk' (pResidual 2 G)
  have hpow : x ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x, hx⟩ : X))
    rw [hX] at hh
    exact congrArg Subtype.val hh
  have hqpow : (q x) ^ 3 = 1 := by rw [← map_pow, hpow, map_one]
  have hcop := (isPGroup_quotient_pResidual (G := G) 2).orderOf_coprime
    (n := 3) (by decide) (q x)
  have horder : orderOf (q x) = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (dvd_refl _) (orderOf_dvd_of_pow_eq_one hqpow)
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp horder)

private theorem cubic_residual_centralizes_core
    (hR : Nat.card (pResidual 2 G) = 3) :
    pCore 2 G ≤ centralizer ((pResidual 2 G : Subgroup G) : Set G) := by
  have hcop : Nat.Coprime (Nat.card (pCore 2 G)) (Nat.card (pResidual 2 G)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn, hR]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hcop))

/-- Every actual cubic subgroup has fixed index at most four on the two-core,
under the original local S₃ and Sylow characteristic-subgroup hypotheses. -/
theorem local_cubic_centralizer_relIndex_le_four
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal)
    (X : Subgroup G) (hX : Nat.card X = 3) :
    (centralizer (X : Set G)).relIndex (pCore 2 G) ≤ 4 := by
  have hXR := cubic_le_twoResidual X hX
  rcases local_residual_cubic_or_alternatingFour e P hP with hR | hR
  · obtain ⟨eR⟩ := hR
    have hR : Nat.card (pResidual 2 G) = 3 := by
      rw [Nat.card_congr eR.toEquiv]
      simp
    have hC : pCore 2 G ≤ centralizer (X : Set G) :=
      (cubic_residual_centralizes_core hR).trans (centralizer_le hXR)
    rw [(relIndex_eq_one.mpr hC)]
    decide
  · obtain ⟨eR⟩ := hR
    obtain ⟨hsplit, _, _, hV, _, hBnormal, _, _⟩ := alternating_residual_core_split eR
    let B := pCore 2 G ⊓ centralizer ((pResidual 2 G : Subgroup G) : Set G)
    let _ : B.Normal := hBnormal
    have hB : B ≤ centralizer (X : Set G) :=
      inf_le_right.trans (centralizer_le hXR)
    have hi : B.relIndex (pCore 2 G) ≤ 4 := by
      rw [hsplit, relIndex_sup_right]
      rw [← hV]
      exact Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card _ _)
    exact (relIndex_le_of_le_left (L := pCore 2 G) hB
      (FiniteIndex.index_ne_zero (H := B.subgroupOf (pCore 2 G)))).trans hi

/-- Every complete chief series has at most one noncentral binary factor;
the cubic actor is constructed from the original S₃ quotient. -/
theorem local_noncentralTwoCount_le_one
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal)
    (s : ChiefSeries G) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  have hd : 3 ∣ Nat.card G := by
    rw [SymmetricThreeTwoCore.card_eq e]
    exact dvd_mul_of_dvd_left (by decide) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 hd
  let X := zpowers x
  have hX : Nat.card X = 3 := by rw [Nat.card_zpowers, hx]
  let f : G →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup
  rw [NoncentralChiefRefinement.CubicComparison.symmetricThree_count f hf hp X hX s h0 h1,
    hk, conjugationCubicLength]
  have hi := Nat.log_mono_right (b := 4)
    (local_cubic_centralizer_relIndex_le_four e P hP X hX)
  exact hi.trans_eq (by decide : Nat.log 4 4 = 1)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
