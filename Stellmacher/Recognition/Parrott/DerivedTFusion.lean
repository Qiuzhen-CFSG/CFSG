module

public import Stellmacher.Recognition.Parrott.LocalFusionObstruction
public import Stellmacher.Recognition.Parrott.ElementaryJoin
public import Stellmacher.Recognition.Parrott.DerivedTOmegaBounds

/-!
# The omega obstruction for Parrott's first derived representative

Let E be the ambient derived core, F the supplied second elementary subgroup,
and A=E∨F. An omega subgroup between E∩F and A is one of E∩F, E, F, A:
its involution generators lie in E or F, and E∩F has index two in each.
The identities A′=⟨z⟩ and C_G(E∩F)=A therefore turn these bounds into a
fusion obstruction when N_G(F)=T.
The local derived computation supplies these bounds, completing the exclusion
for the first representative without an assumed omega geometry.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the last two paragraphs of p.676.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem interval_of_index_two (L M U : Subgroup G)
    (hLM : L ≤ M) (hMU : M ≤ U) (hL : Nat.card L = 16) (hU : Nat.card U = 32) :
    M = L ∨ M = U := by
  have hLU : L.relIndex U = 2 := by
    have hc := (L.subgroupOf U).index_mul_card
    have hcard : Nat.card (L.subgroupOf U) = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe (hLM.trans hMU)).toEquiv).trans hL
    rw [hcard, hU] at hc
    change L.relIndex U * 16 = 32 at hc
    omega
  have hm := relIndex_mul_relIndex L M U hLM hMU
  rw [hLU] at hm
  by_cases hLMone : L.relIndex M = 1
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp hLMone) hLM)
  · right
    have hMUone : M.relIndex U = 1 := by
      by_contra hn
      exact Nat.not_prime_of_mul_eq hm hLMone hn Nat.prime_two
    exact le_antisymm hMU (relIndex_eq_one.mp hMUone)

/-- The two geometric bounds suffice to compute the ambient omega image.
No elementary-abelian assumption on the omega subgroup is needed. -/
public theorem omega_image_cases_of_bounds (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (Q : Type*) [Group Q] (f : Q →* G) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let W := (omega₁ Q (p := 2)).map f
    E ⊓ d.F ≤ W → W ≤ E ⊔ d.F →
      W = E ∨ W = d.F ∨ W = E ⊔ d.F ∨ centralizer (W : Set G) = E ⊔ d.F := by
  intro H J E W hlow hupp
  have hgen : W = (W ⊓ E) ⊔ (W ⊓ d.F) := by
    apply le_antisymm
    · change (omega₁ Q (p := 2)).map f ≤ _
      rw [map_le_iff_le_comap]
      apply (closure_le _).mpr
      intro q hq
      have hq2 : q ^ 2 = 1 := by simpa only [Set.mem_ofPred_eq, pow_one] using hq
      have hqW : f q ∈ W := mem_map_of_mem f (subset_closure hq)
      have hpow : (f q) ^ 2 = 1 := by rw [← map_pow, hq2, map_one]
      rcases d.elementary_join_involution h (f q) (hupp hqW) hpow with hE | hF
      · exact Subgroup.mem_sup_left ⟨hqW, hE⟩
      · exact Subgroup.mem_sup_right ⟨hqW, hF⟩
    · exact sup_le inf_le_left inf_le_left
  have hEcard : Nat.card E = 32 := by
    exact (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans
        (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  have hEc := interval_of_index_two (E ⊓ d.F) (W ⊓ E) E
    (le_inf hlow inf_le_left) inf_le_right d.inf_card hEcard
  have hFc := interval_of_index_two (E ⊓ d.F) (W ⊓ d.F) d.F
    (le_inf hlow inf_le_right) inf_le_right d.inf_card d.card
  rcases hEc with hEz | hEE <;> rcases hFc with hFz | hFF
  · have hW : W = E ⊓ d.F := by rw [hgen, hEz, hFz, sup_idem]
    exact Or.inr (Or.inr (Or.inr (by rw [hW]; exact d.elementary_inf_centralizer h)))
  · exact Or.inr (Or.inl (by rw [hgen, hEz, hFF, sup_eq_right.mpr inf_le_right]))
  · exact Or.inl (by rw [hgen, hEE, hFz, sup_eq_left.mpr inf_le_left])
  · exact Or.inr (Or.inr (Or.inl (by rw [hgen, hEE, hFF])))

/-- Once the local derived computation gives E∩F≤Ω₁(C′)≤A, the first
representative cannot be fused to z. -/
public theorem derived_t_not_isConj_of_omega_bounds (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) (t : G)
    (hlocal : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
      (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G))
    (hcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) = 1024) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
    let W := (omega₁ (commutator C) (p := 2)).map (C.subtype.comp (commutator C).subtype)
    (IsConj z t → E ⊓ d.F ≤ W ∧ W ≤ E ⊔ d.F) → ¬ IsConj z t := by
  intro H J E C W hbounds hconj
  obtain ⟨hlow, hupp⟩ := hbounds hconj
  exact d.local_fusion_omega_derived_cases h hN hself t hlocal (by omega)
    (E ⊔ d.F) (d.elementary_join_commutator h)
    (d.omega_image_cases_of_bounds h (commutator C)
      (C.subtype.comp (commutator C).subtype) hlow hupp) hconj

/-- The first derived representative is not conjugate to z. The omega bounds
are derived from membership in E∖⟨z⟩ and the local centralizer order.
The involution, commutation, and center premises retain the representative's
full local interface, although the omega obstruction needs only the other data. -/
public theorem derived_t_not_isConj (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E, t ∉ zpowers z → orderOf t = 2 → Commute z t →
      H ⊓ centralizer ({t} : Set G) =
        (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      Nat.card C = 1024 → (center C).map C.subtype = closure ({z, t} : Set G) →
      ¬ IsConj z t := by
  intro H J E t ht htz _htwo _hzt hlocal C hcard _hcenter
  exact d.derived_t_not_isConj_of_omega_bounds h hN hself t hlocal hcard
    (fun _ => d.derived_t_omega_bounds h t ht htz hcard)

end Stellmacher.Recognition.ParrottSecondElementaryData
