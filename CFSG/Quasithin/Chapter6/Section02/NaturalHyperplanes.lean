module
public import CFSG.Quasithin.Chapter6.Section02.NaturalSylowGeometry
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.CharacteristicCentralizerFusion


/-!
# Natural eight-groups at the marked Sylow plane

For the literal natural action of L/O₂(L) on V, displacements of a vector
outside the Sylow fixed field-line exhaust that line. Therefore every
order-eight subgroup of the natural SL₂(4) module has commutator with the
Sylow subgroup equal to the marked four-group C_V(S).

An element of order three in L survives the two-core quotient and fixes
only the identity of V. Orbit counting excludes an invariant subgroup of
order eight. If the cubic also normalizes S, it preserves C_V(S); hence
two distinct eight-groups A and A raised to the inverse-conjugation action
meet exactly in that four-group. The final theorem applies both facts to
the original Chapter 6 layer and its actual ambient Sylow intersection.

This supplies the natural-module part of P ∩ Pᵈ = Z_S in the proof of
Aschbacher–Smith 6.2.13, printed p.688 (combined manuscript PDF p.705).
The earlier natural-module selection and the later M₂₂ recognition are
separate source results.
-/

public noncomputable section

open Subgroup Matrix.SpecialLinearGroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G} {n : ℕ}

/-- Every element of the marked fixed plane is a single Sylow displacement. -/
theorem IsNaturalModule.sylow_displacement_surjective (h : IsNaturalModule L V n)
    (S : Sylow 2 L) {v : G} (hv : v ∈ V)
    (hne : v ∉ centralizer ((S : Subgroup L).map L.subtype : Set G))
    {w : G} (hw : w ∈ V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G)) :
    ∃ s ∈ (S : Subgroup L).map L.subtype, ⁅s, v⁆ = w := by
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := h
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hq
  obtain ⟨W, _, hWfix, _, hWonto⟩ :=
    Representation.SpecialLinearTwo.sylow_fixed_line_displacements 2 P
  let j : Multiplicative (Fin 2 → F) →* G := V.subtype.comp f.symm.toMonoidHom
  have hj : Function.Injective j := V.subtype_injective.comp f.symm.injective
  have hconj (s : L) (u : V) :
      j (Multiplicative.ofAdd (toLin' (q s) (f u).toAdd)) =
        (s : G) * (u : G) * (s : G)⁻¹ := hf s u
  have hfix (u : V) : (f u).toAdd ∈ W ↔
      (u : G) ∈ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
    rw [hWfix]
    constructor
    · intro hu
      apply mem_centralizer_iff.mpr
      rintro _ ⟨s, hs, rfl⟩
      have hh := hconj s u
      rw [hu (q s) (mem_map.mpr ⟨s, hs, rfl⟩)] at hh
      change (f.symm (f u) : G) = _ at hh
      rw [f.symm_apply_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
    · intro hu g hg
      obtain ⟨s, hs, rfl⟩ := hg
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hconj]
      change (s : G) * (u : G) * (s : G)⁻¹ = (f.symm (f u) : G)
      rw [f.symm_apply_apply, mem_centralizer_iff.mp hu (s : G)
        (mem_map.mpr ⟨s, hs, rfl⟩), mul_inv_cancel_right]
  obtain ⟨g, hg, he⟩ := hWonto (f ⟨v,hv⟩).toAdd
    (fun hh => hne ((hfix ⟨v,hv⟩).mp hh)) (f ⟨w,hw.1⟩).toAdd
    ((hfix ⟨w,hw.1⟩).mpr hw.2)
  obtain ⟨s, hs, rfl⟩ := hg
  refine ⟨s, mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
  have hh := congrArg (fun u => j (Multiplicative.ofAdd u)) he
  rw [ofAdd_sub, map_div, ofAdd_toAdd, hconj] at hh
  change ((s : G) * v * (s : G)⁻¹) / (f.symm (f ⟨v,hv⟩) : G) =
    (f.symm (f ⟨w,hw.1⟩) : G) at hh
  simpa only [f.symm_apply_apply, div_eq_mul_inv, commutatorElement_def] using hh

/-- Every eight-group in the natural four-space has the full Sylow commutator. -/
theorem IsNaturalModule.eight_sylow_commutator (h : IsNaturalModule L V 2)
    (S : Sylow 2 L) (A : Subgroup G) (hAV : A ≤ V) (hA : Nat.card A = 8) :
    ⁅A, (S : Subgroup L).map L.subtype⁆ =
      V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
  obtain ⟨hc, he⟩ := h.sylow_fixed_geometry S
  have hn : ¬ A ≤ V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
    intro ha
    have hb := card_le_of_le ha
    rw [hA, hc] at hb
    norm_num at hb
  obtain ⟨v,hv,hnv⟩ := SetLike.not_le_iff_exists.mp hn
  have hne : v ∉ centralizer ((S : Subgroup L).map L.subtype : Set G) :=
    fun hh => hnv ⟨hAV hv, hh⟩
  apply le_antisymm
  · exact (commutator_mono hAV le_rfl).trans he.le
  · intro w hw
    obtain ⟨s,hs,rfl⟩ := h.sylow_displacement_surjective S (hAV hv) hne hw
    rw [commutator_comm A]
    exact commutator_mem_commutator hs hv

omit [Finite G] in
/-- A cubic in the original L is fixed-free on its natural layer. -/
theorem IsNaturalModule.cubic_fixed_eq_one (h : IsNaturalModule L V n)
    {d : G} (hdL : d ∈ L) (hd : orderOf d = 3)
    {v : G} (hv : v ∈ V) (hfix : d * v * d⁻¹ = v) : v = 1 := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := h
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let dL : L := ⟨d,hdL⟩
  have hdLorder : orderOf dL = 3 := (Subgroup.orderOf_mk d hdL).trans hd
  have hqne : q dL ≠ 1 := by
    intro hq
    have hm : QuotientGroup.mk' (pCore 2 L) dL = 1 :=
      e.injective (hq.trans (map_one e).symm)
    have hdcore : dL ∈ pCore 2 L := (QuotientGroup.eq_one_iff dL).mp hm
    have hc := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨dL,hdcore⟩ : pCore 2 L)
    rw [Subgroup.orderOf_mk, hdLorder] at hc
    norm_num at hc
  have hqorder : orderOf (q dL) = 3 := orderOf_eq_prime
    (by rw [← map_pow, ← hdLorder, pow_orderOf_eq_one, map_one]) hqne
  have hvfix : toLin' (q dL) (f ⟨v,hv⟩).toAdd = (f ⟨v,hv⟩).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply V.subtype_injective
    change (f.symm (Multiplicative.ofAdd (toLin' (q dL) (f ⟨v,hv⟩).toAdd)) : G) =
      (f.symm (f ⟨v,hv⟩) : G)
    rw [f.symm_apply_apply]
    exact (hf dL ⟨v,hv⟩).trans hfix
  have hz := Matrix.SL2.cubic_fixed_eq_zero (q dL) hqorder (f ⟨v,hv⟩).toAdd hvfix
  have hvone : f ⟨v,hv⟩ = 1 := Multiplicative.toAdd.injective hz
  exact congrArg (fun x : V => (x : G))
    (f.injective (hvone.trans (map_one f).symm))

/-- A fixed-free cubic cannot preserve a subgroup with seven nonidentity elements. -/
theorem IsNaturalModule.eight_not_normalized_by_cubic (h : IsNaturalModule L V n)
    (A : Subgroup G) (hAV : A ≤ V) (hA : Nat.card A = 8)
    {d : G} (hdL : d ∈ L) (hd : orderOf d = 3) :
    d ∉ normalizer (A : Set G) := by
  intro hn
  let C := zpowers d
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by
    simpa only [C, Nat.card_zpowers, pow_one] using hd)
  have hz : A ⊓ centralizer (C : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    exact h.cubic_fixed_eq_one hdL hd (hAV hx.1)
      (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx.2 d (mem_zpowers d)))
  have hm := card_modEq_card_inf_centralizer C A hp (zpowers_le.mpr hn)
  rw [hz, card_bot, hA] at hm
  norm_num [Nat.ModEq] at hm

/-- The exact source conjugation convention gives the marked Sylow plane. -/
theorem IsNaturalModule.eight_cubic_conjugate_intersection
    (h : IsNaturalModule L V 2) (S : Sylow 2 L)
    (A : Subgroup G) (hAV : A ≤ V) (hA : Nat.card A = 8)
    (hZA : V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) ≤ A)
    {d : G} (hdL : d ∈ L)
    (hdS : d ∈ normalizer ((S : Subgroup L).map L.subtype : Set G))
    (hd : orderOf d = 3) :
    A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom =
      V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
  let Z := V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G)
  have hZ : Nat.card Z = 4 := by simpa only [Z, show 2 ^ 2 = 4 by decide] using (h.sylow_fixed_geometry S).1
  have hdV : d ∈ normalizer (V : Set G) := by
    obtain ⟨_,_,_,_,_,hm⟩ := h
    exact hm.normalizes hdL
  have hdZ : d ∈ normalizer (Z : Set G) := by
    apply inf_normalizer_le_normalizer_inf
    exact ⟨hdV, normalizer_le_normalizer_centralizer _ hdS⟩
  have hZmap : Z.map (MulAut.conj d⁻¹).toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (Z : Set G)).inv_mem hdZ)
  have hZI : Z ≤ A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom := by
    refine le_inf hZA ?_
    rw [← hZmap]
    exact map_mono hZA
  have hne : A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom ≠ A := by
    intro he
    have hle : A ≤ A.map (MulAut.conj d⁻¹).toMonoidHom := by
      calc A = A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom := he.symm
           _ ≤ A.map (MulAut.conj d⁻¹).toMonoidHom := inf_le_right
    have hsame : A.map (MulAut.conj d⁻¹).toMonoidHom = A :=
      (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj d⁻¹).injective])).symm
    apply h.eight_not_normalized_by_cubic A hAV hA hdL hd
    simpa only [inv_inv] using (normalizer (A : Set G)).inv_mem
      (mem_normalizer_iff_map_conj_eq.mpr hsame)
  have hcard : Nat.card (A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom : Subgroup G) = 4 := by
    have hdvd : Nat.card (A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom : Subgroup G) ∣ 2 ^ 3 := by
      simpa only [hA, show 2 ^ 3 = 8 by decide] using card_dvd_of_le (show A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom ≤ A from inf_le_left)
    obtain ⟨k,hk,hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hlo : 4 ≤ Nat.card (A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom : Subgroup G) :=
      hZ ▸ card_le_of_le hZI
    have hlt : Nat.card (A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom : Subgroup G) < 8 := by
      have hle := card_le_of_le (show A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom ≤ A from inf_le_left)
      have hcne : Nat.card (A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom : Subgroup G) ≠ Nat.card A := by
        intro he
        exact hne (eq_of_le_of_card_ge inf_le_left he.ge)
      omega
    interval_cases k <;> norm_num only [Nat.reducePow] at hkcard <;> omega
  exact (eq_of_le_of_card_ge hZI (by rw [hcard,hZ])).symm

namespace Hypothesis611
variable {κ : GroupClass} {T : Sylow 2 G} {M V₀ : Subgroup G}

/-- The two natural-module inputs for source 6.2.13 on the actual Chapter 6 layer. -/
theorem natural_eight_cubic_geometry (h : Hypothesis611 κ T L M V₀ n)
    (hnat : IsNaturalModule L (layer L V₀) 2)
    (A : Subgroup G) (hAV : A ≤ layer L V₀) (hA : Nat.card A = 8)
    (hZA : ZS (T : Subgroup G) L V₀ ≤ A)
    {d : G} (hdL : d ∈ L)
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G))
    (hd : orderOf d = 3) :
    ⁅A, (T : Subgroup G) ⊓ L⁆ = ZS (T : Subgroup G) L V₀ ∧
      A ⊓ A.map (MulAut.conj d⁻¹).toMonoidHom = ZS (T : Subgroup G) L V₀ := by
  have hTL : (T : Subgroup G) ≤ normalizer (L : Set G) :=
    h.sylow_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
  obtain ⟨S, hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hbar : (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hS, subgroupOf_map_subtype]
  constructor
  · simpa only [hbar, ZS, coe_inf, Set.inf_eq_inter] using hnat.eight_sylow_commutator S A hAV hA
  · exact hnat.eight_cubic_conjugate_intersection S A hAV hA
      (by simpa only [hbar, ZS, coe_inf, Set.inf_eq_inter] using hZA) hdL
      (by simpa only [hbar, coe_inf, Set.inf_eq_inter] using hdS) hd |>.trans (by rw [hbar]; rfl)

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
