module

public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.Frattini.PGroup
public import Theory.PGroupCore
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Mathlib.GroupTheory.Schreier

/-!
# Centrality of the rank-one odd-core actor

Let Q have trivial two-core and a normal odd p-core R with two-group
quotient. If the elementary abelian rank-one subgroup a lies in the
specified Sylow two-subgroup S and R = [R,a], then S centralizes a.

The quotient hypothesis gives Q = SR. The kernel of S's conjugation on R
is normalized by S and centralized by R, so it lies in O₂(Q) and vanishes.
Burnside's Frattini-kernel theorem preserves this faithfulness on R/Φ(R).
The nonidentity element of a inverts each commutator generator modulo
Φ(R), hence the whole abelian quotient. Inversion commutes with every
automorphism, and faithfulness therefore gives centrality in S.

This is the actor-centrality ingredient of the minimal odd-member reduction
in Aschbacher–Smith, E.5.2, printed p.243, using E.1.2(E1), printed p.210
(combined manuscript, 1 March 2004). No irreducibility is assumed.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterE

private theorem faithful_sylow_on_normal_supplement
    {Q : Type*} [Group Q] [Finite Q] (R : Subgroup Q) [R.Normal]
    (S : Sylow 2 Q) (hgen : (S : Subgroup Q) ⊔ R = ⊤)
    (hcore : pCore 2 Q = ⊥) :
    Function.Injective ((MulAut.conjNormal : Q →* MulAut R).comp (S : Subgroup Q).subtype) := by
  let C := (S : Subgroup Q) ⊓ centralizer (R : Set Q)
  have hnorm : (⊤ : Subgroup Q) ≤ normalizer (C : Set Q) := by
    rw [← hgen]
    apply sup_le
    · exact (le_inf (S : Subgroup Q).le_normalizer le_normalizer_of_normal).trans
        inf_normalizer_le_normalizer_inf
    · exact (le_centralizer_iff.mp (show C ≤ centralizer (R : Set Q) from inf_le_right)).trans
        (centralizer_le_normalizer _)
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique hnorm)
  have hC : C ≤ pCore 2 Q := le_sSup ⟨inferInstance, S.isPGroup'.to_le inf_le_left⟩
  have hCbot : C = ⊥ := bot_unique (hcore ▸ hC)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro s hs
  have hsc : (s : Q) ∈ centralizer (R : Set Q) := by
    rw [mem_centralizer_iff]
    intro r hr
    have he := congrArg (fun f : MulAut R => (f ⟨r, hr⟩ : Q)) hs
    change (s : Q) * r * (s : Q)⁻¹ = r at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hsb : (s : Q) ∈ C := ⟨s.property, hsc⟩
  rw [hCbot] at hsb
  exact Subtype.ext hsb

private theorem rank_one_binary_card
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hrank : Group.rank A = 1) : Nat.card A = 2 := by
  have hd : Nat.card A ∣ 2 := by
    have h := (card_dvd_exponent_pow_rank A).trans
      (pow_dvd_pow_of_dvd (IsElementaryAbelian.exponent_dvd_p 2 A) (Group.rank A))
    simpa [hrank] using h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h).1
    have := Group.rank_eq_zero A
    omega
  · exact h

private theorem quotient_actor_inverts
    {Q : Type*} [Group Q] [Finite Q] (R a : Subgroup Q) [R.Normal]
    [IsMulCommutative (R ⧸ frattini R)]
    (t : Q) (htwo : t * t = 1) (ha : ∀ b ∈ a, b = 1 ∨ b = t)
    (hcomm : R = ⁅R, a⁆) :
    ∀ v : R ⧸ frattini R,
      quotientAut (frattini R) (MulAut.conjNormal t) v = v⁻¹ := by
  let c : Q →* MulAut R := MulAut.conjNormal
  let q := QuotientGroup.mk' (frattini R)
  let f := quotientAut (frattini R) (c t)
  let D : Subgroup R := (f.toMonoidHom.comp q).eqLocus
    ((MulEquiv.inv (R ⧸ frattini R)).toMonoidHom.comp q)
  have hc2 (x : R) : c t (c t x) = x := by
    change (c t * c t) x = x
    rw [← map_mul, htwo, map_one]
    rfl
  have hgen : ⁅R, a⁆ ≤ D.map R.subtype := by
    apply commutator_le.mpr
    intro r hr b hb
    rcases ha b hb with hb1 | hbt
    · subst b
      simp
    · subst b
      let x : R := ⟨r, hr⟩
      refine mem_map.mpr ⟨x * c t x⁻¹, ?_, ?_⟩
      · change f (q (x * c t x⁻¹)) = (q (x * c t x⁻¹))⁻¹
        change quotientAut (frattini R) (c t) (q (x * c t x⁻¹)) = _
        rw [quotientAut_apply_mk]
        change q (c t (x * c t x⁻¹)) = _
        rw [map_mul, hc2]
        simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
      · change r * (t * r⁻¹ * t⁻¹) = r * t * r⁻¹ * t⁻¹
        simp only [mul_assoc]
  have hD : D = ⊤ := by
    apply top_unique
    intro r _
    obtain ⟨x, hx, he⟩ := mem_map.mp (hgen (hcomm.le r.property))
    have heq : x = r := Subtype.ext he
    exact heq ▸ hx
  intro v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini R) v
  exact (show x ∈ D from hD ▸ mem_top x)

/-- The rank-one binary actor in E.1.2(E1) centralizes the prescribed Sylow
subgroup after removal of the two-core. -/
public theorem sylow_le_centralizer_of_rank_one_odd_core_actor
    {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (S : Sylow 2 Q) (a : Subgroup Q)
    (hcore : pCore 2 Q = ⊥) (hquot : IsPGroup 2 (Q ⧸ pCore p Q))
    (_hne : pCore p Q ≠ ⊥) (ha : IsElementaryAbelian 2 a)
    (haS : a ≤ (S : Subgroup Q)) (hrank : Group.rank a = 1)
    (hcomm : pCore p Q = ⁅pCore p Q, a⁆) :
    (S : Subgroup Q) ≤ centralizer (a : Set Q) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian 2 a := ha
  let R := pCore p Q
  have hR : IsPGroup p R := pCore_isPGroup
  let : Fact (IsPGroup p R) := ⟨hR⟩
  let : IsElementaryAbelian p (R ⧸ frattini R) :=
    isElementaryAbelian_quotient_frattini (p := p)
  obtain ⟨t, _htne, huniq⟩ := (Nat.card_eq_two_iff' (1 : a)).mp
    (rank_one_binary_card hrank)
  have hcases : ∀ b ∈ a, b = 1 ∨ b = (t : Q) := by
    intro b hb
    by_cases h1 : b = 1
    · exact Or.inl h1
    · exact Or.inr (congrArg Subtype.val (huniq ⟨b, hb⟩ (by
        intro he
        exact h1 (congrArg Subtype.val he))))
  have ht2 : (t : Q) * t = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian
      (p := 2) (t : Q) t.property
  have hinv := quotient_actor_inverts R a (t : Q) ht2 hcases hcomm
  let c : S →* MulAut R :=
    (MulAut.conjNormal : Q →* MulAut R).comp (S : Subgroup Q).subtype
  have hfaith : Function.Injective c := faithful_sylow_on_normal_supplement R S
    (S.sup_eq_top_of_quotient_isPGroup R hquot) hcore
  have hcop : Nat.Coprime (Nat.card S) p := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact hpodd.coprime_two_left.pow_left n
  let d := (quotientAut (frattini R)).comp c
  have hd : Function.Injective d :=
    MonoidHom.injective_frattini_action_of_coprime hR c hfaith hcop
  let tS : S := ⟨t, haS t.property⟩
  have htinv (v : R ⧸ frattini R) : d tS v = v⁻¹ := hinv v
  have htcentral (s : S) : tS * s = s * tS := by
    apply hd
    rw [map_mul, map_mul]
    apply MulEquiv.ext
    intro v
    change d tS (d s v) = d s (d tS v)
    rw [htinv, htinv, map_inv]
  intro s hs
  rw [mem_centralizer_iff]
  intro b hb
  rcases hcases b hb with rfl | rfl
  · simp
  · exact congrArg Subtype.val (htcentral ⟨s, hs⟩)

end CFSG.Quasithin.ChapterE
