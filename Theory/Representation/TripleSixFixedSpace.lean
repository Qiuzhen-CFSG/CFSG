module

public import Theory.Representation.TripleSixFixedSpace.Group
public import Theory.Representation.TripleSixFixedSpace.Linear
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.NormNum

/-!
# A cubic fixer for the three-dimensional F₄ triple-six module

Take an element of order four in an extension of A₆ by a group of order
three, and a Sylow two-subgroup containing it. Its fixed space has dimension
at most one over F₄. The stabilizer of a generator has index at most 64
and order divisible by eight. If its order were prime to three, Lagrange
would force order eight or forty. The first contradicts the index bound;
the second is excluded by the actual quotient to A₆. Cauchy's theorem
therefore gives a nonidentity cubic element fixing the whole fixed space.

The proof uses the given faithful action, without any representation
recognition or splitting assumption. The case of zero fixed space is
included by the same generator argument.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2(8), printed p.86; K.1.3, printed p.453; 15.4.18, printed p.1163.
-/

public section
open Subgroup Module MulAction
namespace Representation.TripleSixFixedSpace

variable {G F V : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A cubic element fixes the Sylow fixed space in the actual faithful F₄ action. -/
theorem exists_cubic_fixer (q : G →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hk : Nat.card q.ker = 3)
    (ρ : Representation F G V) (hρ : Function.Injective ρ)
    (hF : Nat.card F = 4) (hd : finrank F V = 3) :
    ∃ (T : Sylow 2 G) (d : G), d ^ 3 = 1 ∧ d ≠ 1 ∧
      ∀ v, (∀ t : T, ρ t v = v) → ρ d v = v := by
  classical
  have hG : Nat.card G = 1080 := cover_card q hq hk
  obtain ⟨x, hx⟩ := cover_has_four q hq
  have h4 : x ^ 4 = 1 := hx ▸ pow_orderOf_eq_one x
  have h2 : x ^ 2 ≠ 1 := by
    intro hh
    have hh' := orderOf_dvd_of_pow_eq_one hh
    norm_num [hx] at hh'
  have hp : IsPGroup 2 (zpowers x) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    rw [Nat.card_zpowers, hx]
    decide
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  let W := Representation.invariants (ρ.comp (T : Subgroup G).subtype)
  have hW : finrank F W ≤ 1 := by
    have hle : W ≤ (ρ x - 1).ker := by
      intro v hv
      change ρ x v - v = 0
      exact sub_eq_zero.mpr (hv ⟨x, hT (mem_zpowers x)⟩)
    apply (Submodule.finrank_mono hle).trans
    exact fixed_rank_le_one hd (ρ x)
      (by rw [← map_pow, h4, map_one])
      (fun he => h2 (hρ (by simpa only [map_pow, map_one] using he)))
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hW
  let : MulAction G V :=
    { smul := fun g v => ρ g v
      one_smul := fun v => LinearMap.congr_fun ρ.map_one v
      mul_smul := fun g h v => LinearMap.congr_fun (ρ.map_mul g h) v }
  let K := stabilizer G (v : V)
  have hTK : (T : Subgroup G) ≤ K := by
    intro t ht
    exact v.property ⟨t, ht⟩
  have h8T : 2 ^ 3 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card (by
    rw [hG]
    decide)
  have h8 : 8 ∣ Nat.card K := h8T.trans (card_dvd_of_le hTK)
  let : Finite V := Module.finite_of_finite F
  have hindex : K.index ≤ 64 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_card _).trans_eq (by
      rw [Module.natCard_eq_pow_finrank (K := F), hF, hd]
      norm_num)
  have h3 : 3 ∣ Nat.card K := by
    by_contra hn
    have hcop : Nat.Coprime (Nat.card K) 3 :=
      ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hn).symm
    have hdvd : Nat.card K ∣ 40 := by
      have hh := K.card_subgroup_dvd_card
      rw [hG] at hh
      exact (hcop.pow_right 3).dvd_of_dvd_mul_left hh
    obtain ⟨n, hn⟩ := h8
    have hn5 : n ∣ 5 := by
      rw [hn] at hdvd
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 8)).mp hdvd
    rcases (by decide : Nat.Prime 5).eq_one_or_self_of_dvd n hn5 with hn1 | hn5
    · have hK : Nat.card K = 8 := by simpa [hn1] using hn
      have hh := K.card_mul_index
      rw [hK, hG] at hh
      omega
    · have hK : Nat.card K = 40 := by simpa [hn5] using hn
      exact cover_no_forty q hk K hK
  obtain ⟨d, hd3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hpow : (d : G) ^ 3 = 1 := congrArg Subtype.val (hd3 ▸ pow_orderOf_eq_one d)
  have hne : (d : G) ≠ 1 := by
    intro he
    have he' : d = 1 := Subtype.ext he
    simp [he'] at hd3
  refine ⟨T, d, hpow, hne, ?_⟩
  intro w hw
  obtain ⟨c, hc⟩ := hv (⟨w, hw⟩ : W)
  have hc' : c • (v : V) = w := congrArg Subtype.val hc
  rw [← hc', map_smul]
  exact congrArg (c • ·) d.property

end Representation.TripleSixFixedSpace
