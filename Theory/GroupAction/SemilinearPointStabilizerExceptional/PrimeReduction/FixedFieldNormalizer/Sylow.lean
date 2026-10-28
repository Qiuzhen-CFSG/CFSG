module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.ScalarQuotients
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# From the cyclic Sylow normalizer to the order-p coefficient subgroup

Coprimality to the field and scalar orders makes a coefficient Sylow
subgroup Sylow in the whole actor. Its first omega subgroup has order p.
If that subgroup had centralizing normalizer, conjugation on the cyclic
Sylow subgroup would lie in the p-group kernel of omega restriction. The
same image has order prime to p, since the Sylow subgroup centralizes itself.
Thus its normalizer would centralize it, contradicting the checked Burnside
transfer obstruction from scalar normal generation.

Source: GLS, Volume 4, Chapter 1, Lemma 3.9, the passage from Q = R to
N_X(P) > C_X(P), `refs/KGroup/GLS4/Chapter1.tex`, lines 444–446.
The scalar-order coprimality is an earlier-step input, not a conclusion here.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace MulAction.SemilinearPointStabilizer.Coordinates

private theorem cyclic_sylow_omega_normalizer_not_le
    {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (Q : Sylow p X) [IsCyclic Q]
    (hNC : ¬ normalizer (Q : Set X) ≤ centralizer (Q : Set X)) :
    ¬ normalizer ((omega Q (p := p) 1).map (Q : Subgroup X).subtype : Set X) ≤
      centralizer ((omega Q (p := p) 1).map (Q : Subgroup X).subtype : Set X) := by
  intro h
  let W := omega Q (p := p) 1
  let : W.Characteristic := omega_characteristic Q 1
  let f := (Q : Subgroup X).normalizerMonoidHom
  have hf : f.range ≤ (OmegaAction.omegaRestriction Q p 1).ker := by
    rintro _ ⟨g, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have hn := normalizer_le_normalizer_characteristic_image (Q : Subgroup X) W g.property
    have hc := h hn (x : X) ⟨(x : Q), x.property, rfl⟩
    apply Subtype.ext
    change (g : X) * (x : X) * (g : X)⁻¹ = (x : X)
    rw [← hc, mul_inv_cancel_right]
  have hfp := (OmegaAction.restriction_kernel_isPGroup Q.isPGroup').to_le hf
  obtain ⟨k, hk⟩ := hfp.exists_card_eq
  let Z := centralizer (Q : Set X)
  let N := normalizer (Q : Set X)
  have ha : Z.relIndex N ∣ p ^ k := by
    have he : Z.relIndex N = Nat.card f.range := by
      rw [← Subgroup.index_ker, Subgroup.normalizerMonoidHom_ker]
      rfl
    rw [he, hk]
  have hQZ : (Q : Subgroup X) ≤ Z := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : Q) ⟨x, hx⟩)
  have hi : Z.relIndex N ∣ (Q : Subgroup X).index :=
    (Subgroup.relIndex_dvd_of_le_left N hQZ).trans
      (Subgroup.relIndex_dvd_index_of_le (hQZ.trans (centralizer_le_normalizer _)))
  have hcop : Nat.Coprime ((Q : Subgroup X).index) (p ^ k) :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr Q.not_dvd_index).symm.pow_right k
  exact hNC (Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop hi ha))

variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
variable [MulAction X F] [FaithfulSMul X F] (c : Coordinates X F)
include c

/-- The coefficient Sylow subgroup is Sylow in the whole actor when p is
coprime to the scalar order and to the field order. -/
theorem exists_coefficient_sylow {n p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (htwo : MulAction.IsMultiplyPretransitive X F 2) (hF : Nat.card F = 2 ^ n)
    (hcop : p.Coprime (Nat.card F - 1)) :
    ∃ Q : Sylow p X, (Q : Subgroup X) ≤ twoPoint (X := X) (F := F) := by
  let : Fact p.Prime := ⟨hp⟩
  let : MulAction.IsPreprimitive X F := MulAction.isPreprimitive_of_is_two_pretransitive htwo
  let Γ := twoPoint (X := X) (F := F)
  let Q₀ : Sylow p Γ := Classical.choice inferInstance
  let Q := (Q₀ : Subgroup Γ).map Γ.subtype
  have hindexΓ : Γ.index = Nat.card F * (Nat.card F - 1) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Γ))
    rw [Γ.index_mul_card, c.card_group]
  have hpΓindex : ¬ p ∣ Γ.index := by
    rw [hindexΓ]
    intro h
    rcases hp.dvd_mul.mp h with hf | hk
    · rw [hF] at hf
      have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hf) |>.resolve_left hp.ne_one
      exact hodd.not_two_dvd_nat (hp2 ▸ dvd_rfl)
    · exact hp.coprime_iff_not_dvd.mp hcop hk
  have hQp : IsPGroup p Q := Q₀.isPGroup'.map Γ.subtype
  have hQi : ¬ p ∣ Q.index := by
    dsimp [Q]
    rw [Subgroup.index_map_subtype]
    intro h
    exact (hp.dvd_mul.mp h).elim Q₀.not_dvd_index hpΓindex
  exact ⟨hQp.toSylow hQi, Subgroup.map_subtype_le _⟩

/-- Burnside's obstruction descends from the cyclic coefficient Sylow group
to its actual order-p omega subgroup. -/
theorem exists_prime_coefficient_noncentral_normalizer {n p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (htwo : MulAction.IsMultiplyPretransitive X F 2)
    (hF : Nat.card F = 2 ^ n) (hgen : c.scalarClosure = ⊤)
    (hcop : p.Coprime (Nat.card F - 1))
    (hpdvd : p ∣ Nat.card (twoPoint (X := X) (F := F))) :
    ∃ P : Subgroup X, P ≤ twoPoint (X := X) (F := F) ∧ Nat.card P = p ∧
      ¬ normalizer (P : Set X) ≤ centralizer (P : Set X) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQΓ⟩ := c.exists_coefficient_sylow hp hodd htwo hF hcop
  let : IsCyclic (twoPoint (X := X) (F := F)) := c.twoPoint_isCyclic
  let : IsCyclic Q := isCyclic_of_injective (Subgroup.inclusion hQΓ) (Subgroup.inclusion_injective hQΓ)
  have hpX := hpdvd.trans (twoPoint (X := X) (F := F)).card_subgroup_dvd_card
  let P := (omega Q (p := p) 1).map (Q : Subgroup X).subtype
  refine ⟨P, (Subgroup.map_subtype_le _).trans hQΓ, ?_, ?_⟩
  · dsimp [P]
    rw [Subgroup.card_map_of_injective (Q : Subgroup X).subtype_injective,
      OmegaAction.omega_eq_pow_ker, IsCyclic.card_powMonoidHom_ker, pow_one]
    exact Nat.gcd_eq_right (Q.dvd_card_of_dvd_card hpX)
  · exact cyclic_sylow_omega_normalizer_not_le Q
      (c.sylow_normalizer_not_le_centralizer hgen hcop hpX Q)

end MulAction.SemilinearPointStabilizer.Coordinates
