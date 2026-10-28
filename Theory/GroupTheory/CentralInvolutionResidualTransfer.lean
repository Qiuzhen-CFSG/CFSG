module

public import Theory.GroupTheory.FusionInvariantTransfer
public import Theory.GroupTheory.PResidual.Defs
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Transfer of a central Sylow involution

If all involutions of a Sylow two-subgroup are central, Burnside fusion
moves an involution only by its Sylow normalizer. When that normalizer fixes
the involution, an elementary abelian character detecting it also detects
it under transfer. Its transfer kernel contains the two-residual.

Source application: Aschbacher–Smith, J.2.9, printed p.438, using the
generalized Thompson transfer of A.1.37(2).
-/

public section
namespace Sylow
open Subgroup
variable {G A : Type*} [Group G] [Finite G] [CommGroup A]
  [IsElementaryAbelian 2 A]

/-- Burnside fusion fixes a Sylow involution fixed by the Sylow normalizer,
when all Sylow involutions are central. -/
theorem involution_fusion_eq_of_normalizer_centralizes (P : Sylow 2 G)
    (hcentral : ∀ x : P, x ^ 2 = 1 → (x : G) ∈ centralizer (P : Set G))
    (x : P) (hx : x ^ 2 = 1)
    (hfix : normalizer (P : Set G) ≤ centralizer ({(x : G)} : Set G))
    (y : P) (hxy : IsConj (x : G) (y : G)) : y = x := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hy : y ^ 2 = 1 := by
    apply Subtype.ext
    change (y : G) ^ 2 = 1
    have hxG : (x : G) ^ 2 = 1 := congrArg Subtype.val hx
    have he := congrArg (MulAut.conj g) hxG
    simpa only [map_pow, map_one, MulAut.conj_apply, hg] using he
  have hg' : g⁻¹⁻¹ * (x : G) * g⁻¹ = y := by simpa using hg
  obtain ⟨n, hn, he⟩ := P.conj_eq_normalizer_conj_of_mem_centralizer
    (x : G) g⁻¹ (hcentral x hx) (hg' ▸ hcentral y hy)
  apply Subtype.ext
  rw [← hg', he]
  have hc := mem_centralizer_singleton_iff.mp (hfix hn)
  calc
    n⁻¹ * (x : G) * n = n⁻¹ * ((x : G) * n) := mul_assoc _ _ _
    _ = n⁻¹ * (n * (x : G)) := by rw [hc]
    _ = x := inv_mul_cancel_left _ _

/-- An elementary abelian character detecting a fusion-fixed involution
separates that involution from the literal two-residual. -/
theorem not_mem_twoResidual_of_central_involution (P : Sylow 2 G)
    (hcentral : ∀ x : P, x ^ 2 = 1 → (x : G) ∈ centralizer (P : Set G))
    (character : P →* A) (x : P) (hx : x ^ 2 = 1)
    (hfix : normalizer (P : Set G) ≤ centralizer ({(x : G)} : Set G))
    (hdetect : character x ≠ 1) : (x : G) ∉ pResidual 2 G := by
  have hrespect (k : ℕ) (y : P)
      (hxy : IsConj (((x ^ k) : P) : G) (y : G)) :
      character y = character (x ^ k) := by
    have hpower : x ^ k = x ^ (k % 2) := pow_eq_pow_mod k hx
    rw [hpower] at hxy ⊢
    have hk : k % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize k % 2 = r at hxy ⊢ hk
    interval_cases r
    · have hy : y = 1 := Subtype.ext (isConj_one_right.mp (by simpa using hxy))
      simp [hy]
    · simp only [pow_one] at hxy ⊢
      rw [P.involution_fusion_eq_of_normalizer_centralizes hcentral x hx hfix y hxy]
  have ht := character.transfer_apply_eq_pow_of_conjugate_powers x hrespect
  have hodd : (P : Subgroup G).index % 2 = 1 := by
    have := P.not_dvd_index
    omega
  have hsquare : character x ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hp : character x ^ (P : Subgroup G).index = character x := by
    rw [pow_eq_pow_mod _ hsquare, hodd, pow_one]
  have hr : IsPGroup 2 character.transfer.range :=
    (IsElementaryAbelian.isPGroup 2 A).of_injective
      character.transfer.range.subtype character.transfer.range.subtype_injective
  have hq : IsPGroup 2 (G ⧸ character.transfer.ker) :=
    hr.of_equiv (QuotientGroup.quotientKerEquivRange character.transfer).symm
  have hle : pResidual 2 G ≤ character.transfer.ker := sInf_le ⟨inferInstance, hq⟩
  intro hm
  exact hdetect (hp.symm.trans (ht.symm.trans (hle hm)))

end Sylow
