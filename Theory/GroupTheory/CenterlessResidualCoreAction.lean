module
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.CenterlessCentralizer
public import Theory.GroupTheory.PResidual.PrimeToSubnormal

/-!
# Centerless residuals and the exact core-quotient action kernel

The centralizer of a centerless prime-to-p residual has order prime to p;
it vanishes when the p-prime core does. For any normal subgroup B, its
intrinsic r-core quotient is its actual image modulo the ambient r-core.
Conjugation equivariance of this identification makes the kernel of the
literal quotient action exactly the ambient r-core when the image has
trivial centralizer.

Source application: Aschbacher–Smith, proof of 14.7.32, printed p.1056,
with the whole two-component orbit, not one selected component.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {A : Type*} [Group A] [Finite A]

/-- The centerless prime-to-p residual is self-centralizing when the p-prime core vanishes. -/
theorem centralizer_primeToResidual_eq_bot_of_center_eq_bot
    (p : ℕ) [Fact p.Prime]
    (hz : center (primeToResidual p A) = ⊥) (hc : pPrimeCore p A = ⊥) :
    centralizer (primeToResidual p A : Set A) = ⊥ := by
  have hd := centralizer_card_dvd_index_of_center_eq_bot (primeToResidual p A) hz
  have hle : centralizer (primeToResidual p A : Set A) ≤ pPrimeCore p A :=
    le_sSup ⟨inferInstance, (primeToResidual_index_coprime p).coprime_dvd_right hd⟩
  exact bot_unique (hle.trans_eq hc)

omit [Finite A] in
/-- Exact kernel on the intrinsic core quotient of a normal subgroup. -/
theorem normalQuotientAction_pCore_ker_of_centralizer_eq_bot
    (p : ℕ) (B : Subgroup A) [B.Normal]
    (hc : centralizer (B.map (QuotientGroup.mk' (pCore p A)) : Set (A ⧸ pCore p A)) = ⊥) :
    (normalQuotientAction B (pCore p B)).ker = pCore p A := by
  let q := QuotientGroup.mk' (pCore p A)
  let e := coreQuotientEquivImage p B
  have ha (g : A) (z : B ⧸ pCore p B) :
      (e (normalQuotientAction B (pCore p B) g z) : A ⧸ pCore p A) =
        q g * (e z : A ⧸ pCore p A) * (q g)⁻¹ := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore p B) z
    rw [normalQuotientAction_apply_mk]
    simp only [e, coreQuotientEquivImage_apply_mk]
    change q (g * (b : A) * g⁻¹) = q g * q (b : A) * (q g)⁻¹
    rw [map_mul,map_mul,map_inv]
  ext g
  constructor
  · intro hg
    have he : normalQuotientAction B (pCore p B) g = 1 := hg
    have hcent : q g ∈ centralizer (B.map q : Set (A ⧸ pCore p A)) := by
      intro z hz
      obtain ⟨w,hw⟩ := e.surjective ⟨z,hz⟩
      have hh := ha g w
      rw [he] at hh
      change (e w : A ⧸ pCore p A) = q g * (e w : A ⧸ pCore p A) * (q g)⁻¹ at hh
      rw [hw] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    exact (QuotientGroup.eq_one_iff g).mp (mem_bot.mp (hc ▸ hcent))
  · intro hg
    have hq : q g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    apply MulEquiv.ext
    intro z
    apply e.injective
    apply Subtype.ext
    change (e (normalQuotientAction B (pCore p B) g z) : A ⧸ pCore p A) = (e z : A ⧸ pCore p A)
    simpa only [hq,one_mul,inv_one,mul_one] using ha g z
end Subgroup
