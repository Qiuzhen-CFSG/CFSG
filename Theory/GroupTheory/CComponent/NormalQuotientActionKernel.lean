module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# Exact kernel of a normal component's two-core quotient action

The intrinsic quotient B/O₂(B) is the actual image of B in G/O₂(G).
This identification respects conjugation. If that image has trivial
centralizer, the kernel of the literal action G → Aut(B/O₂(B)) is O₂(G).
The proof checks the quotient formula on original component elements.

Source: the component action in Aschbacher–Smith 14.7.26, printed p.1053,
using the A.3.3 quotient correspondence, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {A : Type*} [Group A] [Finite A]

/-- The literal conjugation action on the intrinsic component quotient has
exactly the ambient two-core as kernel when its quotient image is faithful. -/
theorem IsCComponent.normalQuotientAction_ker_of_centralizer_eq_bot
    {B : Subgroup A} [B.Normal] (hB : B.IsCComponent)
    (hc : centralizer (B.map (QuotientGroup.mk' (pCore 2 A)) : Set (A ⧸ pCore 2 A)) = ⊥) :
    (normalQuotientAction B (pCore 2 B)).ker = pCore 2 A := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let e := cComponentTwoCoreQuotientEquiv hB
  have ha (g : A) (z : B ⧸ pCore 2 B) :
      (e (normalQuotientAction B (pCore 2 B) g z) : A ⧸ pCore 2 A) =
        q g * (e z : A ⧸ pCore 2 A) * (q g)⁻¹ := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    rw [normalQuotientAction_apply_mk]
    change q (g * (b : A) * g⁻¹) = q g * q (b : A) * (q g)⁻¹
    rw [map_mul,map_mul,map_inv]
  ext g
  constructor
  · intro hg
    have he : normalQuotientAction B (pCore 2 B) g = 1 := hg
    have hcent : q g ∈ centralizer (B.map q : Set (A ⧸ pCore 2 A)) := by
      intro z hz
      obtain ⟨w,hw⟩ := e.surjective ⟨z,hz⟩
      have hh := ha g w
      rw [he] at hh
      change (e w : A ⧸ pCore 2 A) = q g * (e w : A ⧸ pCore 2 A) * (q g)⁻¹ at hh
      rw [hw] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    exact (QuotientGroup.eq_one_iff g).mp (mem_bot.mp (hc ▸ hcent))
  · intro hg
    have hq : q g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    apply MulEquiv.ext
    intro z
    apply e.injective
    apply Subtype.ext
    change (e (normalQuotientAction B (pCore 2 B) g z) : A ⧸ pCore 2 A) = (e z : A ⧸ pCore 2 A)
    simpa only [hq,one_mul,inv_one,mul_one] using ha g z
end Subgroup
