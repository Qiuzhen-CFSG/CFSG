module

public import Stellmacher.Recognition.SimpleInputs
public import Glauberman.ZStar.CoreFree

/-!
# Distinct Sylow conjugates of simple-group involutions

An involution in a Sylow two-subgroup of a finite nonsolvable simple group
has a distinct ambient conjugate in that same Sylow subgroup. Otherwise it
is weakly closed, hence central in the Sylow. The actual Glauberman Z-star
theorem and the trivial odd core then make it central in the entire group.
The center of a nonsolvable simple group is trivial, a contradiction.

This is the global fusion input used at the start of Parrott's Tits
recognition argument (1972, p.672). It has no N2 hypothesis and does not
presuppose any local model or identification theorem.
-/

namespace Stellmacher.Recognition

open scoped IsMulCommutative

/-- Every simple-group involution has a distinct conjugate in its Sylow subgroup. -/
public theorem exists_distinct_isConj_in_sylow
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) (z : S) (hz : orderOf z = 2) :
    ∃ t : S, t ≠ z ∧ IsConj (z : G) (t : G) := by
  classical
  by_contra hnone
  have hfix (g : G) (hg : g * (z : G) * g⁻¹ ∈ (S : Subgroup G)) :
      g * (z : G) * g⁻¹ = z := by
    let t : S := ⟨g * (z : G) * g⁻¹, hg⟩
    have ht : t = z := by
      by_contra hne
      exact hnone ⟨t, hne, isConj_iff.mpr ⟨g, rfl⟩⟩
    exact congrArg Subtype.val ht
  have hcentral (s : G) (hs : s ∈ (S : Subgroup G)) : s * (z : G) = z * s := by
    have hconj := hfix s ((S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem hs z.property) ((S : Subgroup G).inv_mem hs))
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hzG : orderOf (z : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hz
  have hzI : BenderSuzuki.PFAppendixIII.IsInvolution (z : G) := by
    refine ⟨?_, ?_⟩
    · intro hone
      simp [hone] at hzG
    · simpa only [hzG] using pow_orderOf_eq_one (z : G)
  have hzcenter := Glauberman.ZStar.glauberman_zstar_corefree
    (simple_nonsolvable_inputs hns).2.2 S (z : G) hzI z.property hcentral
      ⟨z.property, hfix⟩
  have hcenter : Subgroup.center G = ⊥ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hbot | htop
    · exact hbot
    · let : IsMulCommutative G := Subgroup.center_eq_top_iff.mp htop
      exact (hns inferInstance).elim
  have hzone : (z : G) = 1 := by simpa [hcenter] using hzcenter
  exact hzI.ne_one hzone

end Stellmacher.Recognition
