module

public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry

/-!
# Normalizers of nontrivial subgroups of a Suzuki root group

A nonidentity root element fixes precisely the point at infinity on the ovoid.
Consequently, an element normalizing a nontrivial subgroup of the root group
fixes infinity, and belongs to the standard Borel. The Borel is proper by its
order, and the root-group order also proves that the Suzuki group has even order.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.1 and XI.3.3.
This is the normalizer geometry used in the lower-bound argument for
Aschbacher--Smith E.1.14(1), printed p.214.
-/

public section
namespace BenderSuzuki.MatrixGroups

open Subgroup

/-- The positive-parameter Suzuki group has even order. -/
theorem suzukiMatrixGroup_even_card (m : ℕ) (hm : 0 < m) :
    Even (Nat.card (SuzukiMatrixGroup m)) := by
  apply even_iff_two_dvd.mpr
  apply dvd_trans _ (SuzukiRootSubgroup m).card_subgroup_dvd_card
  rw [suzukiRootSubgroup_card m hm]
  exact even_iff_two_dvd.mp
    ((even_two.pow_of_ne_zero (by omega : 2 * m + 1 ≠ 0)).pow_of_ne_zero (by decide))

/-- The standard Borel is a proper subgroup of the Suzuki group. -/
theorem suzukiBorelSubgroup_ne_top (m : ℕ) (hm : 0 < m) :
    SuzukiBorelSubgroup m ≠ ⊤ := by
  have hcard := (External.huppert_blackburn_XI_3_3 m hm
    (suzukiTits m) (suzukiTits_apply m)).2.2.2.2.2.2.1
  have hb := suzukiBorelSubgroup_card m hm
  intro h
  rw [h, Nat.card_congr (Subgroup.topEquiv).toEquiv] at hb
  rw [hcard] at hb
  have hq : 1 < 2 ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
  have hprod : 0 < (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) :=
    Nat.mul_pos (by positivity) (Nat.sub_pos_of_lt hq)
  nlinarith

/-- Every nontrivial subgroup of the root group has its normalizer in the Borel.
The subgroup need not be normal in the root group or elementary abelian. -/
theorem suzuki_normalizer_le_borel_of_le_root (m : ℕ) (hm : 0 < m)
    (A : Subgroup (SuzukiMatrixGroup m)) (hA : A ≠ ⊥)
    (hAF : A ≤ SuzukiRootSubgroup m) :
    normalizer (A : Set (SuzukiMatrixGroup m)) ≤ SuzukiBorelSubgroup m := by
  obtain ⟨r, hr⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have hrne : (r : SuzukiMatrixGroup m) ≠ 1 := fun h => hr (Subtype.ext h)
  intro g hg
  have hmem : g⁻¹ * (r : SuzukiMatrixGroup m) * g ∈ SuzukiRootSubgroup m :=
    hAF ((Subgroup.mem_normalizer_iff''.mp hg (r : SuzukiMatrixGroup m)).mp r.property)
  have hfix : (r : SuzukiMatrixGroup m) • (g • suzukiOvoidInfinity m) =
      g • suzukiOvoidInfinity m := by
    have h := suzukiRootSubgroup_fix_infinity m hm _ hmem
    have h' := congrArg (g • ·) h
    simpa only [mul_smul, smul_inv_smul] using h'
  rw [suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff]
  exact (suzukiRootSubgroup_fixed_iff m hm r (hAF r.property) hrne _).mp hfix

end BenderSuzuki.MatrixGroups
