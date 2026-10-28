module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Levi
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.TorusDetection

/-!
# Relative normality and self-centralization of the linear Ree radical

Relative normality and factorization by the full Levi are unconditional and
hold without model simplicity. A parabolic element centralizing the radical
has a Levi factor acting trivially on the radical's abelianization: its action
equals conjugation by the inverse radical factor. Consequently faithful Levi
action on this abelianization proves self-centralization.

The concrete degree-one matrix calculation detects non-torus end-node Levi
elements. The odd-order action argument and fixed-root character calculation
detect nonidentity elements of the full fixed torus. Together they discharge
the faithful-action premise and prove that the centralizer of the specified
radical inside the full linear parabolic lies in the radical for `m ≥ 1`.
No simplicity or identification with the intrinsic two-core is assumed.

Source: GLS3, Theorem 2.6.5(d,e,g), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section

namespace ReeF4.SectionGeometry.LinearRadical

open LargeLocalSeeds Parabolics Subgroup
open scoped commutatorElement

private theorem levi_factor_actsTrivially (m : ℕ) (r l : Model m)
    (hr : r ∈ radical m .linear)
    (hc : ∀ q ∈ radical m .linear, (r * l) * q = q * (r * l)) :
    ActsTriviallyOnRadicalAbelianization m l := by
  intro q hq
  have he : l * q * l⁻¹ = r⁻¹ * q * r := by
    calc
      l * q * l⁻¹ = r⁻¹ * ((r * l) * q) * l⁻¹ := by group
      _ = r⁻¹ * (q * (r * l)) * l⁻¹ := by rw [hc q hq]
      _ = r⁻¹ * q * r := by group
  have hcomm : ⁅l, q⁆ = ⁅r⁻¹, q⁆ := by
    simp only [commutatorElement_def, inv_inv]
    rw [he]
  rw [hcomm]
  exact commutator_mem_commutator (inv_mem hr) hq

/-- Faithful action of the full Levi on the radical's abelianization gives
the required centralizer bound inside the full parabolic. -/
theorem centralizer_le_radical_of_faithful_fullLevi (m : ℕ)
    (hfaithful : ∀ l ∈ fullLevi m,
      ActsTriviallyOnRadicalAbelianization m l → l = 1) :
    centralizer ((radical m .linear).subgroupOf (parabolic m .linear) :
      Set (parabolic m .linear)) ≤ (radical m .linear).subgroupOf (parabolic m .linear) := by
  intro x hx
  obtain ⟨r, hr, l, hl, he⟩ := exists_radical_fullLevi_factors m x.val x.property
  have hc : ∀ q ∈ radical m .linear, (r * l) * q = q * (r * l) := by
    intro q hq
    have h := mem_centralizer_iff.mp hx
      (⟨q, radical_le_parabolic m .linear hq⟩ : parabolic m .linear) hq
    have hval := congrArg Subtype.val h
    change q * x.val = x.val * q at hval
    simpa only [he] using hval.symm
  have hl1 := hfaithful l hl (levi_factor_actsTrivially m r l hr hc)
  have hxval : x.val = r := by simpa only [hl1, mul_one] using he.symm
  change x.val ∈ radical m .linear
  rwa [hxval]

/-- End-node detection and full fixed-torus character separation are independent
inputs. Both must be proved before asserting unconditional self-centralization. -/
theorem centralizer_le_radical_of_levi_and_torus_detection (m : ℕ)
    (hlevi : ∀ l ∈ fullLevi m,
      ActsTriviallyOnRadicalAbelianization m l → l ∈ fixedTorus m)
    (htorus : ∀ t ∈ fixedTorus m,
      ActsTriviallyOnRadicalAbelianization m t → t = 1) :
    centralizer ((radical m .linear).subgroupOf (parabolic m .linear) :
      Set (parabolic m .linear)) ≤ (radical m .linear).subgroupOf (parabolic m .linear) := by
  apply centralizer_le_radical_of_faithful_fullLevi m
  intro l hl hact
  exact htorus l (hlevi l hl hact) hact

/-- The specified linear root radical contains its centralizer inside the full
parabolic, including the complementary torus, without model simplicity. -/
theorem centralizer_le_radical (m : ℕ) (hm : 1 ≤ m) :
    centralizer ((radical m .linear).subgroupOf (parabolic m .linear) :
      Set (parabolic m .linear)) ≤ (radical m .linear).subgroupOf (parabolic m .linear) :=
  centralizer_le_radical_of_levi_and_torus_detection m
    (fullLevi_mem_fixedTorus_of_trivial_radical_abelianization m hm)
    (fixedTorus_eq_one_of_trivial_radical_abelianization m hm)

end ReeF4.SectionGeometry.LinearRadical
