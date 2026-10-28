module

public import Theory.SpecificGroups.ReeF4.DerivedCarrier
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The ambient group in the positive-parameter Ree case

Let L = F*(G), G = LT with T Sylow two, and suppose L is isomorphic to
the derived Ree group at a positive parameter. The derived-carrier bridge
identifies L with the full fixed-point group. Each element of T induces a
two-power automorphism of L, hence an inner automorphism by the concrete
Ree calculation. After an inner correction that element centralizes F*(G),
so belongs to F*(G). Thus T ≤ L and G = L.

This discharges the outer-extension issue for q > 2 in E.1.14(1), printed
p.214 of `refs/quasithin.pdf`. It does not apply this reduction at q = 2:
the Tits group has a genuine full Ree extension. Even order below uses the
derived carrier at every parameter and applies also to that extension.
-/

public section
noncomputable section

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour

open Subgroup Theory.GroupTheory
open ReeF4 ReeF4.DerivedCarrier ReeF4.Parabolics

variable {G : Type*} [Group G]

/-- An actual embedded derived Ree group makes the ambient order even. -/
theorem even_card_of_subgroup_derived_equiv (L : Subgroup G) {m : ℕ}
    (e : L ≃* commutator (Model m)) : Even (Nat.card G) := by
  apply even_iff_two_dvd.mpr
  apply dvd_trans _ L.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv]
  exact even_iff_two_dvd.mp (derived_even_card m)

variable [Finite G]

/-- For q > 2, the source supplement G = LT has no extra two-extension.
Simplicity and SQTK are not needed for this reduction. -/
theorem positive_generalizedFitting_eq_top (T : Sylow 2 G)
    (L : Subgroup G) (hL : L = generalizedFitting G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ} (hm : 0 < m)
    (e : L ≃* commutator (Model m)) : L = ⊤ := by
  let : L.Normal := hL ▸ inferInstance
  let eL := e.trans (derivedEquiv hm)
  have hcent : centralizer (L : Set G) ≤ L := by
    simpa only [hL] using centralizer_generalizedFitting_le G
  have hTL : (T : Subgroup G) ≤ L := by
    intro t ht
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨t, ht⟩
    have htpow : t ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    let a : G →* MulAut (Model m) :=
      (MulAut.congr eL).toMonoidHom.comp (MulAut.conjNormal (H := L))
    have hapow : a t ^ (2 ^ n) = 1 := by rw [← map_pow, htpow, map_one]
    obtain ⟨x, hx⟩ := OuterLocal.LargeAutomorphisms.inner_of_twoPower hm (a t) n hapow
    let l : L := eL.symm x
    have hl : MulAut.conj l = MulAut.conjNormal t := by
      apply (MulAut.congr eL).injective
      change (MulAut.congr eL) (MulAut.conj l) = a t
      rw [← hx]
      ext y
      simp [MulAut.congr, MulAut.conj_apply, l]
    have hk : MulAut.conjNormal ((l : G)⁻¹ * t) = (1 : MulAut L) := by
      rw [map_mul, map_inv, MulAut.conjNormal_val, hl, inv_mul_cancel]
    have hc : (l : G)⁻¹ * t ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro z hz
      have he := congrArg (fun b : MulAut L => ((b ⟨z, hz⟩ : L) : G)) hk
      change ((l : G)⁻¹ * t) * z * ((l : G)⁻¹ * t)⁻¹ = z at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    simpa using L.mul_mem l.property (hcent hc)
  rw [sup_eq_left.mpr hTL] at hgen
  exact hgen

/-- A concrete equivalence for transporting the model calculation to the
whole source group, with the outer two-extension discharged. -/
def positiveAmbientEquiv (T : Sylow 2 G)
    (L : Subgroup G) (hL : L = generalizedFitting G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ} (hm : 0 < m)
    (e : L ≃* commutator (Model m)) : G ≃* Model m :=
  Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr
      (positive_generalizedFitting_eq_top T L hL hgen hm e).symm).trans
      (e.trans (derivedEquiv hm)))

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour
