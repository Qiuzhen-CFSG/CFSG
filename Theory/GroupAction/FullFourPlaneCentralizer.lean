module
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Centralizing a full symmetric-three action on a four-plane

An elementary abelian group of order four has exactly six automorphisms.
Thus an S3 quotient acting faithfully on it is its full automorphism group.
Any actor whose commutators with that S3 action fix the plane acts through
the center of S3, and fixes the plane itself.

The source application is the full hatted-kernel comparison in
Aschbacher--Smith 14.3.25, printed p.1001. Only the plane is assumed normal;
all centralizers and commutators refer to the actual ambient inclusions.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An actor commuting with the full S3 action modulo the plane centralizer
already centralizes the original four-plane. -/
theorem centralizes_four_plane_of_commuting_symmetricThree
    (D K N : Subgroup G) [D.Normal] [IsElementaryAbelian 2 D]
    (hD : Nat.card D = 4)
    (model : Nonempty ((K ⧸ (centralizer (D : Set G)).comap K.subtype) ≃*
      Equiv.Perm (Fin 3)))
    (hc : ⁅N,K⁆ ≤ centralizer (D : Set G)) : N ≤ centralizer (D : Set G) := by
  let : Nontrivial D := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hD]; decide)
  let : IsKleinFour D := ⟨hD,IsElementaryAbelian.exponent_eq_prime⟩
  let ρ : G →* MulAut D := MulAut.conjNormal
  have hρ : ρ.ker = centralizer (D : Set G) := by
    ext k
    constructor
    · intro hk z hz
      have hh := congrArg (fun a : MulAut D => (a ⟨z,hz⟩ : G)) hk
      change k * z * k⁻¹ = z at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hk
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      change k * (z:G) * k⁻¹ = (z:G)
      rw [←hk z z.property,mul_inv_cancel_right]
  let f := ρ.comp K.subtype
  have hk : f.ker = (centralizer (D : Set G)).comap K.subtype := by
    change ρ.ker.comap K.subtype = _
    rw [hρ]
  obtain ⟨e₀⟩ := model
  let e : f.range ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans e₀)
  have hrange : f.range = ⊤ := by
    apply eq_top_of_card_eq
    rw [Nat.card_congr e.toEquiv,IsKleinFour.card_mulAut]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have honto : Function.Surjective f := MonoidHom.range_eq_top.mp hrange
  let b : MulAut D ≃* Equiv.Perm (Fin 3) :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hrange).symm.trans e)
  have hcenter : center (Equiv.Perm (Fin 3)) = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    decide +kernel
  intro n hn
  rw [←hρ]
  apply b.injective
  change b (ρ n) = b 1
  rw [map_one]
  apply hcenter.le
  rw [mem_center_iff]
  intro a
  obtain ⟨k,hk⟩ := honto (b.symm a)
  have hnk : ⁅ρ n,f k⁆ = 1 := by
    change ⁅ρ n,ρ (k:G)⁆ = 1
    rw [←map_commutatorElement]
    exact (hρ.ge (hc (commutator_mem_commutator hn k.property)))
  have hh := congrArg b (commutatorElement_eq_one_iff_mul_comm.mp hnk).symm
  simpa only [map_mul,hk,MulEquiv.apply_symm_apply] using hh
end Subgroup
