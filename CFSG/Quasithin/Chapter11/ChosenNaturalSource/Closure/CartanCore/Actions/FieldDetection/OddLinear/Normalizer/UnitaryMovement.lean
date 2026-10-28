module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.Unitary
public import Theory.GroupTheory.OddElementLift
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Unitary Borel movement from the original Cartan actor

The cubic projective torus kernel meets the odd-degree subfield trivially,
since that subfield's multiplicative order is prime to three. A nontrivial
odd field actor remains nontrivial on this subfield. Its torus coefficients
have simultaneous lifts in the original Sylow normalizer. Taking an odd
power of a lift preserves its image and gives the literal BorelMovement.

Source: Aschbacher--Smith 11.5.6(3), pp.780--781. This provides a direct
Borel route for the surviving unitary row; it does not discard that row.
-/

public section
open Subgroup Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BorelTorus BorelCoprimeFieldAction
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.Unitary
variable {F : BinaryField} {J : HermitianForm 3 F.Carrier}
variable {hJ : J.form = !![0,0,1;0,1,0;1,0,0]}

/-- The cubic projective kernel disappears on the constructed odd subfield. -/
theorem odd_torus_injective : Function.Injective
    ((hermitianTorusPSU J hJ).comp (Units.map (oddInclusion F).toMonoidHom)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro u hu
  have hcube := ((projective_eq_one_iff J hJ _).mp hu).2
  have hcube' : u ^ 3 = 1 := by
    apply Units.ext
    apply (oddInclusion F).injective
    exact congrArg Units.val hcube
  have hcop : Nat.Coprime (Nat.card (oddField F).Carrierˣ) 3 := by
    rw [Nat.card_units,(oddField F).card_eq]
    exact (Nat.BinaryTorusParity.coprime_three_sub_one (oddSubfield_degree_odd F)).symm
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_natCard u) (orderOf_dvd_of_pow_eq_one hcube'))

namespace Coordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I : Subgroup G}
variable (c : Coordinates T I F J hJ)
variable {L V : Subgroup G} {D : ChosenModule T L V} {E : Geometry D}

include c in
/-- The actual unitary component actor moves an odd-order original-Sylow
normalizer lift; no field actor or lifting callback is assumed. -/
theorem borel_movement
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2 ≤ n) (hcF : Nat.card F.Carrier = (2 ^ n) ^ 2)
    (hconj : ∀ z, J.conj z = z ^ (2 ^ n))
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G)) (hIY : I ≤ E.Y)
    (x : normalizer (I : Set G)) (hxX : (x : G) ∈ E.X)
    (hxS : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G))
    (ho : Odd (Nat.card E.X)) (hthree : Nat.Coprime (Nat.card E.X) 3)
    (hc : Nat.Coprime (Nat.card E.X) (Nat.card I))
    (hne : coreQuotientAction I x ≠ 1) : E.BorelMovement := by
  have hα : c.actor x ≠ 1 := by
    intro h
    exact hne ((MulAut.congr c.model).injective (h.trans (map_one _).symm))
  have hd : orderOf (c.actor x) ∣ Nat.card E.X := by
    apply ((orderOf_map_dvd (MulAut.congr c.model).toMonoidHom _).trans
      (orderOf_map_dvd (coreQuotientAction I) x)).trans
    rw [← Subgroup.orderOf_coe x]
    exact E.X.orderOf_dvd_natCard hxX
  have hcop : Nat.Coprime (orderOf (c.actor x))
      (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    hc.of_dvd hd (card_dvd_of_surjective c.quotient c.quotient_surjective)
  obtain ⟨σ,hσ,hdσ,he⟩ := exists_nontrivial_coefficient J hJ hn hcF hconj
    (c.actor x) hα (hthree.of_dvd_left hd) hcop (c.actor_preserves_root x hxS)
  have hσodd : Odd (orderOf σ) := ho.of_dvd_nat (hdσ.trans hd)
  have hne' := oddRestriction_ne_one F σ hσodd hσ
  have hunits : Odd (Nat.card F.Carrierˣ) := by
    rw [Nat.card_units,F.card_eq]
    have hpow : Even (2 ^ F.degree) :=
      (show Even (2 : ℕ) from ⟨1,rfl⟩).pow_of_ne_zero F.degree_pos.ne'
    exact (Nat.odd_sub' (pow_pos (by decide : 0 < 2) _)).mpr (by simpa using hpow)
  by_contra hmove
  apply hne'
  have hfix (u : (oddField F).Carrierˣ) :
      Units.map (oddRestriction F σ).toMonoidHom u = u := by
    obtain ⟨b,hbN,hbu⟩ := c.odd_torus_lifts hn hcF hconj hTI u
    have hbo : Odd (orderOf (c.quotient b)) := by
      rw [hbu]
      exact hunits.of_dvd_nat ((orderOf_map_dvd (hermitianTorusPSU J hJ) _).trans
        (orderOf_dvd_natCard _))
    obtain ⟨r,hr,hro,hre⟩ := c.quotient.exists_odd_power_with_image b hbo
    have hrN : (r : G) ∈ normalizer (T : Set G) := by
      obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp hr
      exact (normalizer (T : Set G)).zpow_mem hbN k
    let B : Subgroup G := zpowers (r : G)
    have hBY : B ≤ E.Y := zpowers_le.mpr (hIY r.property)
    have hBN : B ≤ normalizer (T : Set G) := zpowers_le.mpr hrN
    have hBo : Odd (Nat.card B) := by
      rw [Nat.card_zpowers,Subgroup.orderOf_coe r]
      exact hro
    have hcomm : ⁅E.X,B⁆ ≤ (T : Subgroup G) := by
      by_contra hn
      exact hmove ⟨B,hBY,hBN,hBo,hn⟩
    let d : I := I.normalizerMonoidHom x r * r⁻¹
    have hdT : d ∈ (T : Subgroup G).subgroupOf I :=
      hcomm (commutator_mem_commutator hxX (mem_zpowers (r : G)))
    have hdq : c.actor x (c.quotient r) * (c.quotient r)⁻¹ ∈ projectiveRoot J hJ := by
      have hh := mem_map_of_mem c.quotient hdT
      rw [c.quotient_sylow_image] at hh
      change c.quotient (I.normalizerMonoidHom x r * r⁻¹) ∈ _ at hh
      rwa [map_mul,map_inv,← c.actor_quotient] at hh
    rw [hre,hbu] at hdq
    have ht := (he _).mp hdq
    apply odd_torus_injective (J := J) (hJ := hJ)
    change hermitianTorusPSU J hJ
      (Units.map (oddInclusion F).toMonoidHom
        (Units.map (oddRestriction F σ).toMonoidHom u)) = _
    have hunit : Units.map (oddInclusion F).toMonoidHom
        (Units.map (oddRestriction F σ).toMonoidHom u) =
        Units.map σ.toMonoidHom (Units.map (oddInclusion F).toMonoidHom u) := by
      apply Units.ext
      exact oddRestriction_apply F σ u.val
    rw [hunit]
    exact ht
  ext z
  by_cases hz : z = 0
  · simp [hz]
  · exact congrArg Units.val (hfix (Units.mk0 z hz))
end Coordinates
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.Unitary
