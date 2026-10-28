module
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.GroupTheory.PGroup.AbelianOmega
public import Theory.GroupTheory.QuotientIntersection
/-!
# Elementary actors above an SL₂ residual and an abelian radical

An abelian two-subgroup of odd-characteristic SL₂ is cyclic, since its first
omega subgroup has order at most two. If an elementary subgroup lies in the
product of an SL₂ subgroup and a commuting abelian two-group R, intersecting
SL₂ with AR therefore gives a cyclic subgroup with the same image modulo R.
The elementary image has order at most two.

For a group whose solvable and two-residuals coincide with SL₂, the residual
centralizes the radical by component calculus. Thus an elementary image of
order four lies outside the simple socle of the radical quotient, provided
the radical is abelian. No model-specific radical calculation is assumed
implicitly; it remains an explicit premise for the application.

Source: elementary quasisimple group theory; the intended application is
Aschbacher--Smith A.3.21(a), p.55, and E.1.14(7), p.214.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.SL2.AbelianRadicalActors
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

private theorem cyclic_abelian_two_subgroup (hchar : (2 : F) ≠ 0)
    (D : Subgroup H) (e : D ≃* SL(2,F)) (B : Subgroup H)
    [IsMulCommutative B] (hB : IsPGroup 2 B) (hBD : B ≤ D) : IsCyclic B := by
  apply hB.isCyclic_of_card_omega_one_le_two
  let O := omega₁ B (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative B
  let f : B →* SL(2,F) := e.toMonoidHom.comp (inclusion hBD)
  have hf : Function.Injective f := e.injective.comp (inclusion_injective hBD)
  let : IsElementaryAbelian 2 (O.map f) := IsElementaryAbelian.map f
  have hc := (primeRank_le_iff_elementary_card_le SL(2,F)).mp
    (Matrix.SpecialLinearGroup.primeRank_two_eq_one hchar).le (O.map f) inferInstance
  rw [card_map_of_injective hf] at hc
  exact hc

/-- An elementary subgroup of the product with an abelian radical has image
of order at most two in the literal radical quotient. -/
theorem image_card_le_two (hchar : (2 : F) ≠ 0)
    (D R : Subgroup H) [R.Normal] [IsMulCommutative R]
    (e : D ≃* SL(2,F)) (hR : IsPGroup 2 R)
    (hDR : D ≤ centralizer (R : Set H)) (A : Subgroup H)
    [IsElementaryAbelian 2 A] (hA : A ≤ D ⊔ R) :
    Nat.card (A.map (QuotientGroup.mk' R)) ≤ 2 := by
  let q := QuotientGroup.mk' R
  have hAR : A ≤ centralizer (R : Set H) := hA.trans (sup_le hDR R.le_centralizer)
  let : IsMulCommutative (A ⊔ R : Subgroup H) := by
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact le_centralizer_iff.mpr (sup_le A.le_centralizer (le_centralizer_iff.mp hAR))
    · exact le_centralizer_iff.mpr (sup_le hAR R.le_centralizer)
  let B := D ⊓ (A ⊔ R)
  let : IsMulCommutative B := le_centralizer_iff_isMulCommutative.mp
    (show B ≤ centralizer (B : Set H) from
      inf_le_right.trans ((A ⊔ R).le_centralizer.trans (centralizer_le inf_le_right)))
  have hB : IsPGroup 2 B :=
    ((IsElementaryAbelian.isPGroup 2 A).to_sup_of_normal_right hR).to_le inf_le_right
  let : IsCyclic B := cyclic_abelian_two_subgroup hchar D e B hB inf_le_left
  have hRq : R.map q = ⊥ := QuotientGroup.map_mk'_self R
  have hAq : A.map q ≤ D.map q := by
    have h := map_mono (f := q) hA
    rwa [Subgroup.map_sup, hRq, sup_bot_eq] at h
  have hBq : B.map q = A.map q := by
    rw [map_inf_of_ker_le q D (A ⊔ R) (by rw [QuotientGroup.ker_mk']; exact le_sup_right),
      Subgroup.map_sup, hRq, sup_bot_eq, inf_eq_right.mpr hAq]
  let : IsCyclic (B.map q) := isCyclic_of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B)
  let : IsCyclic (A.map q) := hBq ▸ inferInstance
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hd := IsElementaryAbelian.exponent_dvd_p 2 (A.map q)
  rw [IsCyclic.exponent_eq_card] at hd
  exact Nat.le_of_dvd (by decide) hd

/-- A four-group image cannot lie in the simple socle when the SL₂ residual
centralizes an abelian radical. The radical commutativity premise is explicit. -/
theorem actor_not_le_socle (hodd : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (e : solvableResidual H ≃* SL(2,F))
    (hres : pResidual 2 H = solvableResidual H)
    [IsMulCommutative (solvableRadical H)]
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hcard : Nat.card (A.map (QuotientGroup.mk' (solvableRadical H))) = 4) :
    ¬ A.map (QuotientGroup.mk' (solvableRadical H)) ≤
      generalizedFitting (H ⧸ solvableRadical H) := by
  let D := solvableResidual H
  let : IsQuasisimple D := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hlarge e
  let : IsSimpleGroup (D ⧸ solvableRadical D) := quasisimple_radicalQuotient_isSimple D
  let : Group.IsPerfect (D ⧸ solvableRadical D) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : Nontrivial D := (QuotientGroup.mk'_surjective (solvableRadical D)).nontrivial
  have hq : IsPGroup 2 (H ⧸ D) :=
    (isPGroup_quotient_pResidual (G := H) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hres)
  have hsoc := generalizedFitting_radical_quotient_eq_image D
    (Group.IsPerfect.not_isMulCommutative _) hq
  have hcomp : IsComponent H D := ⟨(inferInstance : D.Normal).isSubnormal, inferInstance⟩
  have hDR : D ≤ centralizer (solvableRadical H : Set H) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rcases hcomp.normal_dichotomy (solvableRadical H) with hle | hc
    · let : Group.IsSolvable D :=
        Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
      exact (Group.IsPerfect.not_isSolvable D inferInstance).elim
    · exact hc
  intro hA
  rw [hsoc, map_le_iff_le_comap, comap_map_eq, QuotientGroup.ker_mk'] at hA
  have hR := (Theory.SpecificGroups.SL2.ResidualTwoExtension.radical_quotient_structure
    hodd hlarge e hres).1
  have hc := image_card_le_two (GorensteinWalter.two_ne_zero_of_odd_card F hodd)
    D (solvableRadical H) e hR hDR A hA
  omega


end Theory.SpecificGroups.SL2.AbelianRadicalActors
