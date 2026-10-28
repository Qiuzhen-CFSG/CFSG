module

public import Stellmacher.OmegaOneCenterMap

/-!
# Elementary omega-center normal closures

Let `Q ≤ S` be a subgroup contained in `H` and normal there. If
`Ω₁(Z(S)) ≤ Q`, then its normal closure inside `H` lies in
`Ω₁(Z(Q))` (viewed internally in `H`) and is therefore elementary
abelian of exponent two.

The essential point is that `Ω₁(Z(S))` centralizes `Q` and consists of
involutions. Thus it lies in the omega-one center of the normal subgroup `Q`.
That omega-one center is characteristic in `Q`, hence normal in `H`, so it
contains the full normal closure. Restricting its elementary-abelian structure
gives the principal conclusion.

This is the normal-container step for `V = ⟨Ω₁(Z(S))^H⟩` in the
opening paragraph of Stellmacher (3.9), Journal of Algebra 190 (1997), p. 23,
as transcribed in `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

universe u

/-- The omega-center of a normal container contains the internal normal
closure of the omega-center of the larger 2-subgroup. -/
public theorem omegaOneCenter_normalClosure_le_containerOmega
    {G : Type u} [Group G]
    (S H Q : Subgroup G) (_hQH : Q ≤ H) (hQS : Q ≤ S)
    (hQnormal : (Q.subgroupOf H).Normal)
    (hOmega : omegaOneCenterAmbient S ≤ Q) :
    Subgroup.normalClosure
        ((omegaOneCenterAmbient S).subgroupOf H : Set H) ≤
      omegaOneCenterAmbient (Q.subgroupOf H) := by
  let QH : Subgroup H := Q.subgroupOf H
  let ZQ : Subgroup QH := Subgroup.center QH
  let W : Subgroup ZQ := omega₁ (G := ZQ) (p := 2)
  let E : Subgroup QH := W.map ZQ.subtype
  let A : Subgroup H := E.map QH.subtype
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : QH.Normal := hQnormal
  let _ : ZQ.Characteristic := Subgroup.centerCharacteristic
  let _ : W.Characteristic := by
    dsimp [W]
    exact omega₁_characteristic ZQ
  let _ : E.Characteristic := by
    dsimp [E]
    exact Subgroup.characteristic_of_characteristic_of_characteristic
  let _ : A.Normal := by
    dsimp [A]
    exact ConjAct.normal_of_characteristic_of_normal
  have hZA : (omegaOneCenterAmbient S).subgroupOf H ≤ A := by
    intro z hz
    have hzG : (z : G) ∈ omegaOneCenterAmbient S :=
      Subgroup.mem_subgroupOf.mp hz
    obtain ⟨_hzS, hzpow, hzcent⟩ :=
      (mem_omegaOneCenterAmbient_iff S (z : G)).mp hzG
    have hzQ : (z : G) ∈ Q := hOmega hzG
    have hzA : z ∈ omegaOneCenterAmbient QH := by
      apply (mem_omegaOneCenterAmbient_iff QH z).mpr
      refine ⟨hzQ, ?_, ?_⟩
      · apply H.subtype_injective
        simpa using hzpow
      · intro q hq
        apply H.subtype_injective
        exact hzcent (q : G) (hQS (Subgroup.mem_subgroupOf.mp hq))
    simpa [A, E, W, ZQ, QH, omegaOneCenterAmbient] using hzA
  have hclosure :
      Subgroup.normalClosure
          ((omegaOneCenterAmbient S).subgroupOf H : Set H) ≤ A :=
    Subgroup.normalClosure_le_normal hZA
  simpa [A, E, W, ZQ, QH, omegaOneCenterAmbient] using hclosure

/-- A normal subgroup `Q ≤ S` containing `Ω₁(Z(S))` also contains its
normal closure as an elementary abelian subgroup. -/
public theorem omegaOneCenter_normalClosure_isElementaryAbelian
    {G : Type u} [Group G]
    (S H Q : Subgroup G) (hQH : Q ≤ H) (hQS : Q ≤ S)
    (hQnormal : (Q.subgroupOf H).Normal)
    (hOmega : omegaOneCenterAmbient S ≤ Q) :
    IsElementaryAbelian 2
      (Subgroup.normalClosure
        ((omegaOneCenterAmbient S).subgroupOf H : Set H)) := by
  let V : Subgroup H := Subgroup.normalClosure
    ((omegaOneCenterAmbient S).subgroupOf H : Set H)
  let A : Subgroup H := omegaOneCenterAmbient (Q.subgroupOf H)
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAelem : IsElementaryAbelian 2 A :=
    omegaOneCenterAmbient_elementaryAbelian _
  let _ : IsElementaryAbelian 2 A := hAelem
  have hVA : V ≤ A :=
    omegaOneCenter_normalClosure_le_containerOmega
      S H Q hQH hQS hQnormal hOmega
  refine
    { toIsMulCommutative :=
        ⟨⟨fun x y ↦ Subtype.ext
          (show (x : H) * (y : H) = (y : H) * (x : H) from ?_)⟩⟩
      exponent_dvd_p := ?_ }
  · have hcomm := (IsMulCommutative.is_comm (M := A)).comm
        (⟨x, hVA x.property⟩ : A) (⟨y, hVA y.property⟩ : A)
    exact congrArg Subtype.val hcomm
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := A) (x : H) (hVA x.property)

end Stellmacher.SectionThree
