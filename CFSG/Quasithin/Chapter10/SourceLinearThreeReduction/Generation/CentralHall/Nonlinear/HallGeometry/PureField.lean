module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FieldComplement
public import Theory.SpecificGroups.SL2.SylowTorusComplement

/-!
# A pure field complement for the original central Hall subgroup

The original Hall coefficient kernel is B_H ∩ L₀ and has faithful pair
of diagonal characters. The proved ambient prime-rank bound splits this
kernel inside the same B_H, with complement order coprime to |L/O₂(L)|.
Restrict the actual pair action to that complement and apply coprime
cocycle averaging. One diagonal pair simultaneously removes all diagonal
twists. The conclusion retains the original component inclusion, Sylow
marking, kernel characters, and the precise common conjugator.

This proves the binary-linear field-complement step of 10.2.3 with no
additional callback. The complement still has to be eliminated using the
actual module and Ω₁Z(T). That argument, the three row calculations, and
module recognition remain with qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith 10.2.3, printed p.745, using 10.1.3 on p.742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Matrix.SpecialLinearGroup BenderSuzuki.ZD.Linear
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

/-- The original Hall group is the product of its orbit intersection and an
actual complement inducing pure field automorphisms after one diagonal change
of coordinates. Both factors use the same original component and Sylow marking. -/
theorem exists_hall_pure_field_complement
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ (e' : (L ⧸ pCore 2 L) ≃* SL(2,F))
      (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
      (φ : B →* ((F ≃+* F) × (F ≃+* F)))
      (χ : φ.ker →* Fˣ × Fˣ) (E : Subgroup B) (u : Fˣ × Fˣ),
      (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩) =
          (e' (QuotientGroup.mk' (pCore 2 L) l),1)) ∧
      ((T : Subgroup G).subgroupOf (localOrbit T L)).map
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
          (upperUnipotent F).prod (upperUnipotent F) ∧
      φ.ker = (localOrbit T L).comap (H.subtype.comp B.subtype) ∧
      Function.Injective χ ∧
      Monoid.exponent φ.ker ∣ Nat.card F - 1 ∧
      φ.ker.IsComplement' E ∧
      Function.Bijective (φ.rangeRestrict.comp E.subtype) ∧
      Nat.Coprime (Nat.card E) (Nat.card (L ⧸ pCore 2 L)) ∧
      (∀ (b : φ.ker) (x : localOrbit T L ⧸ pCore 2 (localOrbit T L)),
        q (action D B c.hall_le b x) =
          (splitDiagonalHom (χ b).1,splitDiagonalHom (χ b).2) * q x *
            (splitDiagonalHom (χ b).1,splitDiagonalHom (χ b).2)⁻¹) ∧
      ∀ b : E, MulAut.congr q (action D B c.hall_le b) =
        splitDiagonalPairAction u * pairFieldAction (φ b) * (splitDiagonalPairAction u)⁻¹ := by
  obtain ⟨e',q,φ,χ,hcomp,hS,_ho,hk,hχ,hexp,hact,hd⟩ :=
    exists_hall_field_kernel_coordinates D c e
  obtain ⟨E,hE,hbij,hcop⟩ := exists_hall_field_complement D c e' φ hk χ hχ
  let ρ := ((MulAut.congr q).toMonoidHom.comp (action D B c.hall_le)).comp E.subtype
  let ψ := φ.comp E.subtype
  have hunit : Nat.card Fˣ ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e'.toEquiv]
    exact card_dvd_of_injective (splitDiagonalHom (F := F)) splitDiagonalHom_injective
  obtain ⟨u,hu⟩ := exists_pair_diagonal_field_straightening ρ ψ (by
    intro b
    simpa only [ρ,ψ,MonoidHom.comp_apply,Subgroup.subtype_apply,MulEquiv.coe_toMonoidHom,splitDiagonalHom_apply] using hd b) (hcop.coprime_dvd_right hunit)
  refine ⟨e',q,φ,χ,E,u,hcomp,hS,hk,hχ,hexp,hE,hbij,hcop,?_,?_⟩
  · simpa only [splitDiagonalHom_apply] using hact
  · simpa only [ρ,ψ,MonoidHom.comp_apply,Subgroup.subtype_apply,MulEquiv.coe_toMonoidHom] using hu
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
