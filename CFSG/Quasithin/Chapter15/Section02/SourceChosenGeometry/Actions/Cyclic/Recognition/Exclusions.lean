module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Recognition.Cubic
public import Theory.Representation.SmallBinaryFifteenCentralizer

/-!
# Excluding the cyclic-fifteen Fitting row

A source offender image generates an order-two subgroup whose centralizer
has order prime to three. The faithful binary four-space obstruction for a
normal cyclic fifteen therefore excludes that Fitting row. Both steps use
the literal chosen action, with no recognition premise.

Source: Aschbacher--Smith 15.2.13, printed pp.1111--1112, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The centralizer of an offender-image generator has order prime to three. -/
theorem Preceding.not_three_dvd_centralizer {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H)
    (t : internalActionImage M V h.prepared.normalized)
    (ht : zpowers t = actor M V B h.prepared.normalized) :
    ¬ 3 ∣ Nat.card (centralizer ({t} : Set _)) := by
  intro hdiv
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({t} : Set _)) 3 hdiv
  have hco : orderOf (c : internalActionImage M V h.prepared.normalized) = 3 :=
    (orderOf_coe c).trans hc
  have hp : IsPGroup 3 (zpowers (c : internalActionImage M V h.prepared.normalized)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hco]; rfl)
  have hC : zpowers (c : internalActionImage M V h.prepared.normalized) ≤
      centralizer (actor M V B h.prepared.normalized : Set _) := by
    apply zpowers_le.mpr
    rw [←ht]
    intro y hy
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hy
    have he : Commute (c : internalActionImage M V h.prepared.normalized) t :=
      mem_centralizer_singleton_iff.mp c.property
    exact (he.zpow_right n).symm.eq
  have hz := d.three_centralizer_eq_bot hB _ hp hC
  have hc1 : (c : internalActionImage M V h.prepared.normalized) = 1 :=
    mem_bot.mp (show (c : internalActionImage M V h.prepared.normalized) ∈ (⊥ : Subgroup _) from
      hz ▸ mem_zpowers _)
  rw [hc1,orderOf_one] at hco
  contradiction

/-- The normal cyclic-fifteen Fitting row is excluded on the actual action. -/
theorem Preceding.not_fitting_fifteen {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) :
    ¬ Nonempty (fittingSubgroup (internalActionImage M V h.prepared.normalized) ≃*
      Multiplicative (ZMod 15)) := by
  let := h.prepared.elementary
  intro he
  obtain ⟨B,hB⟩ := d.nonempty
  let A := actor M V B h.prepared.normalized
  have hAc := (quadratic_fixed_eq_moved h A (d.planes B hB).1 (d.planes B hB).2.1).1
  let : IsCyclic A := isCyclic_of_prime_card hAc
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hto : orderOf t = 2 := by
    rw [←Nat.card_zpowers,ht,hAc]
  exact d.not_three_dvd_centralizer hB t ht
    (SmallBinaryFiveOvergroup.three_dvd_involution_centralizer_of_normal_fifteen
      (imageRepresentation M V h.prepared.normalized) (imageRepresentation_injective _ _ _)
      h.finrank_eq_four _ he t (hto ▸ pow_orderOf_eq_one t)
      (by intro he; rw [he,orderOf_one] at hto; contradiction))
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
