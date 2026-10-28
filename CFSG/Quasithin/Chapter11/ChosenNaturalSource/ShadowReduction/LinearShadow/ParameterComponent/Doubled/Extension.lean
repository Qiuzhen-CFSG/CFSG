module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Orbit
public import Theory.Representation.SL2OrthogonalCover.Sylow

/-!
# The nonsplit displacement contradiction on the original omega orbit

Orthogonal coordinates on V_H retain its actual conjugation action and
separate the moved subgroup. A central trivial kernel is permitted. Distinct nonidentity elements of one rank-one Sylow have disjoint
displacement lines. Transporting those lines through the original coordinates
proves disjointness of the literal ambient commutator subgroups. Thus the two
equal nonzero commutator planes produced by the doubled SL₃ action are
impossible. Neither disjointness nor the contradiction is a marking field.

The marking itself and the reciprocal SL₃ calculation remain source inputs;
this file does not identify an arbitrary central extension with the full cover.
Source: Aschbacher--Smith, 11.3.6, printed pp.772--773, and I.2.3(1).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
open CommonCore
variable {G : Type*} [Group G] {T : Sylow 2 G} {H B : Subgroup G}
    {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Orthogonal coordinates separating the original moved subgroup.
A central trivial direct summand of V_H need not be removed in advance. -/
structure OrthogonalMarking (T : Sylow 2 G) (H B : Subgroup G) (F : Type*)
    [Field F] [Finite F] [CharP F 2] where
  le_local : B ≤ H
  parameter : B →* SL(2,F)
  coordinates : omegaClosure T H →* Multiplicative (SL2OrthogonalCover.Space F)
  kernel_disjoint : Disjoint coordinates.ker
    ((⁅B,omegaClosure T H⁆).subgroupOf (omegaClosure T H))
  intertwines : ∀ b w,
    (coordinates (localAction T H (inclusion le_local b) w)).toAdd =
      SL2OrthogonalCover.action (parameter b) (coordinates w).toAdd

namespace OrthogonalMarking
variable (c : OrthogonalMarking T H B F)

private def liftSpace (U : Submodule F (SL2OrthogonalCover.Space F)) : Subgroup G :=
  (U.toAddSubgroup.toSubgroup.comap c.coordinates).map
    (omegaClosure T H).subtype

private theorem mem_liftSpace (U : Submodule F (SL2OrthogonalCover.Space F))
    (w : omegaClosure T H) :
    (w : G) ∈ c.liftSpace U ↔ (c.coordinates w).toAdd ∈ U := by
  constructor
  · rintro ⟨v,hv,he⟩
    exact (Subtype.ext he : v = w) ▸ hv
  · exact fun hw => ⟨w,hw,rfl⟩

private def displacement (a : B) (w : omegaClosure T H) : omegaClosure T H :=
  localAction T H (inclusion c.le_local a) w * w⁻¹

private theorem displacement_coordinates (a : B) (w : omegaClosure T H) :
    (c.coordinates (c.displacement a w)).toAdd =
      SL2OrthogonalCover.action (c.parameter a) (c.coordinates w).toAdd -
        (c.coordinates w).toAdd := by
  simp only [displacement,map_mul,map_inv,toAdd_mul,toAdd_inv,c.intertwines,sub_eq_add_neg]

private theorem commutator_le_lift (a : B) (ha : (a : G) ^ 2 = 1) :
    ⁅zpowers (a : G),omegaClosure T H⁆ ≤
      c.liftSpace (SL2OrthogonalCover.movedSpace (c.parameter a)) := by
  apply commutator_le.mpr
  intro x hx w hw
  have hx' : x = 1 ∨ x = a := by
    obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp hx
    rw [zpow_eq_zpow_emod' k ha]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left; simp [hk]
    · right; simp [hk]
  rcases hx' with rfl | rfl
  · simp
  · apply (c.mem_liftSpace _ (c.displacement a ⟨w,hw⟩)).mpr
    refine ⟨(c.coordinates ⟨w,hw⟩).toAdd,?_⟩
    exact (c.displacement_coordinates a ⟨w,hw⟩).symm

/-- Distinct nonidentity Sylow images force disjoint actual commutators. -/
theorem commutators_disjoint (P : Sylow 2 SL(2,F)) (a b : B)
    (ha2 : (a : G) ^ 2 = 1) (hb2 : (b : G) ^ 2 = 1)
    (haP : c.parameter a ∈ P) (hbP : c.parameter b ∈ P)
    (ha1 : c.parameter a ≠ 1) (hb1 : c.parameter b ≠ 1)
    (hab : c.parameter a ≠ c.parameter b) :
    Disjoint ⁅zpowers (a : G),omegaClosure T H⁆
      ⁅zpowers (b : G),omegaClosure T H⁆ := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hxA := c.commutator_le_lift a ha2 hx.1
  have hxB := c.commutator_le_lift b hb2 hx.2
  have hxW : x ∈ omegaClosure T H := map_subtype_le _ hxA
  have he := Submodule.disjoint_def.mp
    (SL2OrthogonalCover.sylow_displacements_disjoint P
      (c.parameter a) (c.parameter b) haP hbP ha1 hb1 hab)
    (c.coordinates ⟨x,hxW⟩).toAdd
    ((c.mem_liftSpace _ ⟨x,hxW⟩).mp hxA)
    ((c.mem_liftSpace _ ⟨x,hxW⟩).mp hxB)
  have hxcomm : x ∈ ⁅B,omegaClosure T H⁆ :=
    (commutator_mono (zpowers_le.mpr a.property) le_rfl) hx.1
  have hxker : (⟨x,hxW⟩ : omegaClosure T H) ∈ c.coordinates.ker := he
  have hx1 := (disjoint_iff_inf_le.mp c.kernel_disjoint) ⟨hxker,hxcomm⟩
  exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hx1))

/-- The reciprocal doubled action cannot have equal nonzero commutator planes
inside a marked nonsplit rank-one cover. -/
theorem false_of_equal_commutators (P : Sylow 2 SL(2,F)) (a b : B)
    (ha2 : (a : G) ^ 2 = 1) (hb2 : (b : G) ^ 2 = 1)
    (haP : c.parameter a ∈ P) (hbP : c.parameter b ∈ P)
    (ha1 : c.parameter a ≠ 1) (hb1 : c.parameter b ≠ 1)
    (hab : c.parameter a ≠ c.parameter b)
    (he : ⁅zpowers (a : G),omegaClosure T H⁆ =
      ⁅zpowers (b : G),omegaClosure T H⁆)
    (hn : ⁅zpowers (a : G),omegaClosure T H⁆ ≠ ⊥) : False := by
  have hd := c.commutators_disjoint P a b ha2 hb2 haP hbP ha1 hb1 hab
  rw [← he,disjoint_self] at hd
  exact hn hd

end OrthogonalMarking

variable [Finite G] {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Application to the literal doubled conjugate and the original omega orbit.
Its elementarity is supplied by the faithful doubled coordinates. -/
theorem doubled_extension_contradiction
    (d : Coordinates D S) (g : G)
    (c : OrthogonalMarking T H ((fullModule L V).map (MulAut.conj g).toMonoidHom) F)
    (P : Sylow 2 SL(2,F))
    (a b : (fullModule L V).map (MulAut.conj g).toMonoidHom)
    (haP : c.parameter a ∈ P) (hbP : c.parameter b ∈ P)
    (ha1 : c.parameter a ≠ 1) (hb1 : c.parameter b ≠ 1)
    (hab : c.parameter a ≠ c.parameter b)
    (he : ⁅zpowers (a : G),omegaClosure T H⁆ =
      ⁅zpowers (b : G),omegaClosure T H⁆)
    (hn : ⁅zpowers (a : G),omegaClosure T H⁆ ≠ ⊥) : False := by
  let := fullModule_elementary d
  let : IsElementaryAbelian 2 ((fullModule L V).map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  exact c.false_of_equal_commutators P a b
    (elemPow_eq_one_of_isElementaryAbelian _ a.property)
    (elemPow_eq_one_of_isElementaryAbelian _ b.property)
    haP hbP ha1 hb1 hab he hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
