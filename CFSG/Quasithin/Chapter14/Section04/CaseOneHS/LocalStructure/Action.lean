module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Contracts

/-!
# Natural coordinates for the literal HS local action

The coordinates identify H/O₂(H) with SL₂(4) extended by field Frobenius
and intertwine its action on U/Z(U) with the actual binary F₄² model.
Because this model is a subgroup of linear automorphisms, the intertwining
identity proves that the action kernel is exactly O₂(H). It also computes
the quotient order without a finite enumeration of the ambient group.

`ActionStructure` specifies the outstanding output of 14.3.32: these
coordinates, the cyclic-four center, and the original component and its
action on the tilded module. It assumes neither quaternion factors nor an
action-kernel equality. The companion LocalStructure assembly constructs
those conclusions. The specification itself does not prove 14.3.32.

Source: Aschbacher--Smith, 14.3.32, printed pp.1003--1004. The coordinates
use the concrete semilinear model in Theory/Representation/SL2FourNaturalOrbits.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Equivariance for the original quotient map and original conjugation action. -/
def NaturalCoordinates (F : InvariantFlag T V 3) : Prop :=
  ∃ (e : (F.H ⧸ pCore 2 F.H) ≃*
        Representation.SL2FourNatural.SemilinearNormalizer.specialField)
    (c : F.Uhat ≃* Multiplicative Representation.SL2FourNatural.V),
    ∀ (h : F.H) (x : F.Uhat),
      (c (F.uhatAction h x)).toAdd =
        (e (QuotientGroup.mk' (pCore 2 F.H) h)).val (c x).toAdd

/-- Faithfulness of the concrete linear model computes the original kernel. -/
theorem NaturalCoordinates.kernel (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F) : F.uhatAction.ker = pCore 2 F.H := by
  obtain ⟨e, c, he⟩ := hc
  ext h
  change F.uhatAction h = 1 ↔ h ∈ pCore 2 F.H
  constructor
  · intro hk
    have hq : e (QuotientGroup.mk' (pCore 2 F.H) h) = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      obtain ⟨x, hx⟩ := c.surjective (Multiplicative.ofAdd v)
      have hv := he h x
      rw [hk] at hv
      change (c x).toAdd = _ at hv
      rw [hx] at hv
      exact hv.symm
    apply (QuotientGroup.eq_one_iff (N := pCore 2 F.H) (x := h)).mp
    apply e.injective
    simpa only [QuotientGroup.mk'_apply, map_one] using hq
  · intro hp
    have hq : QuotientGroup.mk' (pCore 2 F.H) h = 1 :=
      (QuotientGroup.eq_one_iff (N := pCore 2 F.H) (x := h)).mpr hp
    apply MulEquiv.ext
    intro x
    apply c.injective
    have hv := he h x
    rw [hq, map_one] at hv
    exact congrArg Multiplicative.ofAdd hv

/-- The actual central quotient has sixteen elements. -/
theorem NaturalCoordinates.card_uhat (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F) : Nat.card F.Uhat = 16 := by
  obtain ⟨_, c, _⟩ := hc
  rw [Nat.card_congr c.toEquiv]
  change Nat.card Representation.SL2FourNatural.V = 16
  rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_vector]

/-- The remaining source action and component obligations, before constructing
the embedded quaternion factors. The source producer may take centerlessness
as an earlier premise; final assembly must discharge it. -/
structure ActionStructure (F : InvariantFlag T V 3) : Prop where
  natural : NaturalCoordinates F
  center_cyclic : IsCyclic (center F.U)
  center_card : Nat.card (center F.U) = 4
  component : ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
    F.H = K ⊔ (T : Subgroup G) ∧ F.U = ⁅K.pCoreIn 2, K⁆ ∧
    TildeIndecomposable F K
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
