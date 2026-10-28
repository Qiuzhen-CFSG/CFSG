module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Representation.SL3FourNaturalDual.CentralSections

/-!
# Concrete natural coordinates for the B.5.1 central section

A field of order four is identified with the actual field used by the binary
SL₃(4) natural module. Entrywise field transport gives both the group
isomorphism and an intertwining binary linear equivalence; the same marking
acts on every copy. The nontrivial central scalar has no fixed vector, so a
repeated-natural moved space is also its own central quotient.

These are coordinate constructions, conditional on the supplied natural-action
identification. Source: Aschbacher–Smith, B.5.1(1i–ii), printed pp.99–103,
referring to B.4.2(2), p.86, combined manuscript of 1 March 2004. The field
transport reuses the attributed ATLAS port imported below; no ATLAS source
is copied here.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.SL3FourNaturalDual
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Recognition

def fourFieldEquiv (E : BinaryField) (hE : Nat.card E.Carrier = 4) : E.Carrier ≃+* F := by
  let := Fintype.ofFinite E.Carrier
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, hE, SL2FourNatural.card_field]

def fourVectorEquiv (E : BinaryField) (hE : Nat.card E.Carrier = 4) :
    (Fin 3 → E.Carrier) ≃ₗ[ZMod 2] W where
  toFun v i := fourFieldEquiv E hE (v i)
  invFun v i := (fourFieldEquiv E hE).symm (v i)
  left_inv v := by funext i; exact (fourFieldEquiv E hE).symm_apply_apply _
  right_inv v := by funext i; exact (fourFieldEquiv E hE).apply_symm_apply _
  map_add' v w := by funext i; exact map_add _ _ _
  map_smul' c v := by
    funext i
    fin_cases c
    · change fourFieldEquiv E hE ((0 : ZMod 2) • v i) =
        (0 : ZMod 2) • fourFieldEquiv E hE (v i)
      simp
    · change fourFieldEquiv E hE ((1 : ZMod 2) • v i) =
        (1 : ZMod 2) • fourFieldEquiv E hE (v i)
      simp

def fourNaturalEquiv (E : BinaryField) (hE : Nat.card E.Carrier = 4) :
    ActionEquiv (linearNatural E 3) natural where
  groupEquiv := Atlas.fieldEquivSL 3 (fourFieldEquiv E hE)
  linearEquiv := fourVectorEquiv E hE
  intertwines g v := by
    funext i
    change fourFieldEquiv E hE (∑ j, g i j * v j) =
      ∑ j, fourFieldEquiv E hE (g i j) * fourFieldEquiv E hE (v j)
    simp only [map_sum, map_mul]

variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) D U}

def concreteRepeatedEquiv (E : BinaryField) (hE : Nat.card E.Carrier = 4) (r : ℕ)
    (e : ActionEquiv ρ (repeated (linearNatural E 3) r)) :
    ActionEquiv ρ (repeated natural r) where
  groupEquiv := e.groupEquiv.trans (fourNaturalEquiv E hE).groupEquiv
  linearEquiv := e.linearEquiv.trans
    (LinearEquiv.piCongrRight fun _ : Fin r => (fourNaturalEquiv E hE).linearEquiv)
  intertwines g v := by
    funext i
    change (fourNaturalEquiv E hE).linearEquiv (e.linearEquiv (ρ g v) i) = _
    rw [e.intertwines]
    exact (fourNaturalEquiv E hE).intertwines (e.groupEquiv g) (e.linearEquiv v i)

def concreteSingleEquiv (E : BinaryField) (hE : Nat.card E.Carrier = 4)
    (e : ActionEquiv ρ (linearNatural E 3)) : ActionEquiv ρ (repeated natural 1) where
  groupEquiv := e.groupEquiv.trans (fourNaturalEquiv E hE).groupEquiv
  linearEquiv := (e.linearEquiv.trans (fourNaturalEquiv E hE).linearEquiv).trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) W).symm
  intertwines g v := by
    funext i
    change (fourNaturalEquiv E hE).linearEquiv (e.linearEquiv (ρ g v)) = _
    rw [e.intertwines]
    exact (fourNaturalEquiv E hE).intertwines (e.groupEquiv g) (e.linearEquiv v)

private lemma natural_fixed_eq_zero (v : W) (hv : ∀ g : SL, natural g v = v) : v = 0 := by
  funext i
  have h := congrFun (centralScalar_norm v) i
  simpa only [hv, Pi.add_apply, CharTwo.add_self_eq_zero, zero_add, Pi.zero_apply] using h


variable {K : Subgroup D}

def quotientRepeatedSection (s : MovedSection ρ K) (r : ℕ) (hr : 0 < r)
    (e : ActionEquiv (s.action.comp K.subtype) (repeated natural r)) :
    RepeatedNaturalSection ρ K where
  sectionData := s
  marking := e.groupEquiv
  copies := r
  positive := hr
  coordinates := e.linearEquiv
  natural_action g w i := congrFun (e.intertwines g w) i

private lemma repeated_space_central_eq_bot (s : MovedSection ρ K) (r : ℕ)
    (e : ActionEquiv (s.space.toRepresentation.comp K.subtype) (repeated natural r)) :
    s.central.toSubmodule = ⊥ := by
  rw [s.central_eq]
  apply le_bot_iff.mp
  intro v hv
  apply e.linearEquiv.injective
  rw [map_zero]
  funext i
  apply natural_fixed_eq_zero
  intro g
  obtain ⟨k, rfl⟩ := e.groupEquiv.surjective g
  have hh := congrFun (e.intertwines k v) i
  change e.linearEquiv (s.space.toRepresentation k v) i =
    natural (e.groupEquiv k) (e.linearEquiv v i) at hh
  rw [show s.space.toRepresentation k v = v from hv k] at hh
  exact hh.symm

def spaceRepeatedSection (s : MovedSection ρ K) (r : ℕ) (hr : 0 < r)
    (e : ActionEquiv (s.space.toRepresentation.comp K.subtype) (repeated natural r)) :
    RepeatedNaturalSection ρ K where
  sectionData := s
  marking := e.groupEquiv
  copies := r
  positive := hr
  coordinates := (s.central.toSubmodule.quotEquivOfEqBot
    (by exact repeated_space_central_eq_bot s r e)).trans e.linearEquiv
  natural_action g w i := by
    induction w using Submodule.Quotient.induction_on with | _ w =>
      change e.linearEquiv (s.central.toSubmodule.quotEquivOfEqBot _
        (Submodule.Quotient.mk (s.space.toRepresentation g w))) i =
          natural (e.groupEquiv g) (e.linearEquiv
            (s.central.toSubmodule.quotEquivOfEqBot _ (Submodule.Quotient.mk w)) i)
      simp only [Submodule.quotEquivOfEqBot_apply_mk]
      exact congrFun (e.intertwines g w) i


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Recognition
