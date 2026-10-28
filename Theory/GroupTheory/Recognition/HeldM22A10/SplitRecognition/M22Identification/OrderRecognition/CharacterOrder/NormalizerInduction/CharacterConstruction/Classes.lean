module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.Action

/-!
# Marked conjugacy-class representatives for the normalizer table

Nine representatives are fixed by the given centralizer coordinates. The
remaining representatives are an element of the other class of order three
and an element of order five (whose square represents the other fifth-order
class). `NormalizerClassData` asks for actual class coverage and separation
in the actual normalizer. Its construction is a group-theoretic obligation,
independent of constructing the characters.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.10–11.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)

/-- The given involution centralizer embedded in the actual normalizer. -/
@[expose] public def normalizerCentralizer :
    TwistedModel →* normalizer (CaseII.E D k : Set G) :=
  (CaseII.into D k).codRestrict _
    (fun x => centralizer_le_E_normalizer D k (k x).property)

public theorem normalizerCentralizer_injective :
    Function.Injective (normalizerCentralizer D k) := by
  intro x y h
  apply CaseII.into_injective D k
  exact congrArg (fun x : normalizer (CaseII.E D k : Set G) => (x : G)) h

/-- The seven nonspecial representatives, once `c₁` and `μ` are chosen. -/
@[expose] public def normalizerNonspecialRepresentative
    (c₁ μ : normalizer (CaseII.E D k : Set G)) :
    Fin 7 → normalizer (CaseII.E D k : Set G) :=
  ![1, normalizerCentralizer D k CaseII.a, normalizerCentralizer D k CaseII.c,
    c₁, normalizerCentralizer D k (CaseII.b * CaseII.d), μ, μ ^ 2]

/-- All twelve representatives, with the five special ones first. -/
@[expose] public def normalizerFullRepresentative
    (c₁ μ : normalizer (CaseII.E D k : Set G)) :
    Fin 12 → normalizer (CaseII.E D k : Set G) :=
  Fin.append (normalizerRepresentative D k) (normalizerNonspecialRepresentative D k c₁ μ)

/-- The exact class-coverage obligation. Conjugacy here is internal to N(E),
and the named representatives retain the marking of the original `k`. -/
public structure NormalizerClassData where
  otherThree : normalizer (CaseII.E D k : Set G)
  five : normalizer (CaseII.E D k : Set G)
  otherThree_order : orderOf otherThree = 3
  five_order : orderOf five = 5
  distinct : Function.Injective
    (fun r => ConjClasses.mk (normalizerFullRepresentative D k otherThree five r))
  covers : ∀ x, ∃ r, IsConj x (normalizerFullRepresentative D k otherThree five r)

variable {D k}

/-- The chosen class representatives. -/
@[expose] public def NormalizerClassData.representative (Q : NormalizerClassData D k) :
    Fin 12 → normalizer (CaseII.E D k : Set G) :=
  normalizerFullRepresentative D k Q.otherThree Q.five

/-- The first five marked representatives agree with the published interface. -/
public theorem NormalizerClassData.representative_special (Q : NormalizerClassData D k)
    (r : Fin 5) : Q.representative (Fin.castAdd 7 r) = normalizerRepresentative D k r :=
  Fin.append_left _ _ r

/-- Coverage reduces every element outside the special set to one of the
seven remaining representatives. -/
public theorem NormalizerClassData.nonspecial_covers (Q : NormalizerClassData D k)
    (x : normalizer (CaseII.E D k : Set G)) (hx : x ∉ normalizerSpecialSupport D k) :
    ∃ r : Fin 7, IsConj x (Q.representative (Fin.natAdd 5 r)) := by
  obtain ⟨r, hr⟩ := Q.covers x
  change IsConj x (Q.representative r) at hr
  revert hr
  refine Fin.addCases (m := 5) (n := 7)
    (motive := fun r => IsConj x (Q.representative r) →
      ∃ s : Fin 7, IsConj x (Q.representative (Fin.natAdd 5 s)))
    (fun r hr => ?_) (fun r hr => ⟨r, hr⟩) r
  exact (hx ⟨r, (Q.representative_special r) ▸ hr⟩).elim

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
