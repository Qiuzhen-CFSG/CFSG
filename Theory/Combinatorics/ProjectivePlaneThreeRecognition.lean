module

public import Theory.Combinatorics.CollineationAction
public import Theory.Combinatorics.ProjectivePlaneThreeCoordinates
public import Theory.Combinatorics.ProjectivePlaneThreeCollineations

/-!
# Recognition from an action on a projective plane of order three

Every finite projective plane with four points on each line has an actual
incidence identification with PG(2,3). Conjugating its full collineation group
by that identification and using the canonical matrix action identifies this
group with PSL₃(3). The point action is the natural projective action; on line
covectors it is inverse transpose.

An incidence-preserving group action therefore gives a homomorphism to PSL₃(3).
Faithfulness on lines proves injectivity before any group orders are compared.
For a group of order 5616, equality with the order of PSL₃(3) then proves
surjectivity and yields a multiplicative equivalence.

Source motivation: Wong, *On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2*, Theorem 6(b), printed p. 111,
DOI 10.1017/S1446788700022771.
-/

namespace Configuration.PlaneThree

open Matrix.PSL3Three

variable {P L : Type*} [Membership P L]

/-- The full collineation group in given incidence coordinates is PSL₃(3). -/
@[expose] public noncomputable def collineationEquivOfCoordinates
    (ep : P ≃ PG) (el : L ≃ PG) (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l) :
    Collineation P L ≃* PSL :=
  (Collineation.congr ep el hi).trans collineationEquivPSL

/-- The equivalence preserves the actual projective point action. -/
public theorem collineationEquivOfCoordinates_point
    (ep : P ≃ PG) (el : L ≃ PG) (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l)
    (c : Collineation P L) (p : P) :
    ep (Collineation.pointHom P L c p) = collineationEquivOfCoordinates ep el hi c • ep p := by
  simpa [collineationEquivOfCoordinates] using
    collineationEquivPSL_point (Collineation.congr ep el hi c) (ep p)

/-- A determinant-one representative acts on line coordinates by inverse transpose. -/
public theorem collineationEquivOfCoordinates_line
    (ep : P ≃ PG) (el : L ≃ PG) (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l)
    (c : Collineation P L) (A : SL)
    (hA : collineationEquivOfCoordinates ep el hi c = project A) (l : L) :
    el (Collineation.lineHom P L c l) = Matrix.SpecialLinearGroup.inverseTranspose A • el l := by
  have hc : Collineation.congr ep el hi c = pslCollineation (project A) := by
    rw [← hA]
    exact (pslCollineation_collineationEquivPSL _).symm
  have hl := congrArg (fun d => Collineation.lineHom PG PG d (el l)) hc
  simpa using hl

/-- Coordinates and the full group identification can be chosen together, with
both the natural point action and the inverse-transpose line action. -/
public theorem exists_coordinates_collineationEquiv
    [Finite P] [Finite L] [ProjectivePlane P L]
    (h : ∀ l : L, pointCount P l = 4) :
    ∃ (ep : P ≃ PG) (el : L ≃ PG),
      (∀ p l, ep p ∈ el l ↔ p ∈ l) ∧
      ∃ e : Collineation P L ≃* PSL,
        (∀ c p, ep (Collineation.pointHom P L c p) = e c • ep p) ∧
        (∀ c (A : SL), e c = project A → ∀ l,
          el (Collineation.lineHom P L c l) =
            Matrix.SpecialLinearGroup.inverseTranspose A • el l) := by
  obtain ⟨ep, el, hi⟩ := Three.exists_coordinates h
  exact ⟨ep, el, hi, collineationEquivOfCoordinates ep el hi,
    collineationEquivOfCoordinates_point ep el hi,
    collineationEquivOfCoordinates_line ep el hi⟩

variable (G : Type*) [Group G] [MulAction G P] [MulAction G L]
  [IsCollineationAction G P L]

/-- The matrix homomorphism induced by an action and an incidence identification. -/
@[expose] public noncomputable def actionToPSL
    (ep : P ≃ PG) (el : L ≃ PG) (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l) : G →* PSL :=
  (collineationEquivOfCoordinates ep el hi).toMonoidHom.comp (Collineation.ofAction G P L)

/-- The induced homomorphism realizes the given action on point coordinates. -/
public theorem actionToPSL_point
    (ep : P ≃ PG) (el : L ≃ PG) (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l) (g : G) (p : P) :
    ep (g • p) = actionToPSL G ep el hi g • ep p :=
  collineationEquivOfCoordinates_point ep el hi (Collineation.ofAction G P L g) p

/-- The induced homomorphism realizes the given action on line covectors. -/
public theorem actionToPSL_line
    (ep : P ≃ PG) (el : L ≃ PG) (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l)
    (g : G) (A : SL) (hA : actionToPSL G ep el hi g = project A) (l : L) :
    el (g • l) = Matrix.SpecialLinearGroup.inverseTranspose A • el l :=
  collineationEquivOfCoordinates_line ep el hi (Collineation.ofAction G P L g) A hA l

/-- Faithfulness on lines proves injectivity of the incidence-induced matrix map. -/
public theorem actionToPSL_injective [FaithfulSMul G L]
    (ep : P ≃ PG) (el : L ≃ PG) (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l) :
    Function.Injective (actionToPSL G ep el hi) :=
  (collineationEquivOfCoordinates ep el hi).injective.comp
    (Collineation.ofAction_injective G P L)

/-- A group of order 5616 acting by collineations faithfully on the lines of an
order-three plane is isomorphic to the actual projective special linear group. -/
public theorem nonempty_mulEquiv_PSL [Finite G] [Finite P] [Finite L]
    [ProjectivePlane P L] [FaithfulSMul G L]
    (h : ∀ l : L, pointCount P l = 4) (hG : Nat.card G = 5616) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) := by
  obtain ⟨ep, el, hi⟩ := Three.exists_coordinates h
  let f := actionToPSL G ep el hi
  have hf : Function.Injective f := actionToPSL_injective G ep el hi
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hG.trans card_PSL.symm⟩
  exact ⟨MulEquiv.ofBijective f hbij⟩

end Configuration.PlaneThree
