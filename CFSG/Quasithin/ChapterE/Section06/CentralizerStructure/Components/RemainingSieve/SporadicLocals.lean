module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceInputs
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# The sporadic branch of E.6.8

This file is the source-correct interface for the last paragraph of E.6.8.
The quotient in the sporadic alternative is the quotient of the *actual*
component by its two-core.  In particular, no centreless or split-cover
assumption is made.  For `Q = C_T(V)` we retain
`Q_L = Q ∩ N_G(L)` and form the image of `L` in
`X/O₂(X)`, where `X = L Q_L`.

The nine exclusions use intrinsic model calculations.  Those calculations are
represented by `SporadicInvariantWitness`; the record contains only the local
facts consumed by the argument (the invariant subgroup, its block obstruction,
the characteristic-two overgroup, and the residual transfer).  The E.6.7
placement statement is an explicit source input, so this module does not hide
an E.6.8 conclusion in a record projection.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.7 and the
last paragraph of E.6.8, printed pp.246--248 (PDF pp.257--259).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterE.Section06.Components
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open _root_.CFSG.Quasithin.ClassificationModels
open _root_.CFSG.Quasithin.Chapter1.Section02.LocalModels
open _root_.CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure

namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The image of an embedded subgroup in the actual two-core quotient of an
overgroup.  The inclusion is explicit so that no ambient coercion is hidden.
-/
def quotientImage (A X : Subgroup G) (hAX : A ≤ X) :
    Subgroup (X ⧸ pCore 2 X) :=
  let _ := hAX
  (A.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))

/-- Pull a subgroup of `X/O₂(X)` back to `X` and then embed it in `G`. -/
def liftedQuotientSubgroup (X : Subgroup G)
    (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup G :=
  (P.comap (QuotientGroup.mk' (pCore 2 X))).map X.subtype

omit [Finite G] in
theorem liftedQuotientSubgroup_le (X : Subgroup G)
    (P : Subgroup (X ⧸ pCore 2 X)) :
    liftedQuotientSubgroup X P ≤ X := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property

omit [Finite G] in
/-- The quotient image of the lifted subgroup is the subgroup with which we
started.  This is the lift used in the residual transfer below. -/
theorem quotientImage_liftedQuotientSubgroup (X : Subgroup G)
    (P : Subgroup (X ⧸ pCore 2 X)) :
    quotientImage (liftedQuotientSubgroup X P) X
        (liftedQuotientSubgroup_le X P) = P := by
  have hs : (liftedQuotientSubgroup X P).subgroupOf X =
      P.comap (QuotientGroup.mk' (pCore 2 X)) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have heq : y = x := Subtype.ext hxy
      simpa [heq] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  change ((liftedQuotientSubgroup X P).subgroupOf X).map
      (QuotientGroup.mk' (pCore 2 X)) = P
  rw [hs, Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (pCore 2 X))]

/-- The nine sporadic names removed in the last paragraph of E.6.8.  M₁₁ and
J₃ are deliberately retained. -/
def IsExcludedSporadic : SporadicName → Prop
  | .m11 | .j3 => False
  | .m12 | .m22 | .m23 | .m24 | .j2 | .j4 | .hs | .he | .ru => True

theorem isExcludedSporadic_iff (name : SporadicName) :
    IsExcludedSporadic name ↔
      name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨
        name = .j2 ∨ name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru := by
  cases name <;> simp [IsExcludedSporadic]

/-- Intrinsic data for one excluded sporadic model.

`PStar` is a subgroup of the actual image of `L` in `X/O₂(X)`, and is
`Q_L`-invariant.  `fstar` and `central_residual` are the two local model
calculations in the source.  `block_place` is the exact E.6.7 block theorem
specialised to this `PStar`; it is a source input and still has to be
discharged by the model owner.
-/
structure SporadicInvariantWitness
    (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hnotLie : ¬ LieTypeComponent L)
    (name : SporadicName) (z : G) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hnotj3 : name ≠ .j3)
    (hmodel : Nonempty ((L ⧸ pCore 2 L) ≃* name.Carrier))
    (haction : TwoCentralInner α) where
  Q : Subgroup G
  q_eq : Q = sylowCentralizer (T : Subgroup G) V
  QL : Subgroup G
  ql_eq : QL = Q ⊓ normalizer (L : Set G)
  ql_le_Q : QL ≤ Q
  ql_le_normalizer : QL ≤ normalizer (L : Set G)
  X : Subgroup G
  x_eq : X = L ⊔ QL
  l_le_X : L ≤ X
  ql_le_X : QL ≤ X
  pStar : Subgroup (X ⧸ pCore 2 X)
  pStar_le_lStar : pStar ≤ quotientImage L X l_le_X
  qlStar_le_normalizer :
    quotientImage QL X ql_le_X ≤ normalizer (pStar : Set (X ⧸ pCore 2 X))
  block_obstruction : ¬ ChapterC.IsChiZeroBlock pStar
  fstar : generalizedFitting ↥(pStar ⊔ quotientImage QL X ql_le_X) =
      pCore 2 ↥(pStar ⊔ quotientImage QL X ql_le_X)
  central_residual :
    (center ↥(quotientImage QL X ql_le_X)).map
          (quotientImage QL X ql_le_X).subtype ⊓
        centralizer ((primeToResidual 2 ↥pStar).map pStar.subtype : Set _) = ⊥
  P : Subgroup G
  P_eq_lift : P = liftedQuotientSubgroup X pStar
  P_le_X : P ≤ X
  P_le_centralizer_U : P ≤ centralizer (U : Set G)
  Q_le_centralizer_U : Q ≤ centralizer (U : Set G)
  local_characteristic_two : HasCharacteristicTwo ↥(P ⊔ Q)
  /-- The residual subgroup produced by the model calculation.  Its first
  inclusion is the source residual transfer; the second is the fixed-space
  condition used by `residual_fixedSpace_obstruction`. -/
  residual_transfer : P ≤ M → ∃ R : Subgroup G,
    R ≤ (primeToResidual 2 ↥(L ⊓ M)).map (L ⊓ M).subtype ∧
      V ⊓ centralizer (R : Set G) ≤ centralizer (L : Set G)
  /-- Exact E.6.7 placement input for the actual lifted `P`. -/
  block_place :
    ∀ {H : Subgroup G}, Q ≤ H → H ≤ centralizer (U : Set G) →
      HasCharacteristicTwo H →
      Nonempty (E67Decomposition Q M V U H) →
      pStar ≤ quotientImage L X l_le_X →
      quotientImage QL X ql_le_X ≤ normalizer (pStar : Set (X ⧸ pCore 2 X)) →
      ¬ ChapterC.IsChiZeroBlock pStar →
      generalizedFitting ↥(pStar ⊔ quotientImage QL X ql_le_X) =
        pCore 2 ↥(pStar ⊔ quotientImage QL X ql_le_X) →
      (center ↥(quotientImage QL X ql_le_X)).map
            (quotientImage QL X ql_le_X).subtype ⊓
          centralizer ((primeToResidual 2 pStar).map pStar.subtype : Set _) = ⊥ →
      P ≤ M

theorem SporadicInvariantWitness.lift_image
    {h : HypothesisE61 K T M V}
    {hU : U ∈ obstructionFamily M V}
    {hL : ComponentIn (centralizer (U : Set G)) L}
    {hnotLie : ¬ LieTypeComponent L}
    {name : SporadicName} {z : G} {α : MulAut L}
    {hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹}
    {hnotj3 : name ≠ .j3}
    {hmodel : Nonempty ((L ⧸ pCore 2 L) ≃* name.Carrier)}
    {haction : TwoCentralInner α}
    (w : SporadicInvariantWitness h hU hL hnotLie name z α hα hnotj3 hmodel haction) :
    quotientImage w.P w.X w.P_le_X = w.pStar := by
  simpa only [w.P_eq_lift] using
    (quotientImage_liftedQuotientSubgroup w.X w.pStar)

/-- Establish the characteristic-two condition on the local overgroup and
apply the supplied E.6.7 theorem. -/
theorem SporadicInvariantWitness.place_in_M
    {h : HypothesisE61 K T M V}
    {hU : U ∈ obstructionFamily M V}
    {hL : ComponentIn (centralizer (U : Set G)) L}
    {hnotLie : ¬ LieTypeComponent L}
    {name : SporadicName} {z : G} {α : MulAut L}
    {hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹}
    {hnotj3 : name ≠ .j3}
    {hmodel : Nonempty ((L ⧸ pCore 2 L) ≃* name.Carrier)}
    {haction : TwoCentralInner α}
    (h67 : E67Input T M V)
    (w : SporadicInvariantWitness h hU hL hnotLie name z α hα hnotj3 hmodel haction) :
    w.P ≤ M := by
  let H := w.P ⊔ w.Q
  have hQH : w.Q ≤ H := le_sup_right
  have hQH' : sylowCentralizer (T : Subgroup G) V ≤ H := by
    rw [← w.q_eq]
    exact hQH
  have hHC : H ≤ centralizer (U : Set G) := by
    apply sup_le w.P_le_centralizer_U w.Q_le_centralizer_U
  have hchar : HasCharacteristicTwo H := by
    simpa only [H] using w.local_characteristic_two
  obtain ⟨d⟩ := h67 U hU H hQH' hHC hchar
  have hdecomp : Nonempty (E67Decomposition w.Q M V U H) := by
    rw [w.q_eq]
    exact ⟨d⟩
  exact w.block_place hQH hHC hchar hdecomp w.pStar_le_lStar
    w.qlStar_le_normalizer w.block_obstruction w.fstar w.central_residual

/-- The residual transfer and the E.6.7 placement contradict the fact that the
component escapes `M`.  This is the source contradiction for each of the nine
model rows. -/
theorem sporadic_exclusion_of_witness
    (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T)
    (h67 : E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {hnotLie : ¬ LieTypeComponent L}
    {name : SporadicName} {z : G} {α : MulAut L}
    {hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹}
    {hnotj3 : name ≠ .j3}
    {hmodel : Nonempty ((L ⧸ pCore 2 L) ≃* name.Carrier)}
    {haction : TwoCentralInner α}
    (_hname : IsExcludedSporadic name)
    (w : SporadicInvariantWitness h hU hL hnotLie name z α hα hnotj3 hmodel haction) :
    False := by
  have hLM : ¬ L ≤ M := component_not_le h earlier hU hL
  have hPM : w.P ≤ M := w.place_in_M h67
  obtain ⟨R, hR, hfixed⟩ := w.residual_transfer hPM
  exact residual_fixedSpace_obstruction h hU hL.1 hLM hR hfixed

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve

end
