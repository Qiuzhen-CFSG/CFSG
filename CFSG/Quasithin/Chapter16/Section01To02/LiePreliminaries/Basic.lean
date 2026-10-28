module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.GroupAction.SylowPointwiseInner
public import Theory.GroupAction.CentralKernelFixedResidual

/-!
# Quotients and residuals for the characteristic-two component cases

In Lemmas 16.1.2–16.1.6, the simple quotient is L/Z(L), while (E2) is
stated for L/O₂(L). The established center-core equality identifies these
quotients by the canonical map. Automorphisms act through that map, and
their fixed two-residuals map onto the corresponding quotient residuals.
This last assertion does not identify a central cover with its quotient.

The two alternatives below record precisely the Lie-family conclusions
still required from the multiplier and covering calculations. They are
output predicates, not assumptions asserting those calculations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed pp.1170–1172. Throughout, L_r means
O²(C_L(r)), never O₂(C_L(r)).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.LiePreliminaries
open Subgroup Theory.GroupTheory ClassificationModels

variable (L : Type*) [Group L]

/-- The ambient subgroup L_r = O²(C_L(r)) of source 16.1.4. -/
def fixedTwoResidual (r : MulAut L) : Subgroup L :=
  (pResidual 2 r.fixedSubgroup).map r.fixedSubgroup.subtype

/-- The Lie-family part of the nonsimple-cover list in 16.1.2(1). -/
def NonsimpleLieAlternative : Prop :=
  Nonempty ((L ⧸ center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) ∨
    ClassicalGroup.IsPSL (L ⧸ center L) 3 4 ∨ IsG2At (L ⧸ center L) 4

/-- The exact Lie-family part of 16.1.2(2), with an actual E₄ center. -/
def LieCenterAlternative : Prop :=
  Nat.card (center L) ≤ 2 ∨
    ((Nonempty ((L ⧸ center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) ∨
      ClassicalGroup.IsPSL (L ⧸ center L) 3 4) ∧
      Nonempty (center L ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))

variable {L} [Finite L] [IsQuasisimple L]

/-- The canonical identification of the two source quotient conventions. -/
noncomputable def centerQuotientEquivTwoCore (hodd : pPrimeCore 2 L = ⊥) :
    (L ⧸ center L) ≃* (L ⧸ pCore 2 L) :=
  QuotientGroup.quotientMulEquivOfEq (IsQuasisimple.center_eq_pCore hodd)

/-- The center/core quotient identification preserves the image of each element. -/
theorem centerQuotientEquivTwoCore_mk (hodd : pPrimeCore 2 L = ⊥) (x : L) :
    centerQuotientEquivTwoCore hodd (QuotientGroup.mk' (center L) x) =
      QuotientGroup.mk' (pCore 2 L) x := rfl

/-- The source's fixed two-residual projects onto the fixed two-residual
in any specified model of the simple quotient. This is surjectivity,
not a claim of injectivity through an exceptional central cover. -/
theorem map_fixedTwoResidual (hodd : pPrimeCore 2 L = ⊥)
    {S : Type*} [Group S] (e : (L ⧸ center L) ≃* S) (r : MulAut L) :
    (fixedTwoResidual L r).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) =
      fixedTwoResidual S (MulAut.centralQuotientAction e r) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  let b := MulAut.centralQuotientAction e r
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center L))
  have hk : f.ker = center L := by
    ext x
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 f.ker := by
    rw [hk, IsQuasisimple.center_eq_pCore hodd]
    exact pCore_isPGroup
  have heq (x : L) : f (r x) = b (f x) :=
    (MulAut.centralQuotientAction_apply e r x).symm
  have hm := MulAut.map_fixedResidual_of_central_pgroup_ker 2 r b f hf hk.le hp heq
  have hs := congrArg (fun U : Subgroup b.fixedSubgroup => U.map b.fixedSubgroup.subtype) hm
  rw [map_map] at hs
  change ((pResidual 2 r.fixedSubgroup).map r.fixedSubgroup.subtype).map f = _
  rw [map_map]
  exact hs

end CFSG.Quasithin.Chapter16.LiePreliminaries
