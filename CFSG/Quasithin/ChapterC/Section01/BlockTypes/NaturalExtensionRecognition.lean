module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.FromCover
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# Rank-one block recognition from an explicit elementary extension

The actual quotient and natural central-quotient action imply all the short
block conditions, including perfectness and the generalized Fitting condition.
This adapter is at Chapter C so the fixed-block argument of Chapter 2 can use
it without a dependency on Chapter F's parabolic assembly.

Source: Aschbacher--Smith C.1.7, C.1.12 and 2.4.12(2), printed pp.123--124,532.
-/

public section
noncomputable section
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC
variable {F : Type} {L : Type*} [Field F] [Finite F] [CharP F 2] [Group L] [Finite L]
variable {Q : Subgroup L} [Q.Normal] (d : NaturalExtension (F := F) Q)
include d

/-- The commutator layer in C.1.7 is the explicit kernel. -/
private theorem extension_blockU_eq (hF : 2 < Nat.card F) : blockU L = Q := by
  rw [blockU, d.core_eq hF, d.commutator_eq]

/-- All five source short-group clauses follow from the explicit extension. -/
private theorem extension_isShort (hF : 2 < Nat.card F) : IsShort L := by
  have hu := extension_blockU_eq d hF
  refine {
    finite := inferInstance
    twoPerfect := d.twoPerfect hF
    fitting := d.generalizedFitting_eq hF
    elementary := ?_
    central := ?_
    quotient := Or.inl (d.quotient_quasisimple hF)
    irreducible := ?_
  }
  · rw [hu]
    exact d.elementary
  · rw [hu, d.core_eq hF, d.centralizer_eq]
  · change blockU L ⊓ Subgroup.center L < blockU L ∧ _
    rw [hu]
    exact ⟨d.central_lt, fun N hN hlo hhi => @NaturalExtension.invariant_interval
      F L _ _ Q _ d N hN hlo hhi⟩

/-- The quotient and module isomorphisms retain the literal matrix action. -/
private theorem extension_isLinearBlockModel (hF : 2 < Nat.card F) :
    IsLinearBlockModel L (Representation.specialLinearNatural (k := F) 2) := by
  have hu := extension_blockU_eq d hF
  subst Q
  refine ⟨naturalAction, ⟨{
    quotientIso := d.quotientIso hF
    moduleIso := d.moduleIso
    intertwining := ?_
  }⟩, ?_⟩
  · intro l u
    apply Multiplicative.toAdd.injective
    rw [d.quotientIso_mk hF]
    exact d.intertwining l u
  · intro g v
    rfl


/-- An actual elementary natural extension is the named even rank-one block. -/
theorem isL2EvenBlock_of_naturalExtension {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) : IsL2EvenBlock L n := by
  have hc : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hn)
  exact ⟨hn,extension_isShort d hc,F,inferInstance,inferInstance,hF,
    ⟨F,inferInstance,inferInstance,hF,⟨(d.quotientIso hc).trans
      (Representation.SL2NaturalH1.projectiveEquiv (K := F)).symm⟩⟩,
    extension_isLinearBlockModel d hc⟩

omit d in
/-- The actual marked orthogonal core recognizes an even rank-one block. -/
theorem isL2EvenBlock_of_orthogonalExtension [Algebra (ZMod 2) F]
    (hQ : IsElementaryAbelian 2 Q)
    (actor : L →* Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : Function.Surjective actor) (hk : actor.ker = Q)
    (e : Q ≃* Multiplicative (Representation.SL2OrthogonalCover.Space F))
    (he : ∀ (l : L) (u : Q),
      (e (extensionConjugate Q l u)).toAdd = Representation.SL2OrthogonalCover.action (actor l) (e u).toAdd)
    {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n) : IsL2EvenBlock L n := by
  have hc : 2<Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide : 0<2) hn)
  exact isL2EvenBlock_of_naturalExtension
    (naturalExtensionOfOrthogonal hQ actor ha hk hc e he) hn hF
end CFSG.Quasithin.ChapterC
