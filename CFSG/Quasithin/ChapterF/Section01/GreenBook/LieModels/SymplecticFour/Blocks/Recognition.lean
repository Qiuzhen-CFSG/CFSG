module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# Genuine natural-block recognition for the nonbinary symplectic locals

The explicit extension data imply every clause of C.1.7, and identify both
the core quotient and the central quotient of the commutator layer with
the actual SL₂ natural action. No short-group, perfectness, generalized
Fitting, or irreducibility conclusion is assumed.

The isomorphism and subnormal-subgroup wrappers apply inside a chosen local
overgroup. In particular they can be used on `Li.subgroupOf Pi` without
requiring ambient normality in Sp₄. The final PSL₂ naming and the concrete
point/plane matrix calculations belong to the parent assembly.

Source: Aschbacher–Smith C.1.7/C.1.12 and F.1.12(I)(2), combined manuscript
of 1 March 2004, printed pp.123–124 and 262–264.
-/

public section

open Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterF.SymplecticFourRecognition
open ChapterC
variable {F L : Type*} [Field F] [Finite F] [CharP F 2] [Group L] [Finite L]
variable {Q : Subgroup L} [Q.Normal] (d : NaturalExtension (F := F) Q)
include d

/-- The commutator layer in C.1.7 is the explicit kernel. -/
theorem blockU_eq (hF : 2 < Nat.card F) : blockU L = Q := by
  rw [blockU, d.core_eq hF, d.commutator_eq]

/-- All five source short-group clauses follow from the explicit extension. -/
theorem isShort (hF : 2 < Nat.card F) : IsShort L := by
  have hu := blockU_eq d hF
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
theorem isLinearBlockModel (hF : 2 < Nat.card F) :
    IsLinearBlockModel L (Representation.specialLinearNatural (k := F) 2) := by
  have hu := blockU_eq d hF
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

/-- Recognition, including perfectness needed for the residual identification. -/
theorem recognition {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    pCore 2 L = Q ∧ Group.IsPerfect L ∧ IsShort L ∧
      IsLinearBlockModel L (Representation.specialLinearNatural (k := F) 2) := by
  have hc : 2 < Nat.card F := by
    rw [hF]
    calc
      2 = 2 ^ 1 := by decide
      _ < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn
  exact ⟨d.core_eq hc, d.perfect hc, isShort d hc, isLinearBlockModel d hc⟩

omit [Finite L] in
/-- Recognition after an actual isomorphism, suitable for relative local subgroups. -/
theorem recognition_of_equiv {H : Type*} [Group H] [Finite H] (e : H ≃* L)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    pCore 2 H = Q.comap e.toMonoidHom ∧ Group.IsPerfect H ∧ IsShort H ∧
      IsLinearBlockModel H (Representation.specialLinearNatural (k := F) 2) :=
  recognition (d.comap e) hn hF
omit [Finite L] in
/-- A subnormal subgroup of the chosen local overgroup is a genuine block.
Apply this with `K := Li.subgroupOf Pi`; no ambient normality is required. -/
theorem isBlock_of_equiv {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (e : K ≃* L) (hK : K.IsSubnormal)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) : IsBlock K :=
  ⟨inferInstance, (recognition_of_equiv d e hn hF).2.2.1, hK⟩
end CFSG.Quasithin.ChapterF.SymplecticFourRecognition
