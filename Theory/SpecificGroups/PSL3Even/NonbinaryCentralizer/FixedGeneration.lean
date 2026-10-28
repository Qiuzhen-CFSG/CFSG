module

public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.Models
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.StandardGeneration
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.FixedGeneration.Transport
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.FixedGeneration.GraphMarkedConjugacy
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.FixedGeneration.FieldMarkedConjugacy
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent.FixedQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Structure and marked generation of the selected nonbinary PSL₃ fixed groups

The whole fixed subgroup of a coefficient involution is the projective
special linear group over its literal fixed subfield. Higher-rank simplicity
and elementary-matrix perfectness apply even when that subfield is binary.
Transport through actual automorphism conjugacy, together with the graph
calculation in `Models`, proves simplicity and perfectness for every actor
satisfying `IsGraphOrField` over a field of order `2^f`, `f > 1`.

If the actor preserves the original upper-unipotent subgroup, the marked
conjugacy constructions carry it to the Borel-preserving opposition graph
representative or to the same coefficient involution, preserving that subgroup.
Standard generation therefore transports with the original marking. Together
these results supply exactly `hfixed` and `hgenerate` in the Chapter E consumer
`NonbinaryGeometry.simpleCentralizerGeometry_of_model_calculations`.
The separate actor-selection premise remains with that consumer's owner.

Sources: Aschbacher–Smith E.1.1–6 and E.1.14(1), printed pp.209–214;
GLS3, Theorem 2.5.12 and §2.7. The imported simplicity and perfectness
proofs retain the ATLAS attribution in `ExceptionalIsomorphisms`.
-/

public section
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Even.NonbinaryCentralizer
variable {F : Type*} [Field F]

/-- The whole coefficient-fixed group is simple and perfect, including the
binary fixed field. Neither a residual nor a lower bound on the fixed field
is needed. -/
theorem field_fixed_simple_perfect (σ : F ≃+* F) (hs : σ ^ 2 = 1) :
    IsSimpleGroup (fieldAction F σ).fixedSubgroup ∧
      Group.IsPerfect (fieldAction F σ).fixedSubgroup := by
  let e := OuterElementaryRank.FixedRanks.FieldDescent.pure_field_fixed_equiv σ hs
  let := Atlas.psl_simple_high_rank (F := FixedBy.subfield F σ) 3 (by decide)
  let := Atlas.psl_perfect (F := FixedBy.subfield F σ) 3 (by decide)
  exact ⟨e.isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

/-- Actual conjugacy to a coefficient involution preserves the whole fixed
group structure. -/
theorem field_fixed_simple_perfect_of_isConj (σ : F ≃+* F) (hs : σ ^ 2 = 1)
    (a : MulAut PSL(3,F)) (ha : IsConj a (fieldAction F σ)) :
    IsSimpleGroup a.fixedSubgroup ∧ Group.IsPerfect a.fixedSubgroup := by
  obtain ⟨c, hc⟩ := isConj_iff.mp ha
  have he : MulAut.congr c a = fieldAction F σ := hc
  let e := (MulAut.fixedSubgroupCongr c a).trans
    (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he))
  obtain ⟨hsimple, hperfect⟩ := field_fixed_simple_perfect σ hs
  let := hsimple
  let := hperfect
  exact ⟨e.isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

/-- The exact fixed-group structure premise of the nonbinary centralizer
geometry consumer, with no additional model-identification hypothesis. -/
theorem fixed_simple_perfect_of_isGraphOrField [Finite F] {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (a : MulAut PSL(3,F)) (ha : IsGraphOrField a) :
    IsSimpleGroup a.fixedSubgroup ∧ Group.IsPerfect a.fixedSubgroup := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rcases ha with hg | ⟨σ, _, hs, hc⟩
  · apply graph_fixed_simple_perfect_of_isConj _ a hg
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ f)
  · exact field_fixed_simple_perfect_of_isConj σ hs a hc

/-- The exact generation premise of the nonbinary centralizer geometry
consumer. Actual conjugacy and preservation of the marked unipotent subgroup
suffice; both branches construct a conjugator preserving that same subgroup. -/
theorem fixed_sup_unipotent_of_isGraphOrField [Finite F] {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (a : MulAut PSL(3,F)) (ha : IsGraphOrField a)
    (hU : (Matrix.PSL3.LinearThree.unipotent F).map a.toMonoidHom =
      Matrix.PSL3.LinearThree.unipotent F) :
    a.fixedSubgroup ⊔ Matrix.PSL3.LinearThree.unipotent F = ⊤ := by
  rcases ha with hg | ⟨σ, hσ, hs, hc⟩
  · exact graph_fixed_sup_unipotent_of_isConj hf hF a hg hU
  · exact field_fixed_sup_unipotent_of_isConj hf hF σ hσ hs a hc hU

end Matrix.PSL3Even.NonbinaryCentralizer
