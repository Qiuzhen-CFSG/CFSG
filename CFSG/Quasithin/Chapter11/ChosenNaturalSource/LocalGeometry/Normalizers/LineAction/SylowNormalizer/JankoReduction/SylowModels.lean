module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.RankOne
public import Theory.GroupTheory.SylowAutomorphismPGroup
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.SpecificGroups.AlternatingSevenSylowNormalizer
public import Theory.Alternating.Aut
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Self-normalizing Sylow model exclusions

The actual moved component quotient has a nontrivial odd subgroup in its
Sylow automorphism stabilizer. A self-normalizing Sylow and a two-group
outer automorphism group force that stabilizer to be a two-group, giving
the contradiction used in source (**).

For SL₃(2), SL₄(2), and SL₅(2), the binary triangular Borel is precisely
the unitriangular Sylow. The proved inner-or-graph description supplies the
outer bound. Field and projective comparisons apply this to the actual
PSL model predicates. The A₇ calculation and the genuine PSL₄(2) ≃ A₈
isomorphism exclude both alternating rows. The final escape consumer combines
these with the preceding rank-one exclusions on the same component quotient.

This is part of the component recognition owned by
qt-d-1222-natural-line-action, not the complete exceptional classification.
Source: Aschbacher--Smith, A.3.12 and 3.3.12, printed pp.48,589--590.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private theorem sylow_stabilizer_two_of_equiv {H M : Type*} [Group H] [Group M] [Finite H]
    (e : H ≃* M) (hself : ∀ P : Sylow 2 M, normalizer (P : Set M) = (P : Subgroup M))
    (hout : IsPGroup 2 (MulAut.Outer M)) (P : Sylow 2 H) :
    IsPGroup 2 (MulAction.stabilizer (MulAut H) (P : Subgroup H)) := by
  apply MulAut.isPGroup_sylow_stabilizer_of_self_normalizing P
  · apply map_injective (f := e.toMonoidHom) e.injective
    change (normalizer ((P : Subgroup H) : Set H)).map e.toMonoidHom =
      (P : Subgroup H).map e.toMonoidHom
    rw [map_equiv_normalizer_eq]
    exact hself (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  · exact hout.of_equiv (MulAut.outerCongr e).symm

private theorem binary_borel_eq_unipotent (n : ℕ) :
    Theory.SpecificGroups.LinearSylowNormalizers.borel n (ZMod 2) =
      Theory.SpecificGroups.LinearSylowNormalizers.unipotent n (ZMod 2) := by
  open Theory.SpecificGroups.LinearSylowNormalizers in
    apply le_antisymm _ (unipotent_le_borel n (ZMod 2))
    intro g hg
    rw [mem_unipotent]
    refine ⟨hg, fun i => ?_⟩
    have hd := g.property
    rw [Matrix.det_of_isUpperTriangular ((mem_borel n (ZMod 2) g).mp hg)] at hd
    have hp : (∏ j, g.val j j) ≠ 0 := by rw [hd]; exact one_ne_zero
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _
      ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i))

private theorem binary_sylow_self_normalizing {n : ℕ} (hn : 0 < n)
    (P : Sylow 2 SL(n, ZMod 2)) :
    normalizer (P : Set SL(n, ZMod 2)) = (P : Subgroup SL(n, ZMod 2)) := by
  open Theory.SpecificGroups.LinearSylowNormalizers in
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(n,ZMod 2) (standardSylow n (ZMod 2) hn) P
    have he : (unipotent n (ZMod 2)).map (MulAut.conj g).toMonoidHom = (P : Subgroup _) :=
      by
        have hh := congrArg Sylow.toSubgroup hg
        change (standardSylow n (ZMod 2) hn : Subgroup SL(n,ZMod 2)).map
          (MulAut.conj g).toMonoidHom = (P : Subgroup SL(n,ZMod 2)) at hh
        rwa [coe_standardSylow] at hh
    change normalizer ((P : Subgroup SL(n,ZMod 2)) : Set SL(n,ZMod 2)) = _
    rw [← he, ← map_equiv_normalizer_eq, normalizer_unipotent, binary_borel_eq_unipotent]

private theorem alternating_seven_outer_two :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 7))) := by
  let A := alternatingGroup (Fin 7)
  have hcard : Nat.card (Equiv.Perm (Fin 7) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  have htwo : IsPGroup 2 (Equiv.Perm (Fin 7) ⧸ A) := IsPGroup.of_card hcard
  apply htwo.of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- Source (**) rules out any marked model with these two intrinsic properties. -/
theorem quotient_not_equiv_self_normalizing_outer_two {M : Type*} [Group M]
    (hself : ∀ P : Sylow 2 M, normalizer (P : Set M) = (P : Subgroup M))
    (hout : IsPGroup 2 (MulAut.Outer M)) :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* M) := by
  rintro ⟨e⟩
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  apply E.quotientSylow_stabilizer_not_twoGroup
  rw [← hP]
  exact sylow_stabilizer_two_of_equiv e hself hout P

/-- The actual component quotient is not A₇. -/
theorem quotient_not_alternating_seven :
    ¬ Chapter1.Section02.LocalModels.IsAlternating (E.component ⧸ pCore 2 E.component) 7 :=
  E.quotient_not_equiv_self_normalizing_outer_two
    AlternatingSevenSylow.sylow_normalizer_eq_self alternating_seven_outer_two

/-- All three relevant binary linear models are excluded, with their actual fields. -/
theorem quotient_not_binary_linear {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (E.component ⧸ pCore 2 E.component) n 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let e' := (e.trans (Atlas.fieldEquivPSL n k)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega))
  have ho : IsPGroup 2 (MulAut.Outer SL(n,ZMod 2)) := by
    rcases hn with rfl | hn
    · exact Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup
    · exact BinaryLinear.OuterCyclic.sl_outer_isTwoGroup hn
  exact E.quotient_not_equiv_self_normalizing_outer_two
    (binary_sylow_self_normalizing (by omega)) ho ⟨e'⟩

/-- The genuine exceptional isomorphism also excludes A₈. -/
theorem quotient_not_alternating_eight :
    ¬ Chapter1.Section02.LocalModels.IsAlternating (E.component ⧸ pCore 2 E.component) 8 := by
  rintro ⟨e⟩
  apply E.quotient_not_binary_linear (n := 4) (by omega)
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩
end MovedComponent

/-- The original escape yields a proper local image and these concrete model
exclusions, without changing its quotient, Sylow, or odd complement. -/
theorem exists_moved_component_model_restrictions (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      E.residualImage ∈ ChapterA.Section03.localCComponents E.quotientSylow ∧
      E.residualImage ≠ ⊤ ∧
      (¬ ClassificationModels.IsBenderModel (E.component ⧸ pCore 2 E.component)) ∧
      (∀ n : ℕ, 0 < n →
        ¬ Chapter1.Section02.LocalModels.IsSU (E.component ⧸ pCore 2 E.component) 3 (2^n)) ∧
      (∀ n : ℕ, n = 3 ∨ n = 4 ∨ n = 5 →
        ¬ ClassicalGroup.IsPSL (E.component ⧸ pCore 2 E.component) n 2) ∧
      (¬ Chapter1.Section02.LocalModels.IsAlternating (E.component ⧸ pCore 2 E.component) 7) ∧
      (¬ Chapter1.Section02.LocalModels.IsAlternating (E.component ⧸ pCore 2 E.component) 8) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E, E.residualImage_local, E.residualImage_ne_top, E.quotient_not_bender,
    fun _ hn => E.quotient_not_binary_su3 hn, fun _ hn => E.quotient_not_binary_linear hn,
    E.quotient_not_alternating_seven, E.quotient_not_alternating_eight⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
