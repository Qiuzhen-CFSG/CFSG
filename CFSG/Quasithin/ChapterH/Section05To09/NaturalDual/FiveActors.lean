module

public import Theory.Representation.BinaryNaturalDual.FiveActors
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.GeneratedCore

/-!
# The complete coordinate theorem family H.9.2

The actual automorphism group of GL₅(2) has one class of outer involutions.
Their fixed five-space splits into a nonsingular fixed line and the natural
four-dimensional S₆ commutator module. Large elementary actors are inner
and conjugate into the marked three-space radical. Its order turns this
placement into the exact rank-six and rank-five classifications. The
hyperplane centralizer and commutator formulas, followed by the actual
E.3.30 generated-core bridge, complete the five coordinate clauses.

The only representation input is `CoordinateAction 5`, specifying the
inner and graph actions. Constructing it and comparing an arbitrary source
module to these coordinates remain with the parent H.9 source assembly.
The older conditional core interfaces below are retained for compatibility.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.2(1–5),
printed pp.390–391 (PDF pp.401–402), and E.3.30, printed p.237.
-/

public section

namespace CFSG.Quasithin.ChapterH.NaturalDual.FiveActors
open BinaryNaturalDual BinaryNaturalDual.FiveActors

/-- A subgroup of the actual inner radical has full source generated core. -/
theorem dualGeneratedCore_eq_top_of_le_radicalActor (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (hA : A ≤ radicalActor U) :
    ChapterE.dualGeneratedCore
      (multiplicativeAction (d.representation.comp A.subtype)) 3 = ⊤ := by
  rw [← generatedCore_subgroup,
    BinaryNaturalDual.FiveActors.generatedCore_eq_top_of_le_radicalActor d U hU A hA,
    OrderIso.map_top]

/-- The source core is unchanged by simultaneous actor and module conjugation. -/
theorem dualGeneratedCore_eq_top_of_conjugate_radical (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (a : M)
    (hA : A.map (MulAut.conj a).toMonoidHom ≤ radicalActor U) :
    ChapterE.dualGeneratedCore
      (multiplicativeAction (d.representation.comp A.subtype)) 3 = ⊤ := by
  rw [← generatedCore_subgroup,
    BinaryNaturalDual.FiveActors.generatedCore_eq_top_of_conjugate_radical d U hU A a hA,
    OrderIso.map_top]

open BinaryNaturalDual.AdaptedPair BinaryNaturalDual.FiveActors.ModuleGeometry
open Theory.SpecificGroups.SymmetricSix

/-- H.9.2(1): actual conjugacy of any two outer involutions. -/
theorem lemma_H_9_2_1_conjugacy (s t : M) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hsout : s ∉ L) (htout : t ∉ L) :
    ∃ a : M, MulAut.conj a s = t :=
  outer_conjugate s t hs ht hsout htout

/-- H.9.2(1): the literal equivariant map `w ↦ (w,0) + t(w,0)` identifies
the natural five-space with both the actual fixed and commutator spaces. -/
theorem lemma_H_9_2_1_diagonal (d : CoordinateAction 5)
    (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) :
    ∃ θ : X ≃ₗ[ZMod 2] fixedSpace (linearAction d t),
      (∀ w : X, (θ w : V) = (w, 0) + d.representation t (w, 0)) ∧
      (∀ (a : innerCentralizer t) (w : X),
        (θ (centralizerNatural t a w) : V) = d.representation a.val (θ w)) ∧
      fixedSpace (linearAction d t) =
        Representation.BinaryOffender.fixedSpace d.representation (Subgroup.zpowers t) ∧
      fixedSpace (linearAction d t) =
        Representation.BinaryOffender.subspaceCommutator d.representation ⊤
          (Subgroup.zpowers t) ∧
      Module.finrank (ZMod 2) (fixedSpace (linearAction d t)) = 5 := by
  exact ⟨diagonal d t ht hout, diagonal_apply d t ht hout,
    diagonal_equivariance d t ht hout, outer_fixed_eq_cyclic_fixedSpace d t ht hout,
    outer_fixed_eq_cyclic_commutator d t ht hout, fixed_finrank d t ht hout⟩

/-- H.9.2(1): the actual S₆ centralizer, nonsingular fixed line, and
natural four-dimensional commutator summand, with its intertwining map. -/
theorem lemma_H_9_2_1_decomposition (d : CoordinateAction 5)
    (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) :
    ∃ (v : fixedSpace (linearAction d t)) (e : innerCentralizer t ≃* S6)
      (η : NaturalModule ≃ₗ[ZMod 2] centralizerCommutator d t),
      quadratic (v : V) = 1 ∧
      (∀ a : innerCentralizer t, d.representation a.val v = v) ∧
      IsCompl (Submodule.span (ZMod 2) {v}) (centralizerCommutator d t) ∧
      fixedSpace (linearAction d t) = Submodule.span (ZMod 2) {(v : V)} ⊔
        Representation.BinaryOffender.subspaceCommutator d.representation
          (fixedSpace (linearAction d t)) (innerCentralizer t) ∧
      Disjoint (Submodule.span (ZMod 2) {(v : V)})
        (Representation.BinaryOffender.subspaceCommutator d.representation
          (fixedSpace (linearAction d t)) (innerCentralizer t)) ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {(v : V)}) = 1 ∧
      Module.finrank (ZMod 2) (centralizerCommutator d t) = 4 ∧
      ∀ (a : innerCentralizer t) (w : NaturalModule),
        ((η (polarAction (e a) w) : fixedSpace (linearAction d t)) : V) =
          d.representation a.val ((η w : fixedSpace (linearAction d t)) : V) := by
  simpa only [ambientCommutator_eq_subspaceCommutator] using
    outer_fixed_decomposition d t ht hout

/-- H.9.2(2): every elementary actor of rank at least five is inner. -/
theorem lemma_H_9_2_2 (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hA : 5 ≤ primeRank 2 A) : A ≤ L :=
  high_rank_inner A hA

/-- The representative in H.9.2(3) is the unipotent radical of the
parabolic at the marked Sylow-invariant three-space, using its relative two-core. -/
theorem lemma_H_9_2_3_radical :
    Module.finrank (ZMod 2) U₀ = 3 ∧
      (BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow : Subgroup G) ≤
        BinaryLinear.parabolic U₀ ∧
      A₀ = (pCore 2 (BinaryLinear.parabolic U₀)).map
        ((MulAut.conj : G →* M).comp (BinaryLinear.parabolic U₀).subtype) ∧
      IsElementaryAbelian 2 A₀ ∧ Nat.card A₀ = 64 :=
  ⟨finrank_U₀, standardSylow_preserves_U₀, radicalActor_eq_map_twoCore U₀,
    radicalActor_isElementaryAbelian U₀, radicalActor_card U₀ finrank_U₀⟩

/-- H.9.2(3): the E₆₄ subgroups are exactly the conjugates of the actual A₀. -/
theorem lemma_H_9_2_3_six (A : Subgroup M) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 64) ↔
      ∃ a : M, A.map (MulAut.conj a).toMonoidHom = A₀ :=
  elementary_card_64_iff_conjugate_radical A U₀ finrank_U₀

/-- H.9.2(3): the rank-five actors are exactly the conjugates of hyperplanes of A₀. -/
theorem lemma_H_9_2_3_five (A : Subgroup M) [IsElementaryAbelian 2 A] :
    primeRank 2 A = 5 ↔ ∃ a : M,
      A.map (MulAut.conj a).toMonoidHom ≤ A₀ ∧
      (A.map (MulAut.conj a).toMonoidHom).relIndex A₀ = 2 :=
  rank_five_iff_conjugate_hyperplane A U₀ finrank_U₀

/-- H.9.2(4): all four literal subspaces coincide with `U₀ ⊕ ann(U₀)`
and have dimension five. The hypothesis is exactly that A is a hyperplane. -/
theorem lemma_H_9_2_4 (d : CoordinateAction 5)
    (A : Subgroup M) (hA : A ≤ A₀) (hidx : A.relIndex A₀ = 2) :
    Representation.BinaryOffender.fixedSpace d.representation A =
        Representation.BinaryOffender.subspaceCommutator d.representation ⊤ A ∧
      Representation.BinaryOffender.subspaceCommutator d.representation ⊤ A =
        Representation.BinaryOffender.fixedSpace d.representation A₀ ∧
      Representation.BinaryOffender.fixedSpace d.representation A₀ =
        Representation.BinaryOffender.subspaceCommutator d.representation ⊤ A₀ ∧
      Representation.BinaryOffender.subspaceCommutator d.representation ⊤ A₀ =
        U₀.prod U₀.dualAnnihilator ∧
      Module.finrank (ZMod 2)
        (Representation.BinaryOffender.fixedSpace d.representation A) = 5 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hyperplane_radical_formulas d U₀ finrank_U₀ A hA hidx
  exact ⟨h₁, h₂, h₃, h₄,
    finrank_fixedSpace_radicalActor_hyperplane d U₀ finrank_U₀ A hA hidx⟩

/-- H.9.2(5): the full source E.3.30 core for every elementary actor of
rank at least five. Radical placement is discharged by the classification. -/
theorem lemma_H_9_2_5 (d : CoordinateAction 5)
    (A : Subgroup M) [IsElementaryAbelian 2 A] (hA : 5 ≤ primeRank 2 A) :
    ChapterE.dualGeneratedCore
      (multiplicativeAction (d.representation.comp A.subtype)) 3 = ⊤ := by
  rw [← generatedCore_subgroup, generatedCore_eq_top_of_high_rank d A hA,
    OrderIso.map_top]

end CFSG.Quasithin.ChapterH.NaturalDual.FiveActors
