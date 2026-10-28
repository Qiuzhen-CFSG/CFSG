module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Nonopposite.PolynomialTransfer
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Triangular
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Weyl

/-!
# Simultaneous Weyl transport of short-root exchanges

A simple carrier representative conjugates both root groups with parameter
unchanged in characteristic two. It also preserves short roots and the two
geometric correction formulas. Thus a common Weyl word transports the entire
exchange identity. Every independent root pair belongs to a positive system;
Weyl transitivity on bases supplies such a word carrying both roots positive.

Source: Steinberg, Representations of Algebraic Groups (1963), §§2,4,10.
-/

public section
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.SpanInvariance.Nonopposite
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
local instance nonoppositeRootRelationsTransportNeg : InvolutiveNeg F4Chevalley.Root :=
  typeF4RootPairing.indexNeg

/-- Simultaneous reflection transports the full carrier identity, including
its quadratic correction and its zero-correction alternative. -/
theorem ShortRootExchange.simple_reflection {r s : F4Chevalley.Root}
    (h : ShortRootExchange (F := F) r s) (i : Fin 4) :
    ShortRootExchange (F := F)
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r)
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) s) := by
  let C := MulAut.conj (algebraicNElement (F := F) (typeF4SimpleRootIndex i) 1)
  have hc (u : F4Chevalley.Root) (a : F) :
      C (algebraicRootElement u a) =
        algebraicRootElement (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) u) a :=
    EndNode.n_root_conjugation i u a
  rcases h with h | ⟨t, d, q, ht, hsum, htop, he⟩
  · left
    intro a b
    have hh : Commute (C (algebraicRootElement r a)) (C (algebraicRootElement s b)) :=
      (h a b).map C.toMonoidHom
    simpa only [hc] using hh
  · refine Or.inr ⟨typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) t,
      typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) d, q,
      (WordRelations.ShortOperators.isShortRoot_reflection _ _).mpr ht, ?_, ?_, ?_⟩
    · simp only [RootPairing.root_reflectionPerm, hsum, map_add]
    · rcases htop with hq | hd
      · exact Or.inl hq
      · right
        simp only [RootPairing.root_reflectionPerm, hd, map_add, map_nsmul]
    · intro a b
      simpa only [map_mul, hc] using congrArg C (he a b)

/-- Reflection invariance is an equivalence because the root reflection is
involutive. -/
theorem shortRootExchange_simple_reflection_iff (r s : F4Chevalley.Root) (i : Fin 4) :
    ShortRootExchange (F := F)
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r)
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) s) ↔
    ShortRootExchange (F := F) r s := by
  constructor
  · intro h
    simpa only [RootPairing.reflectionPerm_self] using h.simple_reflection i
  · exact fun h => h.simple_reflection i

/-- A common word transports the entire exchange without changing parameters. -/
theorem shortRootExchange_word_iff (w : List typeF4RootPairing_base.support)
    (r s : F4Chevalley.Root) :
    ShortRootExchange (F := F) (reflectionWord w r) (reflectionWord w s) ↔
      ShortRootExchange (F := F) r s := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
    simp only [reflectionWord, typeF4RootPairing_baseEquiv_val,
      shortRootExchange_simple_reflection_iff, ih]

/-- An independent pair has a common word taking it into the fixed positive
system; this is a statement about the actual root action. -/
theorem exists_common_positive_word (r s : F4Chevalley.Root)
    (hli : LinearIndependent ℝ ![typeF4RootPairing.root r, typeF4RootPairing.root s]) :
    ∃ w : List typeF4RootPairing_base.support,
      typeF4RootPairing_base.IsPos (reflectionWord w r) ∧
      typeF4RootPairing_base.IsPos (reflectionWord w s) := by
  obtain ⟨S, hr, hs⟩ :=
    positiveSubsystem_contains_linearIndependent_pair_of_reducedCrystallographic
      typeF4RootPairing hli
  obtain ⟨g, hg⟩ := exists_weylGroup_translate_base_toPositiveSubsystem
    typeF4RootPairing typeF4RootPairing_base S
  have hp (u : F4Chevalley.Root) (hu : u ∈ S) :
      typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm g⁻¹ u) := by
    have hh : (g • typeF4RootPairing_base).IsPos u := by
      rw [← RootPairing.Base.mem_toPositiveSubsystem, hg]
      exact hu
    change (RootPairing.Base.mapAut g.val typeF4RootPairing_base).IsPos u at hh
    rw [RootPairing.Base.isPos_mapAut_iff] at hh
    exact hh
  obtain ⟨w, hw⟩ := typeF4RootPairing_base.exists_wordProd_eq g⁻¹
  exact ⟨w, by simpa only [reflectionWord_eq_weylGroupToPerm, hw] using hp r hr,
    by simpa only [reflectionWord_eq_weylGroupToPerm, hw] using hp s hs⟩

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.SpanInvariance.Nonopposite
