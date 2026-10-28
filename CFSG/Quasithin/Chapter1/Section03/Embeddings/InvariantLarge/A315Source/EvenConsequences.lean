module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.EvenModels
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceModels
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Exclusions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions

/-!
# A.3.15-free nonbinary even source branches

The actual p-subgroup B permutes with S, so B S is soluble. Concrete
Sylow control therefore places B in N_D(S ∩ D), and simultaneous Sylow/torus
coordinates give the already proved linear, G₂, triality and Ree actions.
Their Frattini orbits contradict the intrinsic irreducibility. The full
symplectic carrier instead supplies the original elementary plane, even
degree, field congruence and cyclic ambient automizer. Its proved central
cover theorem retains the whole source component Q.

Every placement and action input is discharged from the original ambient
and complement hypotheses. No raw A.3.15 Cartan configuration is required.
Source: Aschbacher–Smith A.3.15, pp.50–51, and 1.3.4, pp.510–511.
-/
public noncomputable section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {J : Type*} [Group J] [Finite J]
variable {D B : Subgroup J} [D.Normal] {S : Sylow 2 J} {p : ℕ}

/-- The nonbinary linear row is impossible for the actual intrinsic action. -/
theorem not_linear_even
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) (e : D ≃* PSL(3,F)) : False := by
  let : Fact p.Prime := ⟨hA.prime⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hN := normalizes_restriction S hA.p_group (by have := hA.large; omega)
    hA.inside hA.permutes (SolvableSylowControl.of_equiv e (linear_control hF hn))
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal D
  obtain ⟨e', heU, heB⟩ := EvenActions.Linear.SourceAlignment.exists_simultaneous_alignment F e
    (by omega) hF (by have := hA.large; omega) U (B.subgroupOf D)
    hA.p_group.comap_subtype (by rwa [hU])
  rw [hU] at heU
  obtain ⟨g, hg, hact⟩ := EvenActions.Linear.frattini_of_alignment F D B S hA.inside
    (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hF) e' heU heB
  exact hB.not_power_involution g hg hact

/-- The full symplectic row supplies all original plane, field and automizer conclusions. -/
theorem symplectic_alternative
    {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (eQ : Q ⧸ center Q ≃* D)
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hC : centralizer (D : Set J) = ⊥)
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : D ≃* Matrix.symplecticGroup (Fin 2) F) :
    Nonempty (B ≃* Plane p) ∧ SymplecticModel p Q ∧ IsCyclic (automizer S B) := by
  let : Fact p.Prime := ⟨hA.prime⟩
  have hN := normalizes_intersection S hA.p_group (by have := hA.large; omega)
    hA.inside hA.permutes (SolvableSylowControl.of_equiv e (symplectic_control hF hn))
  obtain ⟨hp, hc, hm, he⟩ := symplectic_alternative_of_normalizes hF hn hA.large D e.symm
    S B hA.inside hC hN hB.oddComplement hB.commutator
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨j, _⟩ := Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.exists_whole_model
    hF hn (eQ.trans e)
  exact ⟨hp, ⟨n, he, hm, F, inferInstance, inferInstance, hF, ⟨j⟩⟩, hc⟩

/-- The nonbinary G₂ row is impossible without any assumed Cartan placement. -/
theorem not_g2_even
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) (e : D ≃* Atlas.G2.Model F) : False := by
  let : Fact p.Prime := ⟨hA.prime⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hq : 2 < Nat.card F := by rw [hF]; exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  have hN := normalizes_restriction S hA.p_group (by have := hA.large; omega)
    hA.inside hA.permutes (SolvableSylowControl.of_equiv e (g2_control hq))
  exact hB.not_power (EvenActions.G2.Source.frattini_power_of_normalizes_sylow D e
    (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective hq) S B
    hA.inside hA.p_group (by have := hA.large; omega) hN)

/-- Genuine binary triality with degree greater than one is excluded by its actual power action. -/
theorem not_triality_even
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hna : ¬ IsMulCommutative D)
    (P : Triality.Standard.Parameters) {n : ℕ} (hn : 1 < n) (hq : P.q = 2^n)
    (e : D ≃* Triality.Standard.Carrier P) : False := by
  let : Fact p.Prime := ⟨hA.prime⟩
  let : IsSimpleGroup D := hA.simple
  have hn0 : 0 < n := by omega
  have heP := P.eq_binaryParameters_of_q_eq n hn0 hq
  subst P
  let : Group.IsPerfect D := ⟨
    (inferInstance : (commutator D).Normal).eq_bot_or_eq_top.resolve_left
      (fun h => hna ((commutator_eq_bot_iff D).mp h))⟩
  let : IsSimpleGroup (Triality.Standard.BinaryCarrier n hn0) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Triality.Standard.BinaryCarrier n hn0) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let P := Triality.Standard.binaryParameters n hn0
  have hlarge : 2 < P.q := by change 2 < 2^n; exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  have hN := normalizes_restriction S hA.p_group (by have := hA.large; omega)
    hA.inside hA.permutes (SolvableSylowControl.of_equiv e (triality_control P rfl hlarge))
  have ha := EvenActions.Triality.SourceAlignment.hasCartanAlignment_of_normalizes D B S P
    (Triality.Standard.CartanAction.borelGeometry P rfl)
    (Triality.Standard.Parabolics.unipotentSylow P rfl)
    (Triality.Standard.Parabolics.coe_unipotentSylow P rfl) e
    (by have := hA.large; omega) hA.p_group hN
  exact hB.not_power (EvenActions.Triality.frattini_power_of_alignment D B S hA.inside
    P n hn0 rfl (Triality.Standard.CartanAction.borelGeometry P rfl)
    (Triality.Standard.OuterOdd.Coverage.binary_inner_coefficient n hn0) ha)

/-- The nonbinary Ree row is excluded from the literal permuting product and action. -/
theorem not_ree_even
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hna : ¬ IsMulCommutative D)
    (m : ℕ) (hm : 1 ≤ m) (e : D ≃* ReeF4.Model m) : False := by
  let : Fact p.Prime := ⟨hA.prime⟩
  let : IsSimpleGroup D := hA.simple
  let d := ReeF4.canonicalLocalBlockInput m
  let e' := e.trans d.modelEquiv.symm
  let : Group.IsPerfect D := ⟨
    (inferInstance : (commutator D).Normal).eq_bot_or_eq_top.resolve_left
      (fun h => hna ((commutator_eq_bot_iff D).mp h))⟩
  let : IsSimpleGroup d.fixedGroup := e'.symm.isSimpleGroup
  let : Group.IsPerfect d.fixedGroup :=
    Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  have hN := normalizes_intersection S hA.p_group (by have := hA.large; omega)
    hA.inside hA.permutes (SolvableSylowControl.of_equiv e (ree_control m hm))
  exact hB.not_power (EvenActions.Ree.frattini_power_of_normalizes D B hA.fitting S
    hA.large hA.p_group hN d e (ReeF4.LocalBlockInput.inner_field hm d))
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
