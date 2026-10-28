module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Reductions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Transport
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.Residual
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Normalizer
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Candidates
public import Theory.SpecificGroups.Held.Automorphisms.Reduction

/-!
# Coordinate reductions for the local Held pair calculation

A genuine plane equivalence identifies the Frattini quotient with the plane.
The diagonal action preserves a coordinate line, so a computed containment
of the inner image in that diagonal group supplies the invariant needed by
the outer-actor argument. Full image bounds are kept separate from inner
image bounds and include every extending automorphism. Normality of the
inner image and the computed diagonal normalizer reduce the entire full
image to the diagonal/monomial alternatives once the inner image is diagonal.

These are conditional reductions for Aschbacher–Smith, printed pp.509–511,
and GLS3 Table 5.3p. The exhaustive local pair and action calculations are
still required; no source theorem is asserted from an assumed catalogue.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
namespace LocalActions

/-- Every inner actor is an extending actor of the same pair. -/
theorem innerPairAction_range_le (S R : Subgroup Held.He) :
    (innerPairAction S R).range ≤ pairAutomizer S R := by
  rintro a ⟨g, rfl⟩
  exact ⟨MulAut.conj g.val,
    (mem_automorphismPairStabilizer_iff S R _).mp g.property |>.1, fun _ => rfl⟩

/-- The inner restriction image is normal in the full pair automizer. -/
theorem pairAutomizer_le_normalizer_inner (S R : Subgroup Held.He) :
    pairAutomizer S R ≤ normalizer ((innerPairAction S R).range : Set (MulAut R)) := by
  apply le_normalizer_iff.mpr
  intro a ha c hc
  rw [← pairRestriction_range] at ha
  obtain ⟨b, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := hc
  let q : automorphismPairStabilizer S R := ⟨MulAut.conj g.val, g.property⟩
  have he : MulAut.conj (b.val g.val) = b.val * q.val * b.val⁻¹ := by
    ext x
    simp [q, MulAut.mul_apply, MulAut.conj_apply]
  have hmem : MulAut.conj (b.val g.val) ∈ automorphismPairStabilizer S R := by
    rw [he]
    exact (b * q * b⁻¹).property
  refine ⟨⟨b.val g.val, hmem⟩, ?_⟩
  change pairRestriction S R
      (actingPairMap (MulAut.conj : Held.He →* MulAut Held.He) S R ⟨b.val g.val, hmem⟩) = _
  have heq : actingPairMap (MulAut.conj : Held.He →* MulAut Held.He) S R
      ⟨b.val g.val, hmem⟩ = b * q * b⁻¹ := Subtype.ext he
  rw [heq, map_mul, map_mul, map_inv]
  rfl

/-- Transporting the normal inner restriction image bounds every extending actor.
No local-overgroup stabilizer or outer-group bound occurs in this argument. -/
theorem pairAutomizer_of_inner_diagonal (S R : Subgroup Held.He) (e : R ≃* Plane 3)
    (hinner : ((innerPairAction S R).range).map (MulAut.congr e).toMonoidHom =
      Held.LocalPairs.PairCoverage.LocalActions.diagonal) :
    (pairAutomizer S R).map (MulAut.congr e).toMonoidHom =
        Held.LocalPairs.PairCoverage.LocalActions.diagonal ∨
      (pairAutomizer S R).map (MulAut.congr e).toMonoidHom =
        Held.LocalPairs.PairCoverage.LocalActions.monomial := by
  apply Held.LocalPairs.PairCoverage.LocalActions.eq_diagonal_or_monomial
  · rw [← hinner]
    exact map_mono (innerPairAction_range_le S R)
  · have hb := map_mono (f := (MulAut.congr e).toMonoidHom)
      (pairAutomizer_le_normalizer_inner S R)
    rwa [map_equiv_normalizer_eq, hinner,
      Held.LocalPairs.PairCoverage.LocalActions.normalizer_diagonal_eq_monomial] at hb

/-- Full realization expresses the preceding classification as the range of
actual preserving permutation actors. -/
theorem full_action_of_inner_diagonal
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (S R : Subgroup Held.He) (e : R ≃* Plane 3)
    (hinner : ((innerPairAction S R).range).map (MulAut.congr e).toMonoidHom =
      Held.LocalPairs.PairCoverage.LocalActions.diagonal) :
    (planeAction S R e).range = Held.LocalPairs.PairCoverage.LocalActions.diagonal ∨
      (planeAction S R e).range = Held.LocalPairs.PairCoverage.LocalActions.monomial := by
  rw [planeAction_range hrealize]
  exact pairAutomizer_of_inner_diagonal S R e hinner

private theorem plane_frattini : frattini (Plane 3) = ⊥ := by
  let : IsElementaryAbelian 3 (Plane 3) := {
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel) }
  let : Fact (IsPGroup 3 (Plane 3)) := ⟨IsElementaryAbelian.isPGroup 3 (Plane 3)⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 3)

noncomputable def quotientPlaneEquiv {R : Subgroup Held.He} (e : R ≃* Plane 3) :
    (R ⧸ frattini R) ≃* Plane 3 :=
  (SporadicActions.frattiniEquiv e).trans
    ((QuotientGroup.quotientMulEquivOfEq plane_frattini).trans QuotientGroup.quotientBot)

theorem quotientPlaneEquiv_apply_mk {R : Subgroup Held.He} (e : R ≃* Plane 3) (x : R) :
    quotientPlaneEquiv e (QuotientGroup.mk' (frattini R) x) = e x := by
  rfl

theorem quotientPlaneEquiv_equivariant {R : Subgroup Held.He} (e : R ≃* Plane 3)
    (a : MulAut R) (x : R ⧸ frattini R) :
    quotientPlaneEquiv e (quotientAut (frattini R) a x) =
      MulAut.congr e a (quotientPlaneEquiv e x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    change quotientPlaneEquiv e
        (quotientAut (frattini R) a (QuotientGroup.mk' _ x)) =
      MulAut.congr e a (quotientPlaneEquiv e (QuotientGroup.mk' _ x))
    rw [quotientAut_apply_mk, quotientPlaneEquiv_apply_mk, quotientPlaneEquiv_apply_mk]
    change e (a x) = e (a (e.symm (e x)))
    rw [e.symm_apply_apply]

/-- Pull back a specific coordinate axis through the genuine Frattini quotient equivalence. -/
theorem invariant_of_diagonal {R : Subgroup Held.He} (e : R ≃* Plane 3)
    (E : Subgroup (MulAut R))
    (hE : E.map (MulAut.congr e).toMonoidHom ≤
      Held.LocalPairs.PairCoverage.LocalActions.diagonal) :
    ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ b ∈ E, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A := by
  let f := quotientPlaneEquiv e
  let L := Held.LocalPairs.PairCoverage.LocalActions.axis
  refine ⟨L.comap f.toMonoidHom, ?_, ?_, ?_⟩
  · intro hbot
    apply Held.LocalPairs.PairCoverage.LocalActions.axis_ne_bot
    have hh := congrArg (Subgroup.map f.toMonoidHom) hbot
    rwa [map_comap_eq_self_of_surjective f.surjective, Subgroup.map_bot] at hh
  · intro htop
    apply Held.LocalPairs.PairCoverage.LocalActions.axis_ne_top
    have hh := congrArg (Subgroup.map f.toMonoidHom) htop
    rwa [map_comap_eq_self_of_surjective f.surjective,
      map_top_of_surjective f.toMonoidHom f.surjective] at hh
  · intro b hb x hx
    change f (quotientAut (frattini R) b x) ∈ L
    rw [quotientPlaneEquiv_equivariant]
    exact Held.LocalPairs.PairCoverage.LocalActions.diagonal_preserves_axis _
      (hE ⟨b,hb,rfl⟩) (f x) hx

/-- The inner coordinate-image bound supplies the exact invariant required by
`HeldPairs.exists_outer_actor_of_irreducible`. Proving that bound for actual
Held representatives remains a separate model calculation. -/
theorem inner_invariant_of_diagonal (S R : Subgroup Held.He) (e : R ≃* Plane 3)
    (hinner : ((innerPairAction S R).range).map (MulAut.congr e).toMonoidHom ≤
      Held.LocalPairs.PairCoverage.LocalActions.diagonal)
    (E : Subgroup (MulAut R)) (hE : E ≤ (innerPairAction S R).range) :
    ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ b ∈ E, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A :=
  invariant_of_diagonal e E ((map_mono hE).trans hinner)

/-- Full image bounds leave exactly two coordinate groups, without discarding
any extending automorphism. The bounds still require the Held calculation. -/
theorem full_action_of_bounds
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (S R : Subgroup Held.He) (e : R ≃* Plane 3)
    (hD : Held.LocalPairs.PairCoverage.LocalActions.diagonal ≤
      (pairAutomizer S R).map (MulAut.congr e).toMonoidHom)
    (hM : (pairAutomizer S R).map (MulAut.congr e).toMonoidHom ≤
      Held.LocalPairs.PairCoverage.LocalActions.monomial) :
    (planeAction S R e).range = Held.LocalPairs.PairCoverage.LocalActions.diagonal ∨
      (planeAction S R e).range = Held.LocalPairs.PairCoverage.LocalActions.monomial := by
  rw [planeAction_range hrealize]
  exact Held.LocalPairs.PairCoverage.LocalActions.eq_diagonal_or_monomial _ hD hM

end LocalActions
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
