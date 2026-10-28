module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Reductions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.GlobalPlacement
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.IntervalNormalizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Transport

/-!
# Uniform Held Sylow pairs and full extending actions

Exhaustive double-coset coverage places each source pair in one of the two
literal ATLAS local subgroups. Their local product calculations then give a
single conjugation carrying both pair members to an actual representative.
The representative plane equivalences exclude the extraspecial order-27 case
without automorphism realization or a normalizer-quotient bound.

In these coordinates the inner image is always the diagonal four-group. The
full extending image is monomial D8 at the pure representatives and diagonal
at the mixed representatives, including all actors exchanging local overgroups.
Full realization is the only additional premise for this classification.
The invariant axis of the inner image forces genuinely outer actors in every
irreducible extending two-group. Failure of pair reducibility selects D8.

For the interval-normalizer conclusion, conjugacy transports the proved local
calculation with its irreducibility hypothesis, relative index, embedded
O₂(O²(RS)) and O²(RS) intact. Full realization and the bound of two on the
permutation-normalizer quotient remain explicit inputs for the source owner.
All earlier conditional reductions are preserved below.

Sources: Aschbacher–Smith, printed pp.509–511, 725 and 747–748; GLS3,
Table 5.3p; Aschbacher, Overgroups of Sylow subgroups in sporadic groups
(1986). This is the retained Held branch from docs/quasithin-proof-basis.md,
not the original blanket Held exclusion in Proposition 1.3.4. The reducible
E₉-pair counterevidence to the unrestricted normalizer assertion is preserved
in the parent workspace's Scratch/HeldBranch/NormalizerScope.g and Findings.md.
The interval result retains ¬ PairReducible S R; the GAP evidence is not used
as a Lean premise. Final source assembly belongs to the parent Held module.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs

variable {S : Sylow 2 Held.He} {R : Subgroup Held.He}

/-- The pair product is proper by the certified element of order seventeen. -/
theorem pair_product_ne_top (h : PairInput S R) :
    R ⊔ (S : Subgroup Held.He) ≠ ⊤ := by
  intro he
  have hd : 17 ∣ Nat.card (R ⊔ (S : Subgroup Held.He) : Subgroup Held.He) := by
    rw [he, card_top, ← Held.orderOf_ab]
    exact _root_.orderOf_dvd_natCard _
  have hp := EvenRankTwo.product_prime_divisors h (by norm_num : Nat.Prime 17) hd
  norm_num at hp

/-- The maximal-overgroup route to global coverage, retained as a separate reduction. -/
theorem pair_maximal_overgroup (h : PairInput S R) :
    ∃ M : Subgroup Held.He, IsCoatom M ∧ ¬ 2 ∣ M.index ∧
      R ≤ M ∧ (S : Subgroup Held.He) ≤ M ∧ 9 ∣ Nat.card M := by
  obtain ⟨M, hM, hle⟩ :=
    (eq_top_or_exists_le_coatom (R ⊔ (S : Subgroup Held.He))).resolve_left
      (pair_product_ne_top h)
  have hSM : (S : Subgroup Held.He) ≤ M := le_sup_right.trans hle
  have hRM : R ≤ M := le_sup_left.trans hle
  have hodd : ¬ 2 ∣ M.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le hSM))
  have hR : 9 ∣ Nat.card R := by
    rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> norm_num
  exact ⟨M, hM, hodd, hRM, hSM, hR.trans (card_dvd_of_le hRM)⟩

/-- The alternative maximal-overgroup route, with its coverage premise explicit.
The unconditional direct pair placement is exported from GlobalPlacement. -/
theorem pair_local_placement_of_maximal_cover
    (hcover : ∀ M : Subgroup Held.He, IsCoatom M → ¬ 2 ∣ M.index →
      9 ∣ Nat.card M → ∃ (i : Bool) (g : Held.He),
        M.map (MulAut.conj g).toMonoidHom = Held.LocalPairs.PairCoverage.localOvergroup i)
    (h : PairInput S R) :
    ∃ (i : Bool) (g : Held.He),
      (R ⊔ (S : Subgroup Held.He)).map (MulAut.conj g).toMonoidHom ≤
        Held.LocalPairs.PairCoverage.localOvergroup i := by
  obtain ⟨M, hM, hodd, hRM, hSM, hnine⟩ := pair_maximal_overgroup h
  obtain ⟨i, g, hg⟩ := hcover M hM hodd hnine
  exact ⟨i, g, hg ▸ map_mono (sup_le hRM hSM)⟩

/-- Transport any local plane calculation through an actual pair placement.
The unconditional assembly is `plane` below. -/
theorem plane_of_local_placement
    (hlocal : ∀ (i : Bool) (T : Sylow 2 Held.He) (P : Subgroup Held.He),
      PairInput T P → P ⊔ (T : Subgroup Held.He) ≤
        Held.LocalPairs.PairCoverage.localOvergroup i → Nonempty (P ≃* Plane 3))
    (h : PairInput S R) (i : Bool) (g : Held.He)
    (hplace : (R ⊔ (S : Subgroup Held.He)).map (MulAut.conj g).toMonoidHom ≤
      Held.LocalPairs.PairCoverage.localOvergroup i) : Nonempty (R ≃* Plane 3) := by
  let e := MulAut.conj g
  have hp := pairInput_of_equiv h e
  have hle : R.map e.toMonoidHom ⊔
      ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 Held.He) :
        Subgroup Held.He) ≤ Held.LocalPairs.PairCoverage.localOvergroup i := by
    change R.map e.toMonoidHom ⊔ (S : Subgroup Held.He).map e.toMonoidHom ≤ _
    simpa only [Subgroup.map_sup] using hplace
  obtain ⟨f⟩ := hlocal i _ _ hp hle
  exact ⟨(e.subgroupMap R).trans f⟩

/-- PairInput supplies all hypotheses for the relative-normal-closure computation. -/
theorem pair_residual_eq_normalClosure (h : PairInput S R) :
    Held.LocalPairs.residual S R =
      (normalClosure (R.subgroupOf (R ⊔ (S : Subgroup Held.He)) :
        Set (R ⊔ (S : Subgroup Held.He) : Subgroup Held.He))).map
          (R ⊔ (S : Subgroup Held.He)).subtype := by
  apply Held.LocalPairs.residual_eq_normalClosure _ _ S.isPGroup'
  rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> norm_num

/-- The general outer-actor reduction with inner-action reducibility explicit.
The uniform `exists_outer_actor_of_pair_irreducible` below supplies that premise. -/
theorem exists_outer_actor_of_irreducible
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (S R : Subgroup Held.He) (D : Subgroup (MulAut R))
    (hD : D ≤ pairAutomizer S R) (hDtwo : IsPGroup 2 D)
    (hI : ∀ A : Subgroup (R ⧸ frattini R),
      (∀ b ∈ D, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A) → A = ⊥ ∨ A = ⊤)
    (hinner : ∀ E : Subgroup (MulAut R), E ≤ (innerPairAction S R).range →
      IsPGroup 2 E → ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
        ∀ b ∈ E, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A) :
    ∃ a : Held.LocalPairs.permutationPairStabilizer S R,
      Held.LocalPairs.permutationPairAction S R a ∈ D ∧
      a.val.val ∉ Held.permutationGroup := by
  apply exists_outer_actor_of_not_le_inner hrealize S R D hD
  intro hle
  obtain ⟨A, hAb, hAt, hA⟩ := hinner D hle hDtwo
  exact (hI A hA).elim hAb hAt

open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages

/-- Every source Held pair is simultaneously conjugate to an actual representative. -/
theorem pair_conjugate (h : PairInput S R) :
    ∃ (i : Bool) (j : Fin 2) (g : Held.He),
      (S : Subgroup Held.He).map (MulAut.conj g).toMonoidHom = candidateTwo i j ∧
      R.map (MulAut.conj g).toMonoidHom = candidateOdd i j := by
  obtain ⟨i, g, hplace⟩ := pair_local_placement h
  let e := MulAut.conj g
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := R.map e.toMonoidHom
  have hp : PairInput T P := pairInput_of_equiv h e
  have hle : P ⊔ (T : Subgroup Held.He) ≤ localOvergroup i := by
    change R.map e.toMonoidHom ⊔ (S : Subgroup Held.He).map e.toMonoidHom ≤ _
    simpa only [Subgroup.map_sup] using hplace
  obtain ⟨j, a, _, hT, hP⟩ := LocalActions.pair_conjugate i T P hp hle
  refine ⟨i, j, a * g, ?_, ?_⟩
  · change ((S : Subgroup Held.He).map e.toMonoidHom).map
      (MulAut.conj a).toMonoidHom = candidateTwo i j at hT
    rw [map_map] at hT
    exact hT
  · change (R.map e.toMonoidHom).map
      (MulAut.conj a).toMonoidHom = candidateOdd i j at hP
    rw [map_map] at hP
    exact hP

/-- The odd complement of every source Held pair is a ternary elementary plane. -/
theorem plane (h : PairInput S R) : Nonempty (R ≃* Plane 3) := by
  obtain ⟨i, j, g, _, hR⟩ := pair_conjugate h
  exact ⟨LocalActions.conjugatePlaneEquiv R i j g hR⟩

/-- The extraspecial order-27 alternative is excluded uniformly. -/
theorem pair_card_nine (h : PairInput S R) : Nat.card R = 9 := by
  obtain ⟨i, j, g, _, hR⟩ := pair_conjugate h
  calc
    Nat.card R = Nat.card (candidateOdd i j) :=
      Nat.card_congr (LocalActions.conjugateOddEquiv R i j g hR).toEquiv
    _ = 9 := (Exhaustion.candidateOrders i j).2.1

/-- Exhaustive representatives with the full inner and extending images in
the plane coordinates induced by the same actual conjugation. -/
theorem pair_images
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (h : PairInput S R) :
    ∃ (i : Bool) (j : Fin 2) (g : Held.He),
      (S : Subgroup Held.He).map (MulAut.conj g).toMonoidHom = candidateTwo i j ∧
      ∃ hR : R.map (MulAut.conj g).toMonoidHom = candidateOdd i j,
        ((innerPairAction S R).range).map
            (MulAut.congr (LocalActions.conjugatePlaneEquiv R i j g hR)).toMonoidHom =
          diagonal ∧
        (pairAutomizer S R).map
            (MulAut.congr (LocalActions.conjugatePlaneEquiv R i j g hR)).toMonoidHom =
          (if j = 0 then monomial else diagonal) ∧
        (planeAction S R (LocalActions.conjugatePlaneEquiv R i j g hR)).range =
          if j = 0 then monomial else diagonal := by
  obtain ⟨i, j, g, hS, hR⟩ := pair_conjugate h
  have hfull := LocalActions.full_image_of_conjugate hrealize S R i j g hS hR
  refine ⟨i, j, g, hS, hR,
    LocalActions.inner_image_of_conjugate S R i j g hS hR, hfull, ?_⟩
  rw [planeAction_range hrealize]
  exact hfull

/-- The inner image is always the diagonal four-group, without a realization premise. -/
theorem inner_coordinates (h : PairInput S R) :
    ∃ e : R ≃* Plane 3,
      ((innerPairAction S R).range).map (MulAut.congr e).toMonoidHom = diagonal := by
  obtain ⟨i, j, g, hS, hR⟩ := pair_conjugate h
  exact ⟨LocalActions.conjugatePlaneEquiv R i j g hR,
    LocalActions.inner_image_of_conjugate S R i j g hS hR⟩

/-- The full extending images are the diagonal four-group and the monomial D8. -/
theorem full_action
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (h : PairInput S R) :
    ∃ e : R ≃* Plane 3,
      ((innerPairAction S R).range).map (MulAut.congr e).toMonoidHom = diagonal ∧
      ((planeAction S R e).range = diagonal ∨ (planeAction S R e).range = monomial) := by
  obtain ⟨e, he⟩ := inner_coordinates h
  exact ⟨e, he, LocalActions.full_action_of_inner_diagonal hrealize S R e he⟩

/-- Failure of pair reducibility selects the monomial full image. -/
theorem full_action_of_not_pairReducible
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (h : PairInput S R) (hI : ¬ PairReducible (S : Subgroup Held.He) R) :
    ∃ e : R ≃* Plane 3,
      ((innerPairAction S R).range).map (MulAut.congr e).toMonoidHom = diagonal ∧
      (pairAutomizer S R).map (MulAut.congr e).toMonoidHom = monomial ∧
      (planeAction S R e).range = monomial := by
  obtain ⟨e, he, hd | hm⟩ := full_action hrealize h
  · have hf := (planeAction_range hrealize S R e).symm.trans hd
    exact (hI (fun D hD _ =>
      LocalActions.invariant_of_diagonal e D ((map_mono hD).trans hf.le))).elim
  · exact ⟨e, he, (planeAction_range hrealize S R e).symm.trans hm, hm⟩

/-- Every subgroup of the inner image preserves a proper nonzero subgroup
of the actual Frattini quotient. In particular this holds for every two-subgroup. -/
theorem inner_invariant (h : PairInput S R)
    (E : Subgroup (MulAut R)) (hE : E ≤ (innerPairAction S R).range) :
    ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ b ∈ E, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A := by
  obtain ⟨e, he⟩ := inner_coordinates h
  exact LocalActions.inner_invariant_of_diagonal S R e he.le E hE

/-- An irreducible extending two-group contains the restriction of a genuinely
outer permutation actor preserving the original pair. -/
theorem exists_outer_actor_of_pair_irreducible
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (h : PairInput S R) (D : Subgroup (MulAut R))
    (hD : D ≤ pairAutomizer S R) (hDtwo : IsPGroup 2 D)
    (hI : ∀ A : Subgroup (R ⧸ frattini R),
      (∀ b ∈ D, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A) → A = ⊥ ∨ A = ⊤) :
    ∃ a : Held.LocalPairs.permutationPairStabilizer S R,
      Held.LocalPairs.permutationPairAction S R a ∈ D ∧
      a.val.val ∉ Held.permutationGroup := by
  exact exists_outer_actor_of_irreducible hrealize S R D hD hDtwo hI
    (fun E hE _ => inner_invariant h E hE)

/-- The source's failure of pair reducibility supplies an outer pair actor. -/
theorem exists_outer_pair_actor
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (h : PairInput S R) (hI : ¬ PairReducible (S : Subgroup Held.He) R) :
    ∃ a : Held.LocalPairs.permutationPairStabilizer S R,
      a.val.val ∉ Held.permutationGroup := by
  exact exists_outer_pair_actor_of_not_pairReducible hrealize S R hI
    (fun E hE _ => inner_invariant h E hE)

/-- Under irreducibility, every full automorphism normalizer in the two-core
interval preserves the relative two-residual. -/
theorem intervalNormalizer
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (h : PairInput S R) (hI : ¬ PairReducible (S : Subgroup Held.He) R)
    (R2 : Subgroup Held.He) (hQR2 : Held.LocalPairs.twoCore S R ≤ R2)
    (hR2S : R2 ≤ S) (hindex : R2.relIndex S ≤ 2) :
    Held.LocalPairs.automorphismNormalizer R2 ≤
      Held.LocalPairs.automorphismNormalizer (Held.LocalPairs.residual S R) := by
  obtain ⟨i, g, hplace⟩ := pair_local_placement h
  let e := MulAut.conj g
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := R.map e.toMonoidHom
  have hp : PairInput T P := pairInput_of_equiv h e
  have hle : P ⊔ (T : Subgroup Held.He) ≤ localOvergroup i := by
    change R.map e.toMonoidHom ⊔ (S : Subgroup Held.He).map e.toMonoidHom ≤ _
    simpa only [Subgroup.map_sup] using hplace
  have hI' : ¬ PairReducible (T : Subgroup Held.He) P :=
    fun hr => hI (SporadicActions.pairReducible_of_map e S R hr)
  exact Held.LocalPairs.PairCoverage.IntervalNormalizer.automorphismNormalizer_interval_le_of_map
    S R e (intervalNormalizer_of_local_placement hrealize hbound i T P hp hle hI')
    R2 hQR2 hR2S hindex

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
