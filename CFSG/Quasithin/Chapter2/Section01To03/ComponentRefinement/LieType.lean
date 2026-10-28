module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Endpoints
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.SourceCases
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Triality
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Lie-type calculations for component refinement

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 2.3.9(7), printed pp.525–526, using 1.1.5(3)(a–c).

The concrete relative-block calculations exclude G₂ and its central two-covers,
³D₄, ²F₄, the Tits group, and L₅(2). They construct invariant parabolics and
their overgroups with S, then use the actual subnormal blocks and their
conjugation modules to contradict `LocalBlockGeneration`. The Ree construction
input is discharged by the canonical exceptional endomorphism. The L₄(2)
calculation gives both nontrivial Dynkin action and the projection-centralizer
intersection.

We assemble these results against the actual Theorem C catalogue. Field
transport identifies any order-two coefficient field with `ZMod 2`. For
symplectic groups in larger characteristic-two fields, the central quotient
and derived-group inclusions are isomorphisms. At the binary endpoint the
checked polar representation identifies the projective derived carrier with
A₆, and hence with the full symplectic derived carrier. All central two-covers
and the triple A₆ cover are retained exactly as in the source.

The input list is Theorem C, A.2.3(3–4), not Theorem B: it excludes U₄
and U₅. The invariant parabolics on p.526 are invariant under N_S(L);
`LocalSetup` does not assert that all of S normalizes L. Their local
overgroups are constructed inside ⟨L,S⟩ with this distinction preserved.
`refinement_of_not_bender` proves precisely alternatives (b) or (g) from
the model/action consequences of 1.1.5(3)(a–c) outside the Bender branch.
`refinement` also propagates the Bender-model witness for the parent, which
retains the other source cases and the complete 2.3.9(7) assembly.

Maximality here is among invariant proper parabolics containing the relevant
Sylow intersection, as in the proof of E.2.2 on printed p.216. With graph
action this includes flag stabilizers; requiring each to be a maximal
parabolic of the group would omit the surviving L₄(2) configuration.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType

open Subgroup ClassificationModels ChapterA.Section02

private theorem derivedSymplectic_of_projective {K : Type*} [Group K]
    {f : ℕ} (hf : 2 ≤ f) (hm : ClassicalGroup.IsPSp K 2 (2 ^ f)) :
    IsDerivedSymplecticFour K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have hfour : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
    omega
  exact ⟨f, by omega, F, inferInstance, inferInstance, hF,
    ⟨(e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm).trans
      (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hlarge).symm⟩⟩

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem not_g2_full (h : LocalSetup H L M S z)
    (hinner : ∃ t : L, IsConjugationProjection L z t)
    {f : ℕ} (hf : 2 ≤ f) (hm : IsG2At L (2 ^ f)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have hfour : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
    omega
  let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect hlarge
  let d : commutator (Atlas.G2.Model F) ≃* Atlas.G2.Model F :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  exact G2.not_derived_model h hinner F f (by omega) hF ⟨e.trans d.symm⟩

/-- Every rank-two characteristic-two model of Theorem C reduces to (b).
The source supplies simplicity in 1.1.5(3)(a); all parabolic and relative-block
premises, including the canonical Ree construction, are discharged here. -/
theorem caseB_of_rankTwo (h : LocalSetup H L M S z) [IsSimpleGroup L]
    (hinner : ∃ t : L, IsConjugationProjection L z t)
    {f : ℕ} (hm : IsTheoremCRankTwoModel L f) : CaseB L := by
  cases hm with
  | linear hf iso => exact Or.inr (Or.inl ⟨f, hf, iso⟩)
  | symplectic hf iso => exact Or.inl (derivedSymplectic_of_projective hf iso)
  | g2 hf iso => exact (not_g2_full h hinner hf iso).elim
  | triality _ iso => exact (TrialityCase.not_isTrialityGroupAt_two_pow h f iso).elim
  | ree_f4 m hm _ iso => exact (Ree.not_isReeF4Model h ⟨m, hm, iso⟩).elim
  | symplectic_derived _ iso =>
      obtain ⟨e⟩ := iso
      exact Or.inl (isDerivedSymplecticFour_of_alternatingSix
        (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix))
  | g2_derived _ iso =>
      exact (G2.not_derived_model h hinner (ZMod 2) 1 (by decide) (by norm_num) iso).elim
  | tits _ iso =>
      obtain ⟨t, ht⟩ := hinner
      exact (Ree.not_tits_model h (MulAut.conj t)
        (fun x => (ht x).symm) ⟨t, rfl⟩ iso).elim

/-- The binary alternatives of Theorem C(4) reduce to the full conclusion (g).
The supplied order-two field is transported through an actual field isomorphism,
and L₅(2) is excluded by its relative parabolic blocks. -/
theorem caseG_of_binary (h : LocalSetup H L M S z)
    (hinner : ∃ t : L, IsConjugationProjection L z t)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL L n 2) :
    CaseG L M ((S : Subgroup H).map H.subtype) z := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let eL : L ≃* Binary.PSL n := e.trans (Atlas.fieldEquivPSL n eF)
  rcases hn with rfl | rfl
  · exact ⟨eL, Binary.four_refinement h eL hinner⟩
  · exact (Binary.not_five h eL hinner).elim

/-- The complete simple Lie-type case 1.1.5(3)(a). Rank-one witnesses are
passed to the parent Bender branch; all other cases give (b) or the full (g). -/
theorem refinement_of_simpleLieModel (h : LocalSetup H L M S z) [IsSimpleGroup L]
    (hinner : ∃ t : L, IsConjugationProjection L z t) (hm : SimpleLieModel L) :
    IsBenderModel L ∨ CaseB L ∨ CaseG L M ((S : Subgroup H).map H.subtype) z := by
  rcases hm with hb | ⟨f, hf⟩ | ⟨n, hn, hm⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inl (caseB_of_rankTwo h hinner hf))
  · exact Or.inr (Or.inr (caseG_of_binary h hinner hn hm))

/-- In 1.1.5(3)(b), the full central two-cover of G₂(4) is excluded.
The remaining alternative uses exactly the quotient L/O₂(L), not L/Z(L)
without a comparison or an arbitrary named quotient. -/
theorem caseB_of_centralTwoCover (h : LocalSetup H L M S z)
    (hcenter : center L = pCore 2 L) (hcore : pCore 2 L ≠ ⊥)
    (hinner : ∃ t : L, IsConjugationProjection L z t)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 ∨ IsG2At (L ⧸ pCore 2 L) 4) :
    CaseB L := by
  rcases hm with hm | ⟨F, _, _, hF, he⟩
  · exact Or.inr (Or.inr (Or.inl hm))
  · exact (G2.not_central_quotient_model h hinner hcenter hcore F hF he).elim

/-- The Lie-model calculation in 2.3.9(7), applied to the genuine model/action
consequences of 1.1.5(3)(a–c). All model-local prerequisites are discharged.
The parent retains the Bender witness and the non-Lie source alternatives. -/
theorem refinement (h : LocalSetup H L M S z) (hs : SourceModelCases L z) :
    IsBenderModel L ∨ CaseB L ∨ CaseG L M ((S : Subgroup H).map H.subtype) z := by
  cases hs with
  | simple_lie hs hm hi =>
      let := hs
      exact refinement_of_simpleLieModel h hi hm
  | central_two_cover hc hn hm hi =>
      exact Or.inr (Or.inl (caseB_of_centralTwoCover h hc hn hi hm))
  | alternating_six hm =>
      obtain ⟨e⟩ := hm
      exact Or.inr (Or.inl (Or.inl (isDerivedSymplecticFour_of_alternatingSix e)))
  | triple_six hm => exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr hm))))

/-- Once the parent removes the Bender branch, only (b) and the complete (g)
survive. The result assumes neither a block classification nor its conclusion. -/
theorem refinement_of_not_bender (h : LocalSetup H L M S z)
    (hs : SourceModelCases L z) (hb : ¬ IsBenderModel L) :
    CaseB L ∨ CaseG L M ((S : Subgroup H).map H.subtype) z :=
  (refinement h hs).resolve_left hb

/-- Direct application to the actual automorphism in 1.1.5(3)(a), with its
literal ambient conjugation identity and membership in the inner image. -/
theorem refinement_of_inner_action (h : LocalSetup H L M S z) [IsSimpleGroup L]
    (hm : SimpleLieModel L) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    IsBenderModel L ∨ CaseB L ∨ CaseG L M ((S : Subgroup H).map H.subtype) z := by
  obtain ⟨t, rfl⟩ := hinner
  exact refinement h (.simple_lie inferInstance hm ⟨t, fun x => (hα x).symm⟩)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType

end
