module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.Symplectic
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.SmallCodimension
public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Binary

/-!
# The complete symplectic row of B.5.13

Let U be the moved space of the literal dual and U/C its natural
Sp₄(2ⁿ) section. The universal central cover gives dim U ≤ 5n and
dim C ≤ n. Choose a quadratic offender A on the dual. If its natural
fixed codimension is at least 2n, quadraticity places its commutator
inside the fixed part of U, giving the required dual bound. Otherwise
natural root geometry bounds the rank of A by n. The offender inequality
then forces equality of the fixed codimensions on the whole space and U;
the resulting fixed supplement bounds the commutator by n + dim C ≤ 2n.

The source wrapper excludes outer extensions by dimension and the binary
full symplectic group by its nonperfectness. It applies to the actual
source section, including every trivial top quotient, without assuming
a fixed supplement or a six-dimensional envelope.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.13,
printed pp.110–112, using the central-cover calculation of I.1.5–6, p.408.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour

namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem large_card (F : BinaryField) (hF : 1 < F.degree) : 2 < Nat.card F.Carrier := by
  rw [F.card_eq]
  exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hF

omit [Finite G] in
private theorem symplectic_moved_dimension_bound
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F)) :
    Module.finrank (ZMod 2) s.space.toSubmodule ≤ 5*F.degree := by
  have hcard := large_card F hF
  have hall (g : Sp F.Carrier) : g ∈ commutator (Sp F.Carrier) := by
    rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard]
    trivial
  let f : SymplecticFourOrthogonalCover.L (K := F.Carrier) →* G :=
    L.subtype.comp (e.groupEquiv.symm.toMonoidHom.comp (commutator (Sp F.Carrier)).subtype)
  let σ := s.space.toRepresentation.comp f
  let p := e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  let P : Representation.IntertwiningMap σ
      (SymplecticFourOrthogonalCover.binaryNatural (K := F.Carrier)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
      change e.linearEquiv ((s.action.comp L.subtype) (e.groupEquiv.symm g.val)
        (s.central.toSubmodule.mkQ v)) = _
      rw [e.intertwines, e.groupEquiv.apply_symm_apply]
      rfl)
  have hP : IsCover P := by
    refine ⟨e.linearEquiv.surjective.comp (Submodule.mkQ_surjective _), ?_, ?_⟩
    · intro v hv g
      have hz : s.central.toSubmodule.mkQ v = 0 :=
        e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
      have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
      rw [s.central_eq] at hm
      exact hm (e.groupEquiv.symm g.val)
    · have hm : s.space.toSubmodule ≤ (Coinvariants.ker σ).map s.space.toSubmodule.subtype := by
        conv_lhs => rw [← hi.choose_spec.1]
        apply Submodule.span_le.mpr
        rintro _ ⟨g, hg, v, hv, rfl⟩
        let a : L := ⟨g, hg⟩
        let b : SymplecticFourOrthogonalCover.L (K := F.Carrier) :=
          ⟨e.groupEquiv a, hall _⟩
        refine ⟨σ b ⟨v, hv⟩ - ⟨v, hv⟩, Coinvariants.sub_mem_ker _ _, ?_⟩
        change ρ (e.groupEquiv.symm (e.groupEquiv a)) v - v = ρ g v - v
        rw [e.groupEquiv.symm_apply_apply]
      apply top_unique
      intro v _
      obtain ⟨w, hw, he⟩ := hm v.property
      rwa [show w = v from Subtype.ext he] at hw
  obtain ⟨q, hq, _⟩ := SymplecticFourOrthogonalCover.exists_cover_quotient P hP
  have hd := LinearMap.finrank_le_finrank_of_surjective hq
  rw [← Module.finrank_mul_finrank (ZMod 2) F.Carrier
      (SymplecticFourOrthogonalCover.Space (K := F.Carrier)),
    SymplecticFourOrthogonalCover.space_finrank,
    SymplecticConjugatePair.coefficient_finrank F.card_eq, Nat.mul_comm] at hd
  exact hd

private theorem natural_dual_codim (F : BinaryField) (hF : 1 < F.degree)
    (A : Subgroup (Sp F.Carrier)) :
    fixedCodim (binarySymplectic F).dual A = fixedCodim (binarySymplectic F) A := by
  let E := SymplecticFourOrthogonalCover.binarySelfDual (K := F.Carrier)
  have he : ∀ g v, E (binarySymplectic F g v) = (binarySymplectic F).dual g (E v) := by
    intro g v
    have hg : g ∈ commutator (Sp F.Carrier) := by
      rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top (large_card F hF)]
      trivial
    exact SymplecticFourOrthogonalCover.binarySelfDual_equivariant ⟨g, hg⟩ v
  have hd := fixedCodim_map_equivariant (binarySymplectic F) (binarySymplectic F).dual
    (MonoidHom.id _) E he A
  simpa only [Subgroup.map_id] using hd.symm

omit [Finite G] in
private theorem action_dual_codim {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv σ (binarySymplectic F)) (A : Subgroup G) :
    fixedCodim σ.dual A = fixedCodim σ A := by
  let E := e.linearEquiv.symm.dualMap
  have he : ∀ g f, E (σ.dual g f) = (binarySymplectic F).dual (e.groupEquiv g) (E f) := by
    intro g f
    apply LinearMap.ext
    intro w
    change f (σ g⁻¹ (e.linearEquiv.symm w)) =
      f (e.linearEquiv.symm (binarySymplectic F ((e.groupEquiv g)⁻¹) w))
    congr 1
    apply e.linearEquiv.injective
    rw [e.intertwines, e.linearEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply, map_inv]
  rw [fixedCodim_map_equivariant σ.dual (binarySymplectic F).dual
    e.groupEquiv.toMonoidHom E he A, natural_dual_codim F hF]
  exact (fixedCodim_map_equivariant σ (binarySymplectic F)
    e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines A).symm

omit [Finite G] in
private theorem section_commutator_bound (s : MovedSection ρ L) (A : Subgroup G) :
    Module.finrank (ZMod 2) (Coinvariants.ker (s.space.toRepresentation.comp A.subtype)) ≤
      Module.finrank (ZMod 2) (Coinvariants.ker (s.action.comp A.subtype)) +
        Module.finrank (ZMod 2) s.central.toSubmodule := by
  let q : Representation.IntertwiningMap (s.space.toRepresentation.comp A.subtype)
      (s.action.comp A.subtype) :=
    s.central.toSubmodule.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
  let C := Coinvariants.ker (s.space.toRepresentation.comp A.subtype)
  have hm := map_coinvariants_of_surjective q (Submodule.mkQ_surjective _)
  have hr : Module.finrank (ZMod 2) (C.map q.toLinearMap) +
      Module.finrank (ZMod 2) (C ⊓ q.toLinearMap.ker : Submodule (ZMod 2) s.space.toSubmodule) =
      Module.finrank (ZMod 2) C := by
    have ht := (q.toLinearMap.domRestrict C).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at ht
    rw [← C.map_comap_subtype q.toLinearMap.ker, Submodule.finrank_map_subtype_eq]
    exact ht
  have hker : q.toLinearMap.ker = s.central.toSubmodule := Submodule.ker_mkQ _
  have hk := Submodule.finrank_mono (show C ⊓ q.toLinearMap.ker ≤ q.toLinearMap.ker from inf_le_right)
  rw [hker] at hk hr
  change Module.finrank (ZMod 2) ((Coinvariants.ker _).map q.toLinearMap) + _ = _ at hr
  rw [hm] at hr
  dsimp only [C] at hk hr
  omega

/-- The whole symplectic actor satisfies B.5.13 even with a trivial top quotient. -/
theorem quadraticRatio_le_two_of_symplectic_whole
    (s : MovedSection ρ.dual (⊤ : Subgroup G))
    (hi : IsIrrPlus ρ.dual ⊤ s.space.toSubmodule)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (s.action.comp (⊤ : Subgroup G).subtype) (binarySymplectic F))
    (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  let e' : ActionEquiv s.action (binarySymplectic F) :=
    ⟨Subgroup.topEquiv.symm.trans e.groupEquiv, e.linearEquiv,
      fun g v => e.intertwines ⟨g, mem_top g⟩ v⟩
  have hdimW := e.linearEquiv.finrank_eq.trans (SymplecticConjugatePair.finrank_vector F.card_eq)
  let : AddCommGroup s.space.toSubmodule := s.space.toSubmodule.addCommGroup
  let : Module (ZMod 2) s.space.toSubmodule := s.space.toSubmodule.module
  have hdimU := symplectic_moved_dimension_bound s hi F hF e
  have hdim := s.central.toSubmodule.finrank_quotient_add_finrank
  have hdimC : Module.finrank (ZMod 2) s.central.toSubmodule ≤ F.degree := by omega
  obtain ⟨A, hA⟩ := hff
  obtain ⟨A, _, hm, hquad, _⟩ := hA.exists_quadratic_minimalBestOffender ρ.dual
  have ho := hm.1.isOffender ρ.dual
  have hcodU := fixedCodim_subrepresentation_le ρ.dual s.space A
  have hcodW := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
  change fixedCodim s.action A + _ ≤ _ at hcodW
  let B := A.map e'.groupEquiv.toMonoidHom
  have hsec : fixedCodim s.action A ≤ fixedCodim ρ.dual A := by omega
  have hB : IsOffender (binarySymplectic F) B :=
    (show IsOffender s.action A from ⟨ho.1, hsec.trans ho.2⟩).map_equivariant s.action
      (binarySymplectic F) e'.groupEquiv.toMonoidHom e'.groupEquiv.injective
      e'.linearEquiv e'.intertwines
  have hc : fixedCodim s.action A = fixedCodim (binarySymplectic F) B :=
    fixedCodim_map_equivariant _ _ e'.groupEquiv.toMonoidHom e'.linearEquiv e'.intertwines A
  have hr : rank B = rank A := rank_map_injective e'.groupEquiv.toMonoidHom e'.groupEquiv.injective A
  have hlo : F.degree ≤ fixedCodim s.action A := by
    rw [hc]
    exact SymplecticConjugatePair.NaturalBounds.natural_fixedCodim_lower F.card_eq hB.1.1
  apply (quadraticRatio_le_two_iff ρ).mpr
  refine ⟨A, ho.1, (isQuadratic_dual_iff ρ A).mp hquad, ?_⟩
  by_cases hlarge : 2*F.degree ≤ fixedCodim s.action A
  · have hle : subspaceCommutator ρ.dual ⊤ A ≤
        s.space.toSubmodule ⊓ fixedSpace ρ.dual A := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, v, _, rfl⟩
      refine ⟨?_, fun b => hquad b b.property a ha v⟩
      rw [s.space_eq]
      exact Submodule.subset_span ⟨a, mem_top a, v, Submodule.mem_top, rfl⟩
    have hb := Submodule.finrank_mono hle
    rw [← (subrepresentationFixedEquiv ρ.dual s.space A).finrank_eq] at hb
    have hfix := fixedCodim_add_finrank s.space.toRepresentation A
    have hdual : fixedCodim ρ A =
        Module.finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ A) := by
      rw [subspaceCommutator_top_eq_coinvariants]
      exact finrank_quotient_invariants_eq_dual_commutator (ρ.comp A.subtype)
    have hoff := ho.2
    omega
  · have hrsmall : rank A ≤ F.degree := by
      rw [← hr]
      exact SymplecticConjugatePair.NaturalBounds.natural_small_codim_rank_le
        F.card_eq F.degree_pos hB.1 (by
          change fixedCodim (binarySymplectic F) B < 2 * F.degree
          rw [← hc]
          omega)
    have hoff := ho.2
    have hs := (fixedCodim_subrepresentation_eq_iff ρ.dual s.space A).mp (by omega)
    have hb := section_commutator_bound s A
    have hd : fixedCodim s.action.dual A = fixedCodim s.action A :=
      action_dual_codim s.action F hF e' A
    have hd' : fixedCodim s.space.toRepresentation.dual A ≤
        fixedCodim s.action A + Module.finrank (ZMod 2) s.central.toSubmodule := by
      change Module.finrank (ZMod 2) (Module.Dual (ZMod 2) _ ⧸
        Representation.invariants (Representation.dual (s.space.toRepresentation.comp A.subtype))) ≤ _
      rw [finrank_dual_quotient_invariants]
      have he : fixedCodim s.action.dual A =
          Module.finrank (ZMod 2) (Coinvariants.ker (s.action.comp A.subtype)) :=
        finrank_dual_quotient_invariants (s.action.comp A.subtype)
      rw [← he, hd] at hb
      exact hb
    have he := dual_fixedCodim_eq_of_fixed_supplement ρ.dual s.space A hs
    have hbi : fixedCodim ρ.dual.dual A = fixedCodim ρ A := by
      rw [fixedCodim_dual_eq_moved_finrank, subspaceCommutator_top_eq_coinvariants]
      exact (finrank_quotient_invariants_eq_dual_commutator (ρ.comp A.subtype)).symm
    omega

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem symplectic_source_eq_top
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (c.sectionData.action.comp L.subtype) (binarySymplectic F)) :
    L = ⊤ := by
  have hext : L = ⊤ ∨ OuterNaturalAction c.sectionData.action := by
    cases c.clause_one with
    | irreducible _ _ _ _ he => exact he.imp_right And.right
    | doubleThree _ hL _ _ _ => exact Or.inl hL
    | naturalDual _ _ hL _ => exact Or.inl hL
    | repeatedNatural _ _ _ _ _ hL _ => exact Or.inl hL
  rcases hext with hL | hext
  · exact hL
  have hdim := e.linearEquiv.finrank_eq.trans
    (SymplecticConjugatePair.finrank_vector F.card_eq)
  rcases hext with ⟨n, hn5, hn8, ⟨en⟩⟩ | ⟨eg⟩
  · have hd := en.linearEquiv.finrank_eq
    have hb : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin n)) =
        if n = 5 ∨ n = 6 then 4 else 6 := by
      interval_cases n <;>
        first
        | simpa using BinaryPermutation.finrank_natural_odd (Fin _) (by decide)
        | simpa using BinaryPermutation.finrank_natural_even (Fin _) (by decide)
    split_ifs at hb <;> omega
  · obtain ⟨eg⟩ := eg
    have hd := eg.linearEquiv.finrank_eq
    rw [Atlas.G2.Natural.finrank_space] at hd
    omega

/-- The corrected source conclusion makes the large symplectic component the
whole actor; the numerical argument handles every trivial top extension. -/
theorem quadraticRatio_le_two_of_large_symplectic_source
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (c.sectionData.action.comp L.subtype) (binarySymplectic F))
    (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  have hL := symplectic_source_eq_top c F hF e
  subst L
  exact quadraticRatio_le_two_of_symplectic_whole c.sectionData (c.clause_two hn).1 F hF e hff

omit [Finite G] in
private theorem symplectic_degree_gt_one
    [Theory.GroupTheory.IsQuasisimple L] (F : BinaryField) (e : L ≃* Sp F.Carrier) :
    1 < F.degree := by
  by_contra hn
  have hdeg : F.degree = 1 := by have := F.degree_pos; omega
  have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq, hdeg]; norm_num
  let : Group.IsPerfect (Sp F.Carrier) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply SymplecticFourOrthogonalCover.Roots.card_two_root_not_mem_derived hc
  rw [Group.IsPerfect.commutator_eq_top]
  trivial

/-- The entire symplectic nonsplit source row, including exclusion of the
nonperfect binary full group. No supplement or extension witness is assumed. -/
theorem quadraticRatio_le_two_of_symplectic_source
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hq : Theory.GroupTheory.IsQuasisimple (generalizedFitting G))
    (hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (F : BinaryField)
    (e : ActionEquiv (c.sectionData.action.comp L.subtype) (binarySymplectic F))
    (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  let : Theory.GroupTheory.IsQuasisimple L := c.fitting_eq.symm ▸ hq
  exact quadraticRatio_le_two_of_large_symplectic_source c hn F
    (symplectic_degree_gt_one F e.groupEquiv) e hff

end CFSG.Quasithin.ChapterB.SourceB513
