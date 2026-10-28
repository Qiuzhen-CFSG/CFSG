module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDual
public import Theory.Representation.BinaryConjugationSection.IsotropicCubic
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Closing the original natural-three constrained row

The remaining B.5.1 sections are the six-dimensional orthogonal module and
its symmetric-eight extension. Both restrict to the same natural A₈ module.
The original natural three-space generates the literal orbit section. Its
pairing with itself vanishes because it has no intertwiner to its dual, so
its image is a maximal isotropic subspace. The opposite cubic fixes that
subspace pointwise and must therefore act trivially on the six-space.
Faithfulness of the source quotient places this cubic in the original
two-core action kernel, contradicting its order three.

The fixed kernel of the original B.5.1 section is retained throughout; no
splitting or replacement by a constituent is required. Combining this with
the repeated, natural, exterior and natural--dual exclusions closes every
containing action for the original zero-kernel natural-three marking.
General quiet preparation and the other original rows, including the
four-natural-copy row, remain with qt-d-10-nona5-point-constrained.
Source: Aschbacher--Smith 10.2.9, printed pp.751--753.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem orbit_coordinates
    (c : Context D t v I) (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N))
      (E : ActionEquiv (s.action.comp (A.subgroupOf N).subtype) (alternatingNatural 8)),
    let f := ((actionMk (internalModule D v I)).subgroupMap (I.subgroupOf (pointJoin T v I))).comp
      (subgroupOfEquivOfLe (show I ≤ pointJoin T v I from le_sup_left)).symm.toMonoidHom
    let f' := (subgroupOfEquivOfLe hAN).symm.toMonoidHom.comp f
    ∃ Z : Subgroup G, Nonempty (BinaryConjugationSection I (orbitModule D v I) Z
      ((alternatingNatural 8).comp (E.groupEquiv.toMonoidHom.comp f'))) := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let R := orbitModule D v I
  let K := I.subgroupOf H
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := K.map (actionMk U)
  dsimp only
  intro N hAN s E
  have hm : moved ((action U).comp N.subtype) (A.subgroupOf N) = ⊤ := by
    rw [moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.fully_moved_of_moved_le hspan
  let p := s.fullProjection hm
  let f : I →* A := ((actionMk U).subgroupMap K).comp
    (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm.toMonoidHom
  let f' := (subgroupOfEquivOfLe hAN).symm.toMonoidHom.comp f
  let φ := E.groupEquiv.toMonoidHom.comp f'
  let τ : Representation (ZMod 2) I (BinaryPermutation.natural (Fin 8)) :=
    (alternatingNatural 8).comp φ
  let j : R ≃* U := (subgroupOfEquivOfLe c.orbit_le_join).symm
  let k : R →* Multiplicative (BinaryPermutation.natural (Fin 8)) :=
    E.linearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp
      (p.toAddMonoidHom.toMultiplicative.comp j.toMonoidHom)
  let mark : BinaryConjugationSection I R (k.ker.map R.subtype) τ := {
    section_le := c.orbit_le_component
    kernel_le := map_subtype_le _
    normalized := le_normalizer_conjugateSpanBy _ _
    coordinates := k
    onto := E.linearEquiv.toAddEquiv.toMultiplicative.surjective.comp
      ((show Function.Surjective p.toAddMonoidHom.toMultiplicative from
        s.fullProjection_surjective hm).comp j.surjective)
    kernel_eq := (comap_map_eq_self_of_injective R.subtype_injective k.ker).symm
    equivariant := by
      intro i w
      have ha : action U (f i).val (Additive.ofMul (j w)) =
          Additive.ofMul (j ⟨(i:G)*w*(i:G)⁻¹,
            (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ _ i.property) w).mp w.property⟩) := by
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg H.subtype
          (action_apply U ⟨i,(show I ≤ H from le_sup_left) i.property⟩ (Additive.ofMul (j w)))
      exact (congrArg (fun z : Additive U => E.linearEquiv (p z)) ha.symm).trans
        ((congrArg E.linearEquiv
          (s.fullProjection_intertwines hm (f' i).val (Additive.ofMul (j w)))).trans
            (E.intertwines (f' i) _)) }
  exact ⟨k.ker.map R.subtype,⟨mark⟩⟩

/-- Both six-dimensional containing actions are excluded with their original
central quotient and fixed kernel. -/
theorem Context.no_orthogonal_section_of_natural_three
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ {d : ℕ} (_hd : d = 4 ∨ d = 5) (_eb : A ≃* SL(d,ZMod 2))
      (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N))
      (_hf : Function.Injective s.action)
      (_E : ActionEquiv (s.action.comp (A.subgroupOf N).subtype) (alternatingNatural 8)),
      False := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let R := orbitModule D v I
  let K := I.subgroupOf H
  let := c.reduced.normal
  let := c.reduced.elementary
  let W := ⁅D.fullModule,L⁆
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  let A := K.map (actionMk U)
  dsimp only
  intro d hd eb N hAN s hfaith E
  have hspan := c.moved_le_of_natural_three e r
  have hm : moved ((action U).comp N.subtype) (A.subgroupOf N) = ⊤ := by
    rw [moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.fully_moved_of_moved_le hspan
  let p := s.fullProjection hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ρ : Representation (ZMod 2) L (Fin 3 → ZMod 2) :=
    (specialLinearNatural (k := ZMod 2) 3).comp q
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let f : I →* A := ((actionMk U).subgroupMap K).comp
    (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm.toMonoidHom
  let f' := (subgroupOfEquivOfLe hAN).symm.toMonoidHom.comp f
  let φ := E.groupEquiv.toMonoidHom.comp f'
  let τ : Representation (ZMod 2) I (BinaryPermutation.natural (Fin 8)) :=
    (alternatingNatural 8).comp φ
  let j : R ≃* U := (subgroupOfEquivOfLe c.orbit_le_join).symm
  obtain ⟨Z,⟨mark⟩⟩ := orbit_coordinates c hspan N hAN s E
  have hzero (b : ρ.IntertwiningMap ρ.dual) : b = 0 := by
    let b' : BinaryLinearThree.W.IntertwiningMap BinaryLinearThree.W.dual := {
      toLinearMap := b.toLinearMap
      isIntertwining' := by
        intro g
        obtain ⟨l,rfl⟩ := hq g
        apply LinearMap.ext
        intro w
        apply LinearMap.ext
        intro x
        have he := congrArg (fun z => z x) (LinearMap.congr_fun (b.isIntertwining' l) w)
        change b (ρ l w) x = b w (specialLinearNatural 3 (q l⁻¹) x) at he
        change b (ρ l w) x = b w (specialLinearNatural 3 ((q l)⁻¹) x)
        simpa only [map_inv q] using he }
    have he := BinaryLinearThree.NaturalDual.natural_dual_zero b'
    apply Representation.IntertwiningMap.ext
    exact congrArg (fun z : BinaryLinearThree.W.IntertwiningMap BinaryLinearThree.W.dual => z.toLinearMap) he
  let B := BinaryPermutation.naturalPairing (Fin 8)
  have hB : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    ((LinearMap.ker_eq_bot).mpr (BinaryPermutation.naturalPairing_injective (Fin 8)))
  have hinv (i : I) (x z : BinaryPermutation.natural (Fin 8)) :
      B (τ i x) (τ i z) = B x z := by
    obtain ⟨u,rfl⟩ := BinaryPermutation.coreToNatural_surjective x
    obtain ⟨w,rfl⟩ := BinaryPermutation.coreToNatural_surjective z
    change BinaryPermutation.naturalPairing (Fin 8)
      (BinaryPermutation.naturalRepresentation (Fin 8) (φ i).val (BinaryPermutation.coreToNatural (Fin 8) u))
      (BinaryPermutation.naturalRepresentation (Fin 8) (φ i).val (BinaryPermutation.coreToNatural (Fin 8) w)) = _
    rw [←BinaryPermutation.coreToNatural_equivariant,←BinaryPermutation.coreToNatural_equivariant,
      BinaryPermutation.naturalPairing_apply_core,BinaryPermutation.naturalPairing_apply_core]
    change (∑ j, u.val ((φ i).val.symm j) * w.val ((φ i).val.symm j)) = ∑ j, u.val j * w.val j
    exact Equiv.sum_comp (φ i).val.symm (fun j => u.val j * w.val j)
  have hdim : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 8)) =
      2 * Module.finrank (ZMod 2) (Fin 3 → ZMod 2) := by
    rw [BinaryPermutation.finrank_natural_even (Fin 8) (by decide),Module.finrank_fin_fun]
    decide
  let : Nontrivial (BinaryPermutation.natural (Fin 8)) :=
    Module.nontrivial_of_finrank_pos (by rw [hdim,Module.finrank_fin_fun]; decide)
  obtain ⟨y,hy3,hyv,_,hyC⟩ := c.exists_opposite_cubic_of_natural_three e r
  have hyI : y ∈ I := by
    rw [←c.component_eq_point_residual_of_binary_actor hd eb]
    apply mem_map_of_mem (centralizer ({v} : Set G)).subtype (x := ⟨y,hyv⟩)
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    change y ^ (3 ^ 1) = 1
    simpa only [pow_one,hy3] using pow_orderOf_eq_one y
  let yI : I := ⟨y,hyI⟩
  have hy : yI ^ 3 = 1 := Subtype.ext (hy3 ▸ pow_orderOf_eq_one y)
  have hyact : τ yI = 1 := r.cubic_eq_one_of_centralizes_generator τ mark
    c.escaping.strict.le hspan (conjugateSpanBy_mono inf_le_left le_rfl)
    hzero hdim B hB hinv yI hy hyC
  have hs : s.central.quotientRepresentation (f' yI).val = 1 := by
    apply LinearMap.ext
    intro z
    apply E.linearEquiv.injective
    change E.linearEquiv (s.central.quotientRepresentation (f' yI).val z) = E.linearEquiv z
    exact (E.intertwines (f' yI) z).trans (LinearMap.congr_fun hyact (E.linearEquiv z))
  have hf1 : f yI = 1 := by
    apply Subtype.ext
    exact congrArg N.subtype (hfaith (hs.trans (map_one s.central.quotientRepresentation).symm))
  let yH : H := ⟨y,(le_sup_left : I ≤ H) hyI⟩
  let yK : K := ⟨yH,hyI⟩
  have hyker : yK ∈ ((actionMk U).subgroupMap K).ker := hf1
  have hycore := (c.action_kernel_eq_twoCore_of_binary_actor hd eb).le hyker
  let z : pCore 2 K := ⟨yK,hycore⟩
  have hz3 : orderOf z = 3 := (Subgroup.orderOf_coe z).symm.trans
    ((Subgroup.orderOf_coe yK).symm.trans ((Subgroup.orderOf_coe yH).symm.trans hy3))
  have hzne : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz3; omega
  have htwo := (pCore_isPGroup (p := 2) (G := K)).dvd_orderOf hzne
  rw [hz3] at htwo
  norm_num at htwo

/-- Every containing-action branch is impossible when the original moved
subgroup has its natural three-dimensional marking. -/
theorem Context.no_natural_three
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let U := internalModule D v I
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk U)
  let N := offenderSubgroup (action U)
  have a := c.actionFacts_of_natural_three e r
  have hAN : A ≤ N := a.classification.2.1
  obtain ⟨h,hs,d,hd,⟨eb⟩⟩ := c.orthogonal_source_action_of_natural_three e r
  cases hs with
  | orthogonalSix hf hi E =>
    exact c.no_orthogonal_section_of_natural_three e r hd eb N hAN h.sectionData hf E
  | symmetricEight hf hi E =>
    apply c.no_orthogonal_section_of_natural_three e r hd eb N hAN h.sectionData hf
    refine ⟨E.subgroupEquiv,E.action.linearEquiv,?_⟩
    intro a w
    have he := E.action.intertwines ⟨a,E.contained a.property⟩ w
    exact he.trans (congrArg (fun g : Equiv.Perm (Fin 8) =>
      BinaryPermutation.naturalRepresentation (Fin 8) g (E.action.linearEquiv w)) (E.compatible a))

end CFSG.Quasithin.Chapter10.PointControl.Constrained
