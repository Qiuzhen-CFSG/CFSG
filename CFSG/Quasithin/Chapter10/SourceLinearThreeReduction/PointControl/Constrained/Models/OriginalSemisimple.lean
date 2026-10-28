module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalBinaryAction
public import Theory.Representation.NormalSemisimpleSpan
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.DoubledExclusion

/-!
# Original semisimple actions and the small binary branch

The original component normalizer acts irreducibly on [V_M,L], by minimality
and the proved vanishing of its fixed kernel. Clifford restriction gives
semisimplicity for L. Conjugation descends through the specified quotient
L/O₂(L), with identity coordinates on the original moved subgroup; the
semisimplicity and zero fixed space survive this descent.

For an SL₃(2) quotient, the semisimple catalogue below dimension nine gives
an irreducible module or two natural/dual copies. The natural and natural-dual
exclusions already proved here, together with the minimal-normalizer doubled
exclusion, leave only the eight-dimensional Steinberg module. Consequently
the original binary moved subgroup has dimension at least eight. In the
small branch its recovered irreducible marking proves containment in VI
and equality of the local and full original modules.

This does not assert the original source-row exhaustion. The Steinberg
exclusion, larger binary modules, and Suzuki recognition remain with this
owner. Source applies the reduction to the original point-control contract;
no later generation bound or small-offender recognition is imported.

Source: Aschbacher--Smith H.6.1 and10.2.9, printed pp.386,751--753;
Clifford restriction as in Isaacs, Character Theory of Finite Groups,6.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

private theorem moved_normalizer_le :
    D.maximalLocal ⊓ normalizer (L : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
    (D.maximalLocal_normalizes_fullModule hg.1),mem_normalizer_iff_map_conj_eq.mp hg.2]

private def movedNormalizerSection :
    BinaryConjugationSection (D.maximalLocal ⊓ normalizer (L : Set G))
      ⁅D.fullModule,L⁆ ⊥ (BinaryConjugationSection.originalNormalizerAction
        (moved_normalizer_le (D := D))) := {
  section_le := (source_full_moved_le_component D).trans
    (le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer)
  kernel_le := bot_le
  normalized := moved_normalizer_le
  coordinates := { toFun w := Multiplicative.ofAdd (Additive.ofMul w)
                   map_one' := rfl
                   map_mul' _ _ := rfl }
  onto := fun w => ⟨w.toAdd.toMul,rfl⟩
  kernel_eq := by ext w; simp
  equivariant := by
    intro g w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (BinaryConjugationSection.originalNormalizerAction_apply_coe _ g
      (Additive.ofMul w)).symm }

/-- The literal component action on the original moved subgroup is semisimple. -/
theorem Context.original_moved_semisimple (c : Context D t v I) :
    IsSemisimpleModule (ZMod 2)[L] (Representation.asModule
      (BinaryConjugationSection.originalNormalizerAction
        (normalizer_commutator_ge_right D.fullModule L))) := by
  let W := ⁅D.fullModule,L⁆
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let B := L.subgroupOf N
  have hLN : L ≤ N :=
    le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
  let : B.Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  let : Nontrivial W := (nontrivial_iff_ne_bot _).mpr (source_full_moved_ne_bot D)
  let : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  let η := BinaryConjugationSection.originalNormalizerAction (moved_normalizer_le (D := D))
  have hi : IsIrreducible η :=
    Selection.ModuleChoice.moved_normalizer_section_irreducible D c.minimal
      c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed η
      (c.moved_fixed_eq_bot.symm ▸ movedNormalizerSection)
  let := NormalConstituentDisplacement.restriction_semisimple η hi B
  let e : L ≃* B := (subgroupOfEquivOfLe hLN).symm
  have he : (η.comp B.subtype).comp e.toMonoidHom =
      BinaryConjugationSection.originalNormalizerAction
        (normalizer_commutator_ge_right D.fullModule L) := by
    apply MonoidHom.ext
    intro l
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (BinaryConjugationSection.originalNormalizerAction_apply_coe _ _ _).trans
      (BinaryConjugationSection.originalNormalizerAction_apply_coe
        (normalizer_commutator_ge_right D.fullModule L) l w).symm
  exact he ▸ comp_semisimple_of_surjective (η.comp B.subtype) e.toMonoidHom e.surjective

/-- Semisimple coordinates on the actual moved subgroup through any specified original quotient. -/
theorem Context.original_quotient_semisimple (c : Context D t v I)
    {Q : Type*} [Group Q] (e : (L ⧸ pCore 2 L) ≃* Q) :
    ∃ (ρ : Representation (ZMod 2) Q (Additive (⁅D.fullModule,L⁆ : Subgroup G)))
      (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        (ρ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))),
      (∀ w, (s.coordinates w).toAdd = Additive.ofMul w) ∧
      IsSemisimpleModule (ZMod 2)[Q] ρ.asModule ∧ ρ.invariants = ⊥ := by
  let W := ⁅D.fullModule,L⁆
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  obtain ⟨ρ,s,hs⟩ := BinaryConjugationSection.exists_of_central_kernel L W
    (source_full_moved_le_component D) (normalizer_commutator_ge_right _ _) q hq (by
      intro l hl
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        (e.injective (hl.trans e.map_one.symm))
      exact centralizer_le hWV (source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp)))
  have he : ρ.comp q = BinaryConjugationSection.originalNormalizerAction
      (normalizer_commutator_ge_right D.fullModule L) := by
    apply MonoidHom.ext
    intro l
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [BinaryConjugationSection.originalNormalizerAction_apply_coe]
    have hh := s.equivariant l w.toMul
    rw [hs,hs] at hh
    exact congrArg (fun z : Additive W => (z.toMul : G)) hh.symm
  refine ⟨ρ,s,hs,?_,?_⟩
  · apply (semisimple_comp_iff_of_surjective ρ q hq).mp
    rw [he]
    exact c.original_moved_semisimple
  · apply bot_unique
    intro w hw
    apply Additive.toMul.injective
    apply Subtype.ext
    apply c.moved_fixed_eq_bot.le
    refine ⟨w.toMul.property,?_⟩
    intro l hl
    have hh := s.equivariant ⟨l,hl⟩ w.toMul
    rw [hs,hs] at hh
    change Additive.ofMul _ = ρ (q ⟨l,hl⟩) w at hh
    rw [hw] at hh
    exact mul_inv_eq_iff_eq_mul.mp
      (congrArg (fun z : Additive W => (z.toMul : G)) hh)

private def productEquiv
    {Q X Y X' Y' : Type*} [Group Q]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup X'] [Module (ZMod 2) X'] [AddCommGroup Y'] [Module (ZMod 2) Y']
    {ρ : Representation (ZMod 2) Q X} {σ : Representation (ZMod 2) Q Y}
    {ρ' : Representation (ZMod 2) Q X'} {σ' : Representation (ZMod 2) Q Y'}
    (a : ρ.Equiv ρ') (b : σ.Equiv σ') : (ρ.prod σ).Equiv (ρ'.prod σ') where
  toLinearEquiv := a.toLinearEquiv.prodCongr b.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact Prod.ext (LinearMap.congr_fun (a.isIntertwining' g) v.1)
      (LinearMap.congr_fun (b.isIntertwining' g) v.2)

private def doubleNaturalEquiv :
    (BinaryLinearThree.W.prod BinaryLinearThree.W).Equiv
      (ChapterB.QuasisimpleSource.repeated
        (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3) 2) where
  toLinearEquiv := (LinearEquiv.finTwoArrow (ZMod 2) BinaryLinearThree.Vector).symm
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i <;> rfl

private def swapNaturalDual :
    (BinaryLinearThree.W.dual.prod BinaryLinearThree.W).Equiv
      (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) where
  toLinearEquiv := LinearEquiv.prodComm _ _ _
  isIntertwining' _ := rfl

private theorem no_original_double (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      ((BinaryLinearThree.W.prod BinaryLinearThree.W).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False :=
  Selection.ModuleChoice.not_binaryThreeDoubled_of_minimal D c.minimal
    c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed
    ⟨e,⟨s.relabel _ doubleNaturalEquiv⟩⟩

private def graphDouble :
    (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual).Equiv
      ((BinaryLinearThree.W.prod BinaryLinearThree.W).comp
        BinaryLinearThree.AutomorphismAction.graph.toMonoidHom) :=
  productEquiv BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm
    BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm

private theorem no_original_dual_double (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      ((BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False :=
  no_original_double c (e.trans BinaryLinearThree.AutomorphismAction.graph)
    (s.relabel _ graphDouble)

/-- Below dimension nine, every original binary moved action has literal Steinberg
coordinates: the natural and two-copy alternatives contradict the original context. -/
theorem Context.original_small_binary_steinberg (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (hd : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 9) :
    Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.S.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let W := ⁅D.fullModule,L⁆
  let : Nontrivial W := (nontrivial_iff_ne_bot _).mpr (source_full_moved_ne_bot D)
  let : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  obtain ⟨ρ,s,_,hss,hf⟩ := c.original_quotient_semisimple e
  let := hss
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have sn : BinaryConjugationSection L W (sourceMovedFixed D) (ρ.comp q) :=
    c.moved_fixed_eq_bot.symm ▸ s
  rcases BinaryLinearThree.small_semisimple_alternatives ρ hf hd with hi | h | h | h | h
  · let := hi
    have hm : ∃ g w, ρ g w ≠ w := by
      by_contra! h
      obtain ⟨w,hw⟩ := exists_ne (0 : Additive W)
      exact hw (hf.le (fun g => h g w))
    rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial ρ hm with h | h | h
    · exact (c.no_binaryThreeNatural ⟨e,⟨sn.relabel q h.some⟩⟩).elim
    · exact (c.no_binaryThreeNatural
        ⟨e.trans BinaryLinearThree.AutomorphismAction.graph,
          ⟨sn.relabel q (h.some.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm)⟩⟩).elim
    · exact ⟨sn.relabel q h.some⟩
  · exact (no_original_double c e (sn.relabel q h.some)).elim
  · exact (c.no_naturalDual_cover e (sn.relabel q h.some)).elim
  · exact (c.no_naturalDual_cover e (sn.relabel q (h.some.trans swapNaturalDual))).elim
  · exact (no_original_dual_double c e (sn.relabel q h.some)).elim

/-- An original binary moved subgroup has at least eight dimensions, without a marking premise. -/
theorem Context.original_binary_finrank_ge_eight (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    8 ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := by
  by_contra hn
  obtain ⟨s⟩ := c.original_small_binary_steinberg e (by omega)
  have hi : Function.Injective s.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [s.kernel_eq,c.moved_fixed_eq_bot,bot_subgroupOf])
  let f : Additive (⁅D.fullModule,L⁆ : Subgroup G) ≃ₗ[ZMod 2] BinaryLinearThree.Steinberg :=
    LinearEquiv.ofBijective (s.coordinates.toAdditiveLeft.toZModLinearMap 2)
      ⟨hi,s.onto⟩
  have hd := f.finrank_eq
  rw [BinaryLinearThree.finrank_steinberg] at hd
  omega

/-- The small binary branch has the full original moved subgroup inside VI;
this comparison follows from the recovered irreducible marking. -/
theorem Context.original_small_binary_moved_le (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (hd : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 9) :
    ⁅D.fullModule,L⁆ ≤ orbitModule D v I := by
  obtain ⟨s⟩ := c.original_small_binary_steinberg e hd
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : IsIrreducible (BinaryLinearThree.S.comp q) :=
    (irreducible_comp_surjective_iff q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr
      BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible
  exact c.moved_le_of_irreducible_cover s

/-- The recovered small original binary marking identifies the local and full
modules, rather than assuming this comparison for an arbitrary reduced orbit. -/
theorem Context.original_small_binary_full_eq_local (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (hd : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 9) :
    D.fullModule = D.moduleSubgroup := by
  obtain ⟨s⟩ := c.original_small_binary_steinberg e hd
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : IsIrreducible (BinaryLinearThree.S.comp q) :=
    (irreducible_comp_surjective_iff q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr
      BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible
  exact c.full_eq_local_of_irreducible_cover s

end CFSG.Quasithin.Chapter10.PointControl.Constrained
