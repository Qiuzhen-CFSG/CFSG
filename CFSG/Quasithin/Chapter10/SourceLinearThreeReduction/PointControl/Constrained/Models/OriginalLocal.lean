module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalConstituents
public import Theory.Representation.PSL3Two.NaturalDualNonFF
public import Theory.Representation.TwoGroupIntertwiner
public import Theory.Representation.SimpleHeadQuotient.DistinctPairQuotient

/-!
# Whole local binary-module recognition

The original component joined with its half-Sylow normalizer acts
irreducibly on the local moved subgroup. A natural subsection and the
extension of the natural--dual action to Aut(SL3(2)) give a nonzero
component intertwiner. The two-group quotient supplies a surjection onto
the whole local module. Its kernel leaves a natural, dual-natural or
natural--dual module; a graph change chooses the natural orientation.

All coordinates are on the literal local moved subgroup, with zero kernel.
Its dimension is at most six, whereas the full original moved subgroup has
dimension at least nine. Thus the local marking cannot be substituted for
a marking of the full module. Applying this to the original component
alternatives leaves only the Suzuki quotient branch unmarked.

Source: Aschbacher--Smith 10.2.9, printed pp.751--752. The subsequent local
row exclusions, Suzuki recognition and final constrained exclusion remain
with this source owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
local instance : IsElementaryAbelian 2 (⁅D.moduleSubgroup,L⁆ : Subgroup G) := by
  let := source_original_full_moved_elementary D
  exact IsElementaryAbelian.of_le
    (show ⁅D.moduleSubgroup,L⁆ ≤ ⁅D.fullModule,L⁆ from
      commutator_mono (le_componentOrbit _ _) le_rfl)

/-- The component and half-Sylow normalizer preserve the literal local moved subgroup. -/
theorem Context.local_moved_join_normalizes (c : Context D t v I) :
    L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)) ≤
      normalizer (↑(⁅D.moduleSubgroup,L⁆ : Subgroup G) : Set G) :=
  (sup_le ((le_componentOrbit _ _).trans le_sup_left) le_sup_right).trans
    c.halfJoin_normalizes_local_moved

private def localSection (c : Context D t v I) :
    BinaryConjugationSection (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))
      ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryConjugationSection.originalNormalizerAction (c.local_moved_join_normalizes)) := {
  section_le := (commutator_mono (le_componentOrbit _ _) le_rfl).trans
    ((source_full_moved_le_component D).trans le_sup_left)
  kernel_le := bot_le
  normalized := c.local_moved_join_normalizes
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

/-- The original half-Sylow component join acts irreducibly on the whole local moved subgroup. -/
theorem Context.local_moved_join_irreducible (c : Context D t v I) :
    IsIrreducible (BinaryConjugationSection.originalNormalizerAction (c.local_moved_join_normalizes)) := by
  let : Nontrivial (⁅D.moduleSubgroup,L⁆ : Subgroup G) :=
    (nontrivial_iff_ne_bot _).mpr (Selection.ModuleChoice.local_moved_ne_bot D)
  apply (localSection c).irreducible_of_subgroup_minimal
  intro A hA hN
  rcases c.local_moved_minimal A hA (le_sup_left.trans hN) (le_sup_right.trans hN) with he | hc
  · exact Or.inl he
  · exact Or.inr ((le_inf (hA.trans (commutator_mono (le_componentOrbit _ _) le_rfl)) hc).trans_eq
      c.moved_fixed_eq_bot)


/-- The whole local moved subgroup is a quotient of the actual natural–dual
module under the original half-Sylow component action. -/
theorem Context.local_binary_pair_quotient (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    ∃ f : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
      ∃ p : IntertwiningMap (BinaryLinearThree.NaturalDual.action.comp
          (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
        ((BinaryConjugationSection.originalNormalizerAction (c.local_moved_join_normalizes)).comp
          (inclusion le_sup_left)), Function.Surjective p := by
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let H := L ⊔ S
  let K := L.subgroupOf H
  let η := BinaryConjugationSection.originalNormalizerAction (c.local_moved_join_normalizes)
  let := c.local_moved_join_irreducible
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer inf_le_right)
  have hsup : K ⊔ S.subgroupOf H = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ H from le_sup_left)
      (show S ≤ H from le_sup_right),subgroupOf_self]
  have hQ := isPGroup_quotient_of_sup_eq_top K (S.subgroupOf H)
    (T.isPGroup'.to_le (show S ≤ T from inf_le_left)).comap_subtype hsup
  obtain ⟨B,hB,_,f,⟨r⟩⟩ := c.local_binary_natural_subsection e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hB
  obtain ⟨j,hj⟩ := r.exists_injective_intertwiner (localSection c) le_sup_left hB
  let α : H →* MulAut BinaryLinearThree.Group :=
    (MulAut.congr f).toMonoidHom.comp (pCoreJoinAction 2 (show S ≤ normalizer (L:Set G) from inf_le_right))
  let τ := BinaryLinearThree.NaturalDual.autAction.comp α
  have ha (l : L) : α (inclusion le_sup_left l) = MulAut.conj (q l) := by
    change (MulAut.congr f) (pCoreJoinAction 2 _ (inclusion le_sup_left l)) = _
    rw [pCoreJoinAction_on_component,MulAut.congr_conj]
    rfl
  have he (l : L) : τ (inclusion le_sup_left l) = BinaryLinearThree.NaturalDual.action (q l) := by
    change BinaryLinearThree.NaturalDual.autAction (α _) = _
    rw [ha,BinaryLinearThree.NaturalDual.autAction_inner]
  let b : IntertwiningMap (τ.comp K.subtype) (η.comp K.subtype) := {
    toLinearMap := j.toLinearMap.comp (LinearMap.fst _ _ _)
    isIntertwining' k := by
      apply LinearMap.ext
      intro x
      change j ((τ (k:H) x).1) = η (k:H) (j x.1)
      have hk : (k:H) = inclusion le_sup_left (⟨k.val,k.property⟩ : L) := rfl
      rw [hk,he]
      exact LinearMap.congr_fun (j.isIntertwining' ⟨k.val,k.property⟩) x.1 }
  have hb : b ≠ 0 := by
    intro hz
    obtain ⟨x,hx⟩ := exists_ne (0 : BinaryLinearThree.Vector)
    have hh : j x = 0 := congrArg (fun z : IntertwiningMap (τ.comp K.subtype) _ => z (x,0)) hz
    exact hx (hj (hh.trans j.map_zero.symm))
  obtain ⟨p,hp⟩ := exists_surjective_intertwiner_of_twoGroup_quotient K hQ τ η b hb
  refine ⟨f,⟨{ toLinearMap := p.toLinearMap, isIntertwining' := ?_ },hp⟩⟩
  intro l
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun (p.isIntertwining' (inclusion le_sup_left l)) x
  change p (τ (inclusion le_sup_left l) x) = η (inclusion le_sup_left l) (p x) at hh
  rwa [he] at hh

/-- Original binary local moved modules have at most six dimensions, even
when their full moved module has larger multiplicity. -/
theorem Context.local_binary_finrank_le_six (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    Module.finrank (ZMod 2) (Additive (⁅D.moduleSubgroup,L⁆ : Subgroup G)) ≤ 6 := by
  obtain ⟨f,p,hp⟩ := c.local_binary_pair_quotient e
  have hh := LinearMap.finrank_le_finrank_of_surjective (f := p.toLinearMap) hp
  have hd : Module.finrank (ZMod 2) BinaryLinearThree.NaturalDual.Space = 6 := by
    rw [Module.finrank_prod,Subspace.dual_finrank_eq]
    norm_num [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector,Module.finrank_fin_fun]
  exact hh.trans_eq hd


/-- The entire local moved subgroup has natural, dual-natural, or natural–dual
coordinates. This is a whole-module statement, with zero covering kernel. -/
theorem Context.local_binary_marking (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    ∃ f : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
      Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
        (BinaryLinearThree.W.comp (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∨
      Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
        (BinaryLinearThree.W.dual.comp (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∨
      Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
        (BinaryLinearThree.NaturalDual.action.comp
          (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let U := ⁅D.moduleSubgroup,L⁆
  let η := (BinaryConjugationSection.originalNormalizerAction (c.local_moved_join_normalizes)).comp
    (inclusion (show L ≤ L ⊔ ((T:Subgroup G) ⊓ normalizer (L:Set G)) from le_sup_left))
  let : Nontrivial U := (nontrivial_iff_ne_bot _).mpr (Selection.ModuleChoice.local_moved_ne_bot D)
  obtain ⟨f,p,hp⟩ := c.local_binary_pair_quotient e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  let σ := BinaryLinearThree.W.comp q
  let τ := BinaryLinearThree.W.dual.comp q
  let : IsIrreducible σ := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible τ := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  have hne : ¬ Nonempty (Representation.Equiv σ τ) := by
    rintro ⟨E⟩
    apply BinaryLinearThree.AutomorphismAction.natural_not_equiv_dual
    exact ⟨{ toLinearEquiv := E.toLinearEquiv
             isIntertwining' := fun g => by
               obtain ⟨l,rfl⟩ := hq g
               exact E.isIntertwining' l }⟩
  let s : BinaryConjugationSection L U ⊥ η := {
    section_le := (commutator_mono (le_componentOrbit _ _) le_rfl).trans
      (source_full_moved_le_component D)
    kernel_le := bot_le
    normalized := normalizer_commutator_ge_right _ _
    coordinates := (localSection c).coordinates
    onto := (localSection c).onto
    kernel_eq := (localSection c).kernel_eq
    equivariant := fun l w => (localSection c).equivariant (inclusion le_sup_left l) w }
  refine ⟨f,?_⟩
  rcases SimpleHeadQuotient.distinct_pair_quotient σ τ hne η p hp with h | h | h
  · exact Or.inl ⟨s.relabel (MonoidHom.id L) h.some⟩
  · exact Or.inr (Or.inl ⟨s.relabel (MonoidHom.id L) h.some⟩)
  · exact Or.inr (Or.inr ⟨s.relabel (MonoidHom.id L) h.some⟩)

/-- A graph change chooses the natural orientation of the actual local
module. Larger original multiplicities do not create additional local rows. -/
theorem Context.local_binary_natural_or_pair (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    ∃ f : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
      Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
        (BinaryLinearThree.W.comp (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∨
      Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
        (BinaryLinearThree.NaturalDual.action.comp
          (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  obtain ⟨f,h | h | h⟩ := c.local_binary_marking e
  · exact ⟨f,Or.inl h⟩
  · exact ⟨f.trans BinaryLinearThree.AutomorphismAction.graph,
      Or.inl ⟨h.some.relabel _ BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm⟩⟩
  · exact ⟨f,Or.inr h⟩


/-- The larger binary branch has a genuinely smaller local moved subgroup.
The recovered three- or six-dimensional marking is not a marking of the
whole original moved module. -/
theorem Context.local_moved_lt_full_of_binary (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    ⁅D.moduleSubgroup,L⁆ < ⁅D.fullModule,L⁆ := by
  apply lt_of_le_of_ne (commutator_mono (le_componentOrbit _ _) le_rfl)
  intro he
  let := source_original_full_moved_elementary D
  have hsmall := c.local_binary_finrank_le_six e
  have hlarge := c.original_binary_finrank_ge_nine e
  have hd : Module.finrank (ZMod 2) (Additive (⁅D.moduleSubgroup,L⁆ : Subgroup G)) =
      Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := by
    let f := (MulEquiv.subgroupCongr he).toAdditive
    let F : Additive (⁅D.moduleSubgroup,L⁆ : Subgroup G) →ₗ[ZMod 2]
        Additive (⁅D.fullModule,L⁆ : Subgroup G) := f.toAddMonoidHom.toZModLinearMap 2
    have hf : Function.Bijective F := f.bijective
    exact (LinearEquiv.ofBijective F hf).finrank_eq
  omega

/-- Apply whole local recognition to the original component alternatives.
The only unmarked quotient branch is Suzuki; the binary local coordinates
retain the literal subgroup inside VI and its zero kernel. -/
theorem Context.original_local_marking_or_suzuki (c : Context D t v I) :
    (∃ f : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
      Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
        (BinaryLinearThree.W.comp (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∨
      Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
        (BinaryLinearThree.NaturalDual.action.comp
          (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) ∨
    ∃ m : ℕ, 0 < m ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rcases c.original_component_alternatives with h | h
  · exact Or.inl (c.local_binary_natural_or_pair h.some)
  · exact Or.inr h

end CFSG.Quasithin.Chapter10.PointControl.Constrained
