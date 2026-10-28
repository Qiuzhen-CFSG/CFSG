module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.CellCollection
public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.CellSeparation
public import Theory.AlgebraicGroup.BNPair.StandardParabolicCore

/-!
# The concrete binary split D4 Tits system

The actual Borel-normalizer intersection is the torus. Torus normalization
therefore gives the required relative normality, while the upper-matrix Weyl
separation identifies the normalizer quotient with the root permutation group.
The numbered pinned words give its distinguished involutions. Concrete cell
exchange and the negative-simple matrix witness prove the remaining BN axioms.

All conclusions use only the published Weyl/torus `Inputs`; the parent supplies
those inputs. No Bruhat coverage, separation, or parabolic assertion is assumed.
The small private group-theoretic transport lemmas keep quotient elaboration
independent of the size of the underlying Geck matrix expressions.

Source: GLS3 2.3.4–8 and §2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

open scoped Pointwise
open Theory.AlgebraicGroup
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm
open Parabolics
noncomputable section

theorem normalizer_intersection_normal (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) :
    ((splitBorel (binaryParameters n hn) ⊓ splitNormalizer _).subgroupOf
      (splitNormalizer _)).Normal := by
  rw [CellSeparation.borel_inf_normalizer n hn D]
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le (splitTorus _).le_normalizer D.weyl_normalizes_torus)

theorem lift_mem_borel_iff (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (w : rootWeylGroup) :
    D.lift w ∈ splitBorel _ ↔ w = 1 := by
  constructor
  · intro h
    exact CellSeparation.weyl_eq_one_of_upper D w
      (CellSeparation.upper_borel n hn D (CellSeparation.upper_torus _ rfl) h)
      (CellSeparation.matrix_lift_root_pivot_ne_zero n hn D w)
  · rintro rfl
    rw [map_one]
    exact (splitBorel _).one_mem

def normalizerLift {P : Parameters} (D : Inputs P) :
    rootWeylGroup →* splitNormalizer P :=
  D.lift.codRestrict (splitNormalizer P)
    (fun w => Subgroup.mem_sup_right (D.weylEquiv.symm w).property)

section Quotient
variable {P : Parameters} (D : Inputs P)
variable [((splitBorel P ⊓ splitNormalizer P).subgroupOf (splitNormalizer P)).Normal]

def quotientLift : rootWeylGroup →*
    (splitNormalizer P ⧸ (splitBorel P ⊓ splitNormalizer P).subgroupOf (splitNormalizer P)) :=
  (QuotientGroup.mk' _).comp (normalizerLift D)

private theorem surjective_quotient_comp_of_factors {G W : Type*} [Group G] [Group W]
    (H : Subgroup G) [H.Normal] (f : W →* G)
    (hf : ∀ g, ∃ t ∈ H, ∃ w, t * f w = g) :
    Function.Surjective ((QuotientGroup.mk' H).comp f) := by
  intro q
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H q
  obtain ⟨t, ht, w, hw⟩ := hf g
  refine ⟨w, ?_⟩
  have htq : QuotientGroup.mk' H t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
  have hm : QuotientGroup.mk' H (t * f w) = QuotientGroup.mk' H (f w) := by
    rw [map_mul, htq, one_mul]
  exact hm.symm.trans ((congrArg (QuotientGroup.mk' H) hw).trans hg)

theorem quotientLift_surjective : Function.Surjective (quotientLift D) := by
  apply surjective_quotient_comp_of_factors
  intro g
  have hg := g.property
  change g.val ∈ (splitTorus P ⊔ splitWeylSubgroup P : Subgroup (SplitGroup P)) at hg
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    D.weyl_normalizes_torus] at hg
  obtain ⟨t, ht, v, hv, htv⟩ := hg
  let w := D.weylEquiv ⟨v, hv⟩
  have hw : D.lift w = v :=
    congrArg Subtype.val (D.weylEquiv.symm_apply_apply ⟨v, hv⟩)
  let tN : splitNormalizer P := ⟨t, Subgroup.mem_sup_left ht⟩
  refine ⟨tN, ⟨splitTorus_le_splitBorel P ht, tN.property⟩, w, ?_⟩
  exact Subtype.ext ((congrArg (fun x => t * x) hw).trans htv)

end Quotient

section BinaryQuotient
variable (n : ℕ) (hn : 0 < n) (D : Inputs (binaryParameters n hn))
variable [((splitBorel (binaryParameters n hn) ⊓ splitNormalizer _).subgroupOf
  (splitNormalizer _)).Normal]

theorem quotientLift_injective : Function.Injective (quotientLift D) := by
  apply (injective_iff_map_eq_one _).mpr
  intro w hw
  apply (lift_mem_borel_iff n hn D w).mp
  exact ((QuotientGroup.eq_one_iff (normalizerLift D w)).mp hw).1

def quotientEquiv : rootWeylGroup ≃*
    (splitNormalizer (binaryParameters n hn) ⧸
      (splitBorel _ ⊓ splitNormalizer _).subgroupOf (splitNormalizer _)) :=
  MulEquiv.ofBijective (quotientLift D)
    ⟨quotientLift_injective n hn D, quotientLift_surjective D⟩

theorem cell_eq_quotient_cell (w : rootWeylGroup) :
    cell D w = (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) *
      TitsSystem.representativeSet (splitBorel _) (splitNormalizer _)
        (quotientEquiv n hn D w) * (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) := by
  apply Eq.trans _ (TitsSystem.B_mul_representativeSet_mul_B
    (splitBorel (binaryParameters n hn)) (splitNormalizer (binaryParameters n hn))
    (quotientEquiv n hn D w) (normalizerLift D w) rfl).symm
  ext g
  constructor
  · rintro ⟨b, hb, c, hc, rfl⟩
    exact ⟨b * D.lift w, ⟨b, hb, D.lift w, rfl, rfl⟩, c, hc, rfl⟩
  · rintro ⟨x, ⟨b, hb, v, hv, rfl⟩, c, hc, rfl⟩
    rcases hv with rfl
    exact ⟨b, hb, c, hc, rfl⟩

end BinaryQuotient

theorem rootWeylGenerator_generate :
    Subgroup.closure (Set.range rootWeylGenerator) = ⊤ := by
  apply Subgroup.map_injective rootWeylGroup.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← Set.range_comp]
  rfl

private theorem representative_product_eq {G : Type*} [Group G] (B N : Subgroup G)
    [((B ⊓ N).subgroupOf N).Normal]
    (v w : N ⧸ (B ⊓ N).subgroupOf N) (nv nw : N)
    (hv : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) nv = v)
    (hw : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) nw = w) :
    TitsSystem.representativeSet B N v * (B : Set G) *
        TitsSystem.representativeSet B N w =
      ({nv.val} : Set G) * (B : Set G) * ({nw.val} : Set G) := by
  rw [TitsSystem.representativeSet_mul_B B N v nv hv, mul_assoc,
    TitsSystem.B_mul_representativeSet B N w nw hw, ← mul_assoc]

private theorem generates_range_comp {G H I : Type*} [Group G] [Group H]
    (e : G ≃* H) (f : I → G) (hf : Subgroup.closure (Set.range f) = ⊤) :
    Subgroup.closure (Set.range (e ∘ f)) = ⊤ := by
  rw [Set.range_comp]
  change Subgroup.closure (e.toMonoidHom '' Set.range f) = ⊤
  rw [← MonoidHom.map_closure e.toMonoidHom, hf]
  exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective

private theorem forall_range_equiv {I A B : Type*} (e : A ≃ B) (f : I → A)
    (R : B → B → Prop) (h : ∀ i w, R (e (f i)) (e w)) :
    ∀ s ∈ Set.range (e ∘ f), ∀ w, R s w := by
  rintro _ ⟨i, rfl⟩ q
  obtain ⟨w, rfl⟩ := e.surjective q
  exact h i w

section BinaryAxioms
variable (n : ℕ) (hn : 0 < n) (D : Inputs (binaryParameters n hn))
variable [((splitBorel (binaryParameters n hn) ⊓ splitNormalizer _).subgroupOf
  (splitNormalizer _)).Normal]

private theorem quotient_exchange (i : Fin 4) (w : rootWeylGroup) :
    TitsSystem.representativeSet (splitBorel _) (splitNormalizer _)
        (quotientEquiv n hn D (rootWeylGenerator i)) *
      (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) *
      TitsSystem.representativeSet (splitBorel _) (splitNormalizer _)
        (quotientEquiv n hn D w) ⊆
      cell D (rootWeylGenerator i * w) ∪ cell D w := by
  intro g hg
  have hg' : g ∈ ({D.lift (rootWeylGenerator i)} : Set (SplitGroup _)) *
      (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) *
      ({D.lift w} : Set (SplitGroup _)) :=
    (congrArg (fun A : Set (SplitGroup _) => g ∈ A)
      (representative_product_eq (splitBorel _) (splitNormalizer _) _ _
        (normalizerLift D (rootWeylGenerator i)) (normalizerLift D w) rfl rfl)).mp hg
  obtain ⟨x, ⟨s, hs, b, hb, rfl⟩, v, hv, rfl⟩ := hg'
  rcases hs with rfl
  rcases hv with rfl
  exact simple_reflection_exchange n hn D i w hb

private theorem quotient_nontrivial (i : Fin 4) :
    TitsSystem.representativeSet (splitBorel _) (splitNormalizer _)
        (quotientEquiv n hn D (rootWeylGenerator i)) *
      (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) *
      TitsSystem.representativeSet (splitBorel _) (splitNormalizer _)
        (quotientEquiv n hn D (rootWeylGenerator i)) ≠
      (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) := by
  intro heq
  have hpos : positiveRoot (binaryParameters n hn) i 1 ∈ splitBorel _ :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, 1, rfl⟩)
  have hx : D.lift (rootWeylGenerator i) * positiveRoot _ i 1 *
      D.lift (rootWeylGenerator i) ∈
      TitsSystem.representativeSet (splitBorel _) (splitNormalizer _)
          (quotientEquiv n hn D (rootWeylGenerator i)) *
        (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) *
        TitsSystem.representativeSet (splitBorel _) (splitNormalizer _)
          (quotientEquiv n hn D (rootWeylGenerator i)) :=
    ⟨_, ⟨_, ⟨normalizerLift D (rootWeylGenerator i), rfl, rfl⟩, _, hpos, rfl⟩,
      _, ⟨normalizerLift D (rootWeylGenerator i), rfl, rfl⟩, rfl⟩
  have hb := (congrArg (fun A : Set (SplitGroup _) =>
    D.lift (rootWeylGenerator i) * positiveRoot _ i 1 * D.lift (rootWeylGenerator i) ∈ A)
    heq).mp hx
  rw [D.lift_simple, weylWord_positive _ rfl] at hb
  exact CellSeparation.negativeRoot_not_borel n hn D i hb

private theorem quotient_involutions :
    ∀ s ∈ Set.range (quotientEquiv n hn D ∘ rootWeylGenerator), s ≠ 1 ∧ s ^ 2 = 1 := by
  let e := quotientEquiv n hn D
  rintro _ ⟨i, rfl⟩
  change e (rootWeylGenerator i) ≠ 1 ∧ e (rootWeylGenerator i) ^ 2 = 1
  constructor
  · intro h
    have hw : rootWeylGenerator i = 1 := e.injective (h.trans (map_one e).symm)
    have hb := (lift_mem_borel_iff n hn D (rootWeylGenerator i)).mpr hw
    rw [D.lift_simple] at hb
    exact CellSeparation.weylWord_not_borel n hn D i hb
  · have hw : rootWeylGenerator i ^ 2 = 1 := by
      apply Subtype.ext
      exact (Theory.AlgebraicGroup.StandardRootSystem.typeDRootPairing 2).reflectionPerm_sq _
    exact (map_pow e _ 2).symm.trans ((congrArg e hw).trans (map_one e))

private theorem quotient_generates :
    Subgroup.closure (Set.range (quotientEquiv n hn D ∘ rootWeylGenerator)) = ⊤ :=
  generates_range_comp (quotientEquiv n hn D) rootWeylGenerator rootWeylGenerator_generate

private theorem quotient_full_exchange :
    ∀ s ∈ Set.range (quotientEquiv n hn D ∘ rootWeylGenerator), ∀ w,
      TitsSystem.representativeSet (splitBorel _) (splitNormalizer _) s *
          (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) *
          TitsSystem.representativeSet (splitBorel _) (splitNormalizer _) w ⊆
        ((splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) *
          TitsSystem.representativeSet (splitBorel _) (splitNormalizer _) (s * w) *
          (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn)))) ∪
        ((splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) *
          TitsSystem.representativeSet (splitBorel _) (splitNormalizer _) w *
          (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn)))) := by
  apply forall_range_equiv (quotientEquiv n hn D).toEquiv rootWeylGenerator
  intro i w
  let e := quotientEquiv n hn D
  let R := fun q => (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))) *
    TitsSystem.representativeSet (splitBorel _) (splitNormalizer _) q *
    (splitBorel (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn)))
  have hsw : cell D (rootWeylGenerator i * w) =
      R (e (rootWeylGenerator i) * e w) :=
    (cell_eq_quotient_cell n hn D (rootWeylGenerator i * w)).trans
      (congrArg R (map_mul e _ _))
  have heq := congrArg₂ (fun A B : Set (SplitGroup (binaryParameters n hn)) => A ∪ B)
    hsw (cell_eq_quotient_cell n hn D w)
  exact fun g hg => heq.le (quotient_exchange n hn D i w hg)

end BinaryAxioms

/-- The Tits system on the literal split Borel and split normalizer. -/
def splitTitsSystem (n : ℕ) (hn : 0 < n) (D : Inputs (binaryParameters n hn)) :
    TitsSystem (X := SplitGroup (binaryParameters n hn)) := by
  letI := normalizer_intersection_normal n hn D
  refine {
    B := splitBorel (binaryParameters n hn)
    N := splitNormalizer (binaryParameters n hn)
    generate := ?_
    S := Set.range (quotientEquiv n hn D ∘ rootWeylGenerator)
    finite_S := Set.finite_range _
    involutions := by exact quotient_involutions n hn D
    quotient_generate := by exact quotient_generates n hn D
    exchange := by exact quotient_full_exchange n hn D
    nontrivial := by
      rintro _ ⟨i, rfl⟩
      exact quotient_nontrivial n hn D i
  }
  · rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    apply top_unique
    rw [← borel_sup_weyl_eq_top (binaryParameters n hn) rfl]
    exact sup_le_sup_left le_sup_right _

/-- The concrete double cosets coincide with the cells of the split Tits system. -/
theorem cell_eq_bruhatCell (n : ℕ) (hn : 0 < n) (D : Inputs (binaryParameters n hn))
    (w : rootWeylGroup) :
    letI := normalizer_intersection_normal n hn D
    cell D w = (splitTitsSystem n hn D).bruhatCell (quotientEquiv n hn D w) := by
  let := normalizer_intersection_normal n hn D
  exact cell_eq_quotient_cell n hn D w

end
end Triality.Standard.ConcreteBruhat.SplitNormalForm
