module

public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.Product

universe u

set_option linter.style.haveILetI false

/-!
# Product subtori

This module constructs the external product of two closed subgroups as the
intersection of the inverse images under the two projections. Its carrier is
identified, as an algebraic group, with the product of the carrier varieties.

The product of two algebraic tori is proved to be a torus by splitting a
standard diagonal torus along a sum of dimensions. Consequently, if the two
factors are maximal tori, their product is maximal: the two projections of any
containing subtorus are subtori containing the factors, hence equal to them.
Coordinatewise membership then gives the reverse inclusion.

This standard direct-product construction supplies the maximal-torus input for
the product root-realization branch used in GLS3, Theorem 1.10.6.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

noncomputable section

/-- The external product of two closed subgroups, inside the product algebraic
group. -/
public noncomputable def ClosedSubgroup.prod
    {G₁ G₂ : Variety k} [hG₁ : AlgebraicGroup G₁]
    [hG₂ : AlgebraicGroup G₂]
    (T₁ : ClosedSubgroup G₁) (T₂ : ClosedSubgroup G₂) :
    @ClosedSubgroup k _ (Variety.prod G₁ G₂)
      (@AlgebraicGroup.prod k _ G₁ G₂ hG₁ hG₂) := by
  letI : AlgebraicGroup (Variety.prod G₁ G₂) :=
    AlgebraicGroup.prod G₁ G₂
  exact ((Morphism.fst G₁ G₂).closedSubgroupPreimage T₁).inter
    ((Morphism.snd G₁ G₂).closedSubgroupPreimage T₂)

/-- A point belongs to a product closed subgroup exactly when its two
coordinates belong to the corresponding factors. -/
public lemma ClosedSubgroup.mem_prod_iff
    {G₁ G₂ : Variety k} [AlgebraicGroup G₁] [AlgebraicGroup G₂]
    (T₁ : ClosedSubgroup G₁) (T₂ : ClosedSubgroup G₂)
    (x : Variety.Point (Variety.prod G₁ G₂)) :
    x ∈ T₁.prod T₂ ↔
      (Variety.prodPointEquiv G₁ G₂ x).1 ∈ T₁ ∧
      (Variety.prodPointEquiv G₁ G₂ x).2 ∈ T₂ := by
  rfl

private noncomputable def prodRightUnitIso
    (G : Variety k) [hG : AlgebraicGroup G] :
    @AlgebraicGroup.Iso k _ (Variety.prod G (dVariety k 0)) G
      (@AlgebraicGroup.prod k _ G (dVariety k 0) hG
        (dAlgebraicGroup k 0)) hG := by
  letI : AlgebraicGroup (dVariety k 0) := dAlgebraicGroup k 0
  letI : AlgebraicGroup (Variety.prod G (dVariety k 0)) :=
    AlgebraicGroup.prod G (dVariety k 0)
  exact Iso.ofInverseMorphisms
    (Morphism.fst G (dVariety k 0))
    (Morphism.prod (Morphism.id G)
      { toVariety := Variety.Morphism.const _ _ 1
        map_one := rfl
        map_mul := by intro _ _; exact (one_mul 1).symm })
    (by
      intro z
      apply (Variety.prodPointEquiv G (dVariety k 0)).injective
      apply Prod.ext
      · rfl
      · apply (dPointEquiv 0).injective
        funext i
        exact Fin.elim0 i)
    (by intro x; rfl)

private noncomputable def prodAssocIso
    (G H I : Variety k) [hG : AlgebraicGroup G] [hH : AlgebraicGroup H]
    [hI : AlgebraicGroup I] :
    @AlgebraicGroup.Iso k _ (Variety.prod (Variety.prod G H) I)
      (Variety.prod G (Variety.prod H I))
      (@AlgebraicGroup.prod k _ (Variety.prod G H) I
        (@AlgebraicGroup.prod k _ G H hG hH) hI)
      (@AlgebraicGroup.prod k _ G (Variety.prod H I) hG
        (@AlgebraicGroup.prod k _ H I hH hI)) := by
  letI : AlgebraicGroup (Variety.prod G H) := AlgebraicGroup.prod G H
  letI : AlgebraicGroup (Variety.prod H I) := AlgebraicGroup.prod H I
  letI : AlgebraicGroup (Variety.prod (Variety.prod G H) I) :=
    AlgebraicGroup.prod (Variety.prod G H) I
  letI : AlgebraicGroup (Variety.prod G (Variety.prod H I)) :=
    AlgebraicGroup.prod G (Variety.prod H I)
  exact Iso.ofInverseMorphisms
    (Morphism.prod
      ((Morphism.fst G H).comp (Morphism.fst (Variety.prod G H) I))
      (Morphism.prod
        ((Morphism.snd G H).comp (Morphism.fst (Variety.prod G H) I))
        (Morphism.snd (Variety.prod G H) I)))
    (Morphism.prod
      (Morphism.prod
        (Morphism.fst G (Variety.prod H I))
        ((Morphism.fst H I).comp (Morphism.snd G (Variety.prod H I))))
      ((Morphism.snd H I).comp (Morphism.snd G (Variety.prod H I))))
    (by
      intro x
      apply (Variety.prodPointEquiv (Variety.prod G H) I).injective
      apply Prod.ext
      · apply (Variety.prodPointEquiv G H).injective
        rfl
      · rfl)
    (by
      intro x
      apply (Variety.prodPointEquiv G (Variety.prod H I)).injective
      apply Prod.ext
      · rfl
      · apply (Variety.prodPointEquiv H I).injective
        rfl)

private noncomputable def diagonalProdIso (n m : ℕ) :
    @AlgebraicGroup.Iso k _ (dVariety k (n + m))
      (Variety.prod (dVariety k n) (dVariety k m))
      (dAlgebraicGroup k (n + m))
      (@AlgebraicGroup.prod k _ (dVariety k n) (dVariety k m)
        (dAlgebraicGroup k n) (dAlgebraicGroup k m)) := by
  letI : AlgebraicGroup (dVariety k n) := dAlgebraicGroup k n
  letI : AlgebraicGroup (dVariety k m) := dAlgebraicGroup k m
  letI : AlgebraicGroup (dVariety k (n + m)) := dAlgebraicGroup k (n + m)
  letI : AlgebraicGroup (Variety.prod (dVariety k n) (dVariety k m)) :=
    AlgebraicGroup.prod (dVariety k n) (dVariety k m)
  induction m with
  | zero =>
      simpa using (prodRightUnitIso (k := k) (dVariety k n)).symm
  | succ m ih =>
      letI : AlgebraicGroup (KMult k) := dAlgebraicGroup k 1
      letI : AlgebraicGroup (dVariety k (m + 1)) := dAlgebraicGroup k (m + 1)
      letI : AlgebraicGroup (dVariety k (n + m + 1)) :=
        dAlgebraicGroup k (n + m + 1)
      letI : AlgebraicGroup
          (Variety.prod (dVariety k n) (dVariety k m)) :=
        AlgebraicGroup.prod _ _
      letI : AlgebraicGroup
          (Variety.prod (dVariety k (n + m)) (KMult k)) :=
        AlgebraicGroup.prod _ _
      letI : AlgebraicGroup
          (Variety.prod (Variety.prod (dVariety k n) (dVariety k m))
            (KMult k)) := AlgebraicGroup.prod _ _
      letI : AlgebraicGroup
          (Variety.prod (dVariety k m) (KMult k)) :=
        AlgebraicGroup.prod _ _
      letI : AlgebraicGroup
          (Variety.prod (dVariety k n)
            (Variety.prod (dVariety k m) (KMult k))) :=
        AlgebraicGroup.prod _ _
      letI : AlgebraicGroup
          (Variety.prod (dVariety k n) (dVariety k (m + 1))) :=
        AlgebraicGroup.prod _ _
      have hsplit : AlgebraicGroup.Iso (dVariety k (n + m + 1))
          (Variety.prod (dVariety k (n + m)) (KMult k)) :=
        dVarietySuccProdIso (n + m)
      have hih : AlgebraicGroup.Iso
          (Variety.prod (dVariety k (n + m)) (KMult k))
          (Variety.prod (Variety.prod (dVariety k n) (dVariety k m))
            (KMult k)) :=
        Iso.prod ih (Iso.id (KMult k))
      have hassoc : AlgebraicGroup.Iso
          (Variety.prod (Variety.prod (dVariety k n) (dVariety k m))
            (KMult k))
          (Variety.prod (dVariety k n)
            (Variety.prod (dVariety k m) (KMult k))) :=
        prodAssocIso _ _ _
      have hlast : AlgebraicGroup.Iso
          (Variety.prod (dVariety k n)
            (Variety.prod (dVariety k m) (KMult k)))
          (Variety.prod (dVariety k n) (dVariety k (m + 1))) :=
        Iso.prod (Iso.id (dVariety k n)) (dVarietySuccProdIso m).symm
      simpa only [Nat.add_succ] using
        hlast.comp (hassoc.comp (hih.comp hsplit))

private theorem isTorus_prod
    {G₁ G₂ : Variety k} [hG₁ : AlgebraicGroup G₁]
    [hG₂ : AlgebraicGroup G₂]
    (h₁ : IsTorus G₁) (h₂ : IsTorus G₂) :
    @IsTorus k _ (Variety.prod G₁ G₂)
      (@AlgebraicGroup.prod k _ G₁ G₂ hG₁ hG₂) := by
  obtain ⟨n, ⟨e₁⟩⟩ := h₁
  obtain ⟨m, ⟨e₂⟩⟩ := h₂
  letI : AlgebraicGroup (dVariety k n) := dAlgebraicGroup k n
  letI : AlgebraicGroup (dVariety k m) := dAlgebraicGroup k m
  letI : AlgebraicGroup (Variety.prod (dVariety k n) (dVariety k m)) :=
    AlgebraicGroup.prod _ _
  letI : AlgebraicGroup (Variety.prod G₁ G₂) := AlgebraicGroup.prod _ _
  exact ⟨n + m, ⟨(Iso.prod e₁ e₂).comp (diagonalProdIso n m)⟩⟩

/-- The carrier algebraic group of a product closed subgroup is the product of
the two carrier algebraic groups. -/
public noncomputable def ClosedSubgroup.prodCarrierIso
    {G₁ G₂ : Variety k} [AlgebraicGroup G₁] [AlgebraicGroup G₂]
    (T₁ : ClosedSubgroup G₁) (T₂ : ClosedSubgroup G₂) :
    @AlgebraicGroup.Iso k _ (T₁.prod T₂).carrierVariety
      (Variety.prod T₁.carrierVariety T₂.carrierVariety)
      (T₁.prod T₂).carrierAlgebraicGroup
      (@AlgebraicGroup.prod k _ T₁.carrierVariety T₂.carrierVariety
        T₁.carrierAlgebraicGroup T₂.carrierAlgebraicGroup) := by
  letI : AlgebraicGroup (Variety.prod G₁ G₂) := AlgebraicGroup.prod _ _
  let P := T₁.prod T₂
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  letI : AlgebraicGroup T₁.carrierVariety := T₁.carrierAlgebraicGroup
  letI : AlgebraicGroup T₂.carrierVariety := T₂.carrierAlgebraicGroup
  letI : AlgebraicGroup
      (Variety.prod T₁.carrierVariety T₂.carrierVariety) :=
    AlgebraicGroup.prod _ _
  let f₁ : Morphism P.carrierVariety T₁.carrierVariety :=
    ((Morphism.fst G₁ G₂).comp P.inclusion).codRestrictClosedSubgroup T₁
      (fun x => (T₁.mem_prod_iff T₂ (P.inclusion.onPoints x)).mp
        (P.pointEquiv x).property |>.1)
  let f₂ : Morphism P.carrierVariety T₂.carrierVariety :=
    ((Morphism.snd G₁ G₂).comp P.inclusion).codRestrictClosedSubgroup T₂
      (fun x => (T₁.mem_prod_iff T₂ (P.inclusion.onPoints x)).mp
        (P.pointEquiv x).property |>.2)
  let forward := Morphism.prod f₁ f₂
  let ambientBackward : Morphism
      (Variety.prod T₁.carrierVariety T₂.carrierVariety)
      (Variety.prod G₁ G₂) :=
    Morphism.prod
      (T₁.inclusion.comp (Morphism.fst T₁.carrierVariety T₂.carrierVariety))
      (T₂.inclusion.comp (Morphism.snd T₁.carrierVariety T₂.carrierVariety))
  have hback (x : Variety.Point
      (Variety.prod T₁.carrierVariety T₂.carrierVariety)) :
      ambientBackward.onPoints x ∈ P := by
    rw [T₁.mem_prod_iff T₂]
    change T₁.inclusion.onPoints
        (Variety.prodPointEquiv T₁.carrierVariety T₂.carrierVariety x).1 ∈ T₁ ∧
      T₂.inclusion.onPoints
        (Variety.prodPointEquiv T₁.carrierVariety T₂.carrierVariety x).2 ∈ T₂
    exact ⟨(T₁.pointEquiv _).property, (T₂.pointEquiv _).property⟩
  let backward := ambientBackward.codRestrictClosedSubgroup P hback
  have hf₁ (x : Variety.Point P.carrierVariety) :
      T₁.inclusion.onPoints (f₁.onPoints x) =
        ((Morphism.fst G₁ G₂).comp P.inclusion).onPoints x := by
    simpa [f₁] using
      (Morphism.codRestrictClosedSubgroup_inclusion_apply
        ((Morphism.fst G₁ G₂).comp P.inclusion) T₁ _ x)
  have hf₂ (x : Variety.Point P.carrierVariety) :
      T₂.inclusion.onPoints (f₂.onPoints x) =
        ((Morphism.snd G₁ G₂).comp P.inclusion).onPoints x := by
    simpa [f₂] using
      (Morphism.codRestrictClosedSubgroup_inclusion_apply
        ((Morphism.snd G₁ G₂).comp P.inclusion) T₂ _ x)
  have hbackward (x : Variety.Point
      (Variety.prod T₁.carrierVariety T₂.carrierVariety)) :
      P.inclusion.onPoints (backward.onPoints x) =
        ambientBackward.onPoints x := by
    simpa [backward] using
      (Morphism.codRestrictClosedSubgroup_inclusion_apply
        ambientBackward P hback x)
  exact Iso.ofInverseMorphisms forward backward
    (by
      intro x
      apply P.inclusion_injective
      rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
      apply (Variety.prodPointEquiv G₁ G₂).injective
      apply Prod.ext
      · change T₁.inclusion.onPoints (f₁.onPoints x) =
          (Variety.prodPointEquiv G₁ G₂ (P.inclusion.onPoints x)).1
        exact (hf₁ x).trans rfl
      · change T₂.inclusion.onPoints (f₂.onPoints x) =
          (Variety.prodPointEquiv G₁ G₂ (P.inclusion.onPoints x)).2
        exact (hf₂ x).trans rfl)
    (by
      intro x
      apply (Variety.prodPointEquiv T₁.carrierVariety T₂.carrierVariety).injective
      apply Prod.ext
      · change f₁.onPoints (backward.onPoints x) =
          (Variety.prodPointEquiv T₁.carrierVariety T₂.carrierVariety x).1
        apply T₁.inclusion_injective
        calc
          T₁.inclusion.onPoints (f₁.onPoints (backward.onPoints x)) =
              ((Morphism.fst G₁ G₂).comp P.inclusion).onPoints
                (backward.onPoints x) := hf₁ _
          _ = (Morphism.fst G₁ G₂).onPoints
                (ambientBackward.onPoints x) :=
            congrArg (Morphism.fst G₁ G₂).onPoints (hbackward x)
          _ = T₁.inclusion.onPoints
                (Variety.prodPointEquiv T₁.carrierVariety
                  T₂.carrierVariety x).1 := rfl
      · change f₂.onPoints (backward.onPoints x) =
          (Variety.prodPointEquiv T₁.carrierVariety T₂.carrierVariety x).2
        apply T₂.inclusion_injective
        calc
          T₂.inclusion.onPoints (f₂.onPoints (backward.onPoints x)) =
              ((Morphism.snd G₁ G₂).comp P.inclusion).onPoints
                (backward.onPoints x) := hf₂ _
          _ = (Morphism.snd G₁ G₂).onPoints
                (ambientBackward.onPoints x) :=
            congrArg (Morphism.snd G₁ G₂).onPoints (hbackward x)
          _ = T₂.inclusion.onPoints
                (Variety.prodPointEquiv T₁.carrierVariety
                  T₂.carrierVariety x).2 := rfl)

private theorem ClosedSubgroup.prod_isSubtorus
    {G₁ G₂ : Variety k} [AlgebraicGroup G₁] [AlgebraicGroup G₂]
    {T₁ : ClosedSubgroup G₁} {T₂ : ClosedSubgroup G₂}
    (h₁ : IsSubtorus T₁) (h₂ : IsSubtorus T₂) :
    IsSubtorus (T₁.prod T₂) := by
  letI : AlgebraicGroup (Variety.prod G₁ G₂) := AlgebraicGroup.prod _ _
  let P := T₁.prod T₂
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  letI : AlgebraicGroup T₁.carrierVariety := T₁.carrierAlgebraicGroup
  letI : AlgebraicGroup T₂.carrierVariety := T₂.carrierAlgebraicGroup
  letI : AlgebraicGroup
      (Variety.prod T₁.carrierVariety T₂.carrierVariety) :=
    AlgebraicGroup.prod _ _
  let e := T₁.prodCarrierIso T₂
  obtain ⟨n, ⟨d⟩⟩ := isTorus_prod h₁ h₂
  exact ⟨n, ⟨e.symm.comp d⟩⟩

section

variable [IsAlgClosed k]

/-- The external product of two maximal tori is a maximal torus of the product
algebraic group. -/
public theorem IsMaximalTorus.prod
    {G₁ G₂ : Variety k} [AlgebraicGroup G₁] [AlgebraicGroup G₂]
    {T₁ : ClosedSubgroup G₁} {T₂ : ClosedSubgroup G₂}
    (h₁ : IsMaximalTorus T₁) (h₂ : IsMaximalTorus T₂) :
    IsMaximalTorus (T₁.prod T₂) := by
  refine ⟨ClosedSubgroup.prod_isSubtorus h₁.1 h₂.1, ?_⟩
  intro S hS hPS
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let p₁ : Morphism S.carrierVariety G₁ :=
    (Morphism.fst G₁ G₂).comp S.inclusion
  let p₂ : Morphism S.carrierVariety G₂ :=
    (Morphism.snd G₁ G₂).comp S.inclusion
  have himage₁ : IsSubtorus p₁.imageClosedSubgroup :=
    morphism_image_isTorus p₁ hS
  have himage₂ : IsSubtorus p₂.imageClosedSubgroup :=
    morphism_image_isTorus p₂ hS
  have hT₁image : T₁ ≤ p₁.imageClosedSubgroup := by
    intro x hx
    let z := (Variety.prodPointEquiv G₁ G₂).symm (x, 1)
    have hzP : z ∈ T₁.prod T₂ := by
      rw [T₁.mem_prod_iff T₂]
      constructor
      · simpa [z] using hx
      · change (1 : Variety.Point G₂) ∈ T₂
        exact T₂.toSubgroup.one_mem
    have hzS : z ∈ S := hPS hzP
    let zS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨z, hzS⟩
    change x ∈ Set.range p₁.onPoints
    refine ⟨zS, ?_⟩
    change (Variety.prodPointEquiv G₁ G₂ z).1 = x
    simp [z]
  have hT₂image : T₂ ≤ p₂.imageClosedSubgroup := by
    intro y hy
    let z := (Variety.prodPointEquiv G₁ G₂).symm (1, y)
    have hzP : z ∈ T₁.prod T₂ := by
      rw [T₁.mem_prod_iff T₂]
      constructor
      · change (1 : Variety.Point G₁) ∈ T₁
        exact T₁.toSubgroup.one_mem
      · simpa [z] using hy
    have hzS : z ∈ S := hPS hzP
    let zS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨z, hzS⟩
    change y ∈ Set.range p₂.onPoints
    refine ⟨zS, ?_⟩
    change (Variety.prodPointEquiv G₁ G₂ z).2 = y
    simp [z]
  have himage₁ : p₁.imageClosedSubgroup = T₁ := h₁.2 _ himage₁ hT₁image
  have himage₂ : p₂.imageClosedSubgroup = T₂ := h₂.2 _ himage₂ hT₂image
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro z hzS
    change z ∈ T₁.prod T₂
    rw [T₁.mem_prod_iff T₂]
    constructor
    · rw [← himage₁]
      change (Variety.prodPointEquiv G₁ G₂ z).1 ∈ Set.range p₁.onPoints
      exact ⟨S.pointEquiv.symm ⟨z, hzS⟩, by rfl⟩
    · rw [← himage₂]
      change (Variety.prodPointEquiv G₁ G₂ z).2 ∈ Set.range p₂.onPoints
      exact ⟨S.pointEquiv.symm ⟨z, hzS⟩, by rfl⟩
  · exact hPS

end

end

end Theory.AlgebraicGroup
