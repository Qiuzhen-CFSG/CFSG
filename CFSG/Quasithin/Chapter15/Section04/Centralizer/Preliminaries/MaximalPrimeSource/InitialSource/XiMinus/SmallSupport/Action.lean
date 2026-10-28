module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.Setup
public import Theory.GroupTheory.PCoreFrattiniQuotient
public import Theory.Representation.NormalElementaryQuotient

/-!
# The original odd image and its Frattini projection

For V = [R₂(XT),X], conjugation kills O₂(X). The image of X is therefore
a p-group and is exactly O_p(XT/C_XT(V)), since its quotient is a two-group.
The permitted X-kernel containment constructs a surjection from this actual
odd image onto the original (X/O₂(X))/Φ(X/O₂(X)), compatible with both
original quotient maps. No decomposition or automizer bound is assumed.

Source: Aschbacher–Smith, Lemma 3.2.13, printed pp.584–585.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
variable {G : Type*} [Group G] {T X : Subgroup G}

/-- The original XT modulo the centralizer of its original module. -/
abbrev sourceActionGroup (hX : X ∈ Chapter1.Xi G T) :=
  let := sourceModule_normal hX
  sourceGroup T X ⧸ centralizer (sourceModule T X : Set (sourceGroup T X))

/-- Normality of the original module gives the literal quotient group. -/
instance sourceActionGroup_group (hX : X ∈ Chapter1.Xi G T) :
    Group (sourceActionGroup hX) := by
  let := sourceModule_normal hX
  exact inferInstanceAs (Group (sourceGroup T X ⧸
    centralizer (sourceModule T X : Set (sourceGroup T X))))

/-- The canonical centralizer quotient map. -/
def sourceActionProjection (hX : X ∈ Chapter1.Xi G T) :
    sourceGroup T X →* sourceActionGroup hX :=
  let := sourceModule_normal hX
  QuotientGroup.mk' (centralizer (sourceModule T X : Set (sourceGroup T X)))

/-- The image of the original X inside that quotient. -/
def sourceOddImage (hX : X ∈ Chapter1.Xi G T) : Subgroup (sourceActionGroup hX) :=
  (X.subgroupOf (sourceGroup T X)).map (sourceActionProjection hX)

/-- The literal faithful conjugation representation on the original V. -/
noncomputable def sourceRepresentation (hX : X ∈ Chapter1.Xi G T) :
    Representation (ZMod 2) (sourceActionGroup hX) (Additive (sourceModule T X)) :=
  let := sourceModule_normal hX
  Representation.NormalElementaryQuotient.representation (sourceModule T X)
    (sourceActionProjection hX) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)


/-- O₂(X) acts trivially, since it lies in O₂(XT). -/
theorem source_twoCore_le_action_kernel (hX : X ∈ Chapter1.Xi G T) :
    pCore 2 X ≤ ((sourceActionProjection hX).comp
      (inclusion (show X ≤ sourceGroup T X from le_sup_left))).ker := by
  let := sourceModule_normal hX
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mpr
  apply sourceModule_core_centralizes T X
  have hc : X.pCoreIn 2 ≤ (sourceGroup T X).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le X.le_normalizer hX.invariant)
  obtain ⟨y, hy, he⟩ := hc (mem_map_of_mem X.subtype hx)
  exact (Subtype.ext he : y = inclusion (show X ≤ sourceGroup T X from le_sup_left) x) ▸ hy

/-- The odd image is a quotient of the original X/O₂(X). -/
theorem sourceOddImage_isPGroup (hX : X ∈ Chapter1.Xi G T) {p : ℕ} [Fact p.Prime]
    (hp : Chapter1.XiOddQuotient p (Chapter1.XiQuotient X)) :
    IsPGroup p (sourceOddImage hX) := by
  let := sourceModule_normal hX
  let f := (sourceActionProjection hX).comp
    (inclusion (show X ≤ sourceGroup T X from le_sup_left))
  have he : f.range = sourceOddImage hX := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨a, rfl⟩; exact a.property
    · intro hx; exact ⟨⟨x.val, hx⟩, rfl⟩
  have hk : pCore 2 X ≤ f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact source_twoCore_le_action_kernel hX
  let fq := QuotientGroup.lift (pCore 2 X) f.rangeRestrict hk
  have hs : Function.Surjective fq := by
    intro y
    obtain ⟨x, hx⟩ := f.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk x, hx⟩
  rw [← he]
  exact hp.isPGroup.of_surjective fq hs

/-- Relative normality of X in XT descends to the action quotient. -/
theorem sourceOddImage_normal (hX : X ∈ Chapter1.Xi G T) :
    (sourceOddImage hX).Normal := by
  let := sourceModule_normal hX
  let := hX.normal_in_join
  exact Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

/-- The image of the original T supplements the odd core. -/
theorem source_oddCore_quotient_isTwoGroup (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) {p : ℕ} [Fact p.Prime]
    (hp : Chapter1.XiOddQuotient p (Chapter1.XiQuotient X)) :
    IsPGroup 2 (sourceActionGroup hX ⧸ pCore p (sourceActionGroup hX)) := by
  let := sourceModule_normal hX
  let q := sourceActionProjection hX
  let U := (T.subgroupOf (sourceGroup T X)).map q
  have hXP : sourceOddImage hX ≤ pCore p (sourceActionGroup hX) :=
    le_sSup ⟨sourceOddImage_normal hX, sourceOddImage_isPGroup hX hp⟩
  have hsup : sourceOddImage hX ⊔ U = ⊤ := by
    rw [sourceOddImage, ← Subgroup.map_sup]
    have hgen : X.subgroupOf (sourceGroup T X) ⊔ T.subgroupOf (sourceGroup T X) = ⊤ := by
      rw [← subgroupOf_sup (show X ≤ sourceGroup T X from le_sup_left)
        (show T ≤ sourceGroup T X from le_sup_right)]
      exact subgroupOf_self _
    rw [hgen, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  exact isPGroup_quotient_of_sup_eq_top _ U (hT.comap_subtype.map q)
    (top_unique (hsup ▸ sup_le_sup_right hXP U))

/-- Modulo the odd image, the action group is an image of T. -/
theorem sourceOddImage_quotient_isTwoGroup (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) :
    let := sourceOddImage_normal hX
    IsPGroup 2 (sourceActionGroup hX ⧸ sourceOddImage hX) := by
  let := sourceOddImage_normal hX
  let := sourceModule_normal hX
  let q := sourceActionProjection hX
  let U := (T.subgroupOf (sourceGroup T X)).map q
  have hsup : sourceOddImage hX ⊔ U = ⊤ := by
    rw [sourceOddImage, ← Subgroup.map_sup]
    have hgen : X.subgroupOf (sourceGroup T X) ⊔ T.subgroupOf (sourceGroup T X) = ⊤ := by
      rw [← subgroupOf_sup (show X ≤ sourceGroup T X from le_sup_left)
        (show T ≤ sourceGroup T X from le_sup_right)]
      exact subgroupOf_self _
    rw [hgen, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  exact isPGroup_quotient_of_sup_eq_top _ U (hT.comap_subtype.map q) hsup

/-- The original odd image is precisely the actual odd core. -/
theorem sourceOddImage_eq_pCore (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hp : Chapter1.XiOddQuotient p (Chapter1.XiQuotient X)) :
    sourceOddImage hX = pCore p (sourceActionGroup hX) := by
  let := sourceOddImage_normal hX
  have hle : sourceOddImage hX ≤ pCore p (sourceActionGroup hX) :=
    le_sSup ⟨sourceOddImage_normal hX, sourceOddImage_isPGroup hX hp⟩
  apply le_antisymm hle
  let q := QuotientGroup.mk' (sourceOddImage hX)
  have hd : Disjoint ((pCore p (sourceActionGroup hX)).map q) ⊤ :=
    IsPGroup.disjoint_of_ne p 2 (by intro e; rw [e] at ho; norm_num at ho) _ _
      (pCore_isPGroup.map q) ((sourceOddImage_quotient_isTwoGroup hX hT).to_subgroup ⊤)
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  exact disjoint_def.mp hd (mem_map_of_mem q hx) (mem_top _)

/-- X maps onto its literal image in the centralizer quotient. -/
def sourceOddProjection (hX : X ∈ Chapter1.Xi G T) : X →* sourceOddImage hX :=
  ((sourceActionProjection hX).comp
    (inclusion (show X ≤ sourceGroup T X from le_sup_left))).codRestrict _
      (fun x => mem_map_of_mem _ x.property)

/-- Every element of the literal odd image comes from X. -/
theorem sourceOddProjection_surjective (hX : X ∈ Chapter1.Xi G T) :
    Function.Surjective (sourceOddProjection hX) := by
  rintro ⟨y, z, hz, rfl⟩
  exact ⟨⟨z.val, hz⟩, rfl⟩

/-- The hypothesis on the original X-kernel, expressed with the canonical inclusion. -/
def SourceKernelInFrattini (hX : X ∈ Chapter1.Xi G T) : Prop :=
  (sourceOddProjection hX).ker ≤
    (frattini (Chapter1.XiQuotient X)).comap (QuotientGroup.mk' (pCore 2 X))

/-- This is exactly the permitted centralizer-kernel containment. -/
theorem sourceKernelInFrattini_iff (hX : X ∈ Chapter1.Xi G T) :
    SourceKernelInFrattini hX ↔
      (centralizer (sourceModule T X : Set (sourceGroup T X))).comap
        (inclusion (show X ≤ sourceGroup T X from le_sup_left)) ≤
      (frattini (Chapter1.XiQuotient X)).comap (QuotientGroup.mk' (pCore 2 X)) := by
  let := sourceModule_normal hX
  have he : (sourceOddProjection hX).ker =
      (centralizer (sourceModule T X : Set (sourceGroup T X))).comap
        (inclusion (show X ≤ sourceGroup T X from le_sup_left)) := by
    ext x
    change (sourceOddProjection hX) x = 1 ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  unfold SourceKernelInFrattini
  rw [he]

/-- The image maps onto the original Frattini quotient, in the correct direction. -/
noncomputable def sourceFrattiniProjection (hX : X ∈ Chapter1.Xi G T)
    (hk : SourceKernelInFrattini hX) :
    sourceOddImage hX →* Chapter1.XiFrattiniQuotient X :=
  (sourceOddProjection hX).liftOfSurjective (sourceOddProjection_surjective hX)
    ⟨(QuotientGroup.mk' (frattini (Chapter1.XiQuotient X))).comp
      (QuotientGroup.mk' (pCore 2 X)), by
        intro x hx
        exact (QuotientGroup.eq_one_iff _).mpr (hk hx)⟩

/-- Compatibility with both original quotient maps. -/
theorem sourceFrattiniProjection_apply (hX : X ∈ Chapter1.Xi G T)
    (hk : SourceKernelInFrattini hX) (x : X) :
    sourceFrattiniProjection hX hk (sourceOddProjection hX x) =
      QuotientGroup.mk' (frattini (Chapter1.XiQuotient X))
        (QuotientGroup.mk' (pCore 2 X) x) := by
  unfold sourceFrattiniProjection
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- No element of the original Frattini quotient is lost. -/
theorem sourceFrattiniProjection_surjective (hX : X ∈ Chapter1.Xi G T)
    (hk : SourceKernelInFrattini hX) :
    Function.Surjective (sourceFrattiniProjection hX hk) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (frattini (Chapter1.XiQuotient X)) y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) z
  exact ⟨sourceOddProjection hX x, sourceFrattiniProjection_apply hX hk x⟩


end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
