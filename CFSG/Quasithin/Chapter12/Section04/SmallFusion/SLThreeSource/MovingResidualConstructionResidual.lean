module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionRelative
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.NormalResidualOrbit
public import Theory.GroupTheory.PResidual.NormalClosureCover

/-!
# The original centralizing line and its residual

Use the actual normalizer action on L/O₂(L). Its kernel meets X in a
normal subgroup; the image of that intersection in X/O₂(X) is the
centralizing line. Its full preimage is the intersection joined with O₂(X).
The two-residual kills that two-group supplement and hence centralizes
L/O₂(L). C.1.10, with the natural binary-three endomorphism field computed
earlier, then centralizes L itself. Normality in XLT follows from its
construction and centralization, without assuming ambient normality of L.

The cubic-line order is an explicit source calculation. Conditional on it,
the canonical residual belongs to the corrected normal family and is
nontrivial. Quotient actions and embeddings remain literal throughout.

Source: Aschbacher–Smith, C.1.10 and proof of 12.4.6, printed pp.124,814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The actual normalizer action on the component's core quotient. -/
def componentCoreAction (L : Subgroup G) :
    normalizer (L : Set G) →* MulAut (L ⧸ pCore 2 L) :=
  (quotientAut (pCore 2 L)).comp L.normalizerMonoidHom

/-- Its kernel, embedded in the original ambient group. -/
def coreActionKernel (L : Subgroup G) : Subgroup G :=
  (componentCoreAction L).ker.map (normalizer (L : Set G)).subtype

/-- The actual kernel's image in the literal quotient of X. -/
def centralizingLine (L X : Subgroup G) : Subgroup (X ⧸ pCore 2 X) :=
  ((X ⊓ coreActionKernel L).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))

/-- Full preimage of the centralizing quotient image, in the original group. -/
def centralizingPreimage (L X : Subgroup G) : Subgroup G :=
  (X ⊓ coreActionKernel L) ⊔ (pCore 2 X).map X.subtype

/-- The source subgroup X₁, with its ambient embedding retained. -/
def centralizingResidual (L X : Subgroup G) : Subgroup G :=
  (pResidual 2 (centralizingPreimage L X)).map (centralizingPreimage L X).subtype

omit [Finite G] in
theorem coreActionKernel_le (L : Subgroup G) :
    coreActionKernel L ≤ normalizer (L : Set G) := map_subtype_le _

omit [Finite G] in
theorem normalizer_normalizes_coreActionKernel (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (coreActionKernel L : Set G) := by
  have hh := (componentCoreAction L).ker.le_normalizer_map
    (normalizer (L : Set G)).subtype
  simpa only [coreActionKernel, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh

omit [Finite G] in
theorem centralizingPreimage_le (L X : Subgroup G) :
    centralizingPreimage L X ≤ X := sup_le inf_le_left (map_subtype_le _)

omit [Finite G] in
theorem centralizingPreimage_as_quotient (L X : Subgroup G) :
    ((centralizingLine L X).comap (QuotientGroup.mk' (pCore 2 X))).map X.subtype =
      centralizingPreimage L X := by
  rw [centralizingLine, comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    map_subgroupOf_eq_of_le inf_le_left]
  rfl

theorem centralizingResidual_as_lift (L X : Subgroup G) :
    (NormalCubicLines.lift (centralizingLine L X)).map X.subtype =
      centralizingResidual L X := by
  rw [NormalCubicLines.lift, map_embedded_pResidual, centralizingPreimage_as_quotient]
  rfl

omit [Finite G] in
theorem centralizingResidual_le (L X : Subgroup G) :
    centralizingResidual L X ≤ X :=
  (map_subtype_le _).trans (centralizingPreimage_le L X)

omit [Finite G] in
theorem normalizes_centralizingResidual (L X : Subgroup G) :
    normalizer (L : Set G) ⊓ normalizer (X : Set G) ≤
      normalizer (centralizingResidual L X : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (centralizingPreimage L X) (pResidual 2 (centralizingPreimage L X)))
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_inf
  · exact (le_inf inf_le_right
      (inf_le_left.trans (normalizer_normalizes_coreActionKernel L))).trans
        inf_normalizer_le_normalizer_inf
  · exact inf_le_right.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))

theorem centralizingResidual_le_kernel (L X : Subgroup G)
    (hXM : X ≤ normalizer (L : Set G)) :
    centralizingResidual L X ≤ coreActionKernel L := by
  let K := (X ⊓ coreActionKernel L).subgroupOf X
  have hKn : K.Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf X.le_normalizer
      (hXM.trans (normalizer_normalizes_coreActionKernel L))).trans
        inf_normalizer_le_normalizer_inf)
  let := hKn
  have hh := embedded_pResidual_le_of_normal_sup_pGroup K (pCore 2 X)
    (K ⊔ pCore 2 X) pCore_isPGroup le_rfl
  have hpre : (centralizingLine L X).comap (QuotientGroup.mk' (pCore 2 X)) =
      K ⊔ pCore 2 X := by
    rw [centralizingLine, comap_map_eq, QuotientGroup.ker_mk']
  rw [← centralizingResidual_as_lift]
  apply (map_mono (f := X.subtype) (show NormalCubicLines.lift (centralizingLine L X) ≤ K from ?_)).trans
    ((map_subgroupOf_eq_of_le inf_le_left).le.trans inf_le_right)
  dsimp only [NormalCubicLines.lift]
  rw [hpre]
  exact hh

omit [Finite G] in
theorem coreActionKernel_commutator (L : Subgroup G) :
    ⁅coreActionKernel L, L⁆ ≤ (pCore 2 L).map L.subtype := by
  apply commutator_le.mpr
  rintro x ⟨a, ha, rfl⟩ l hl
  have he := DFunLike.congr_fun (MonoidHom.mem_ker.mp ha)
    (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩)
  change quotientAut (pCore 2 L) (L.normalizerMonoidHom a)
    (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩) = _ at he
  rw [quotientAut_apply_mk] at he
  let b := L.normalizerMonoidHom a ⟨l, hl⟩
  have hb : b * (⟨l, hl⟩ : L)⁻¹ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 L) (b * (⟨l, hl⟩ : L)⁻¹) = 1
    rw [map_mul, map_inv]
    exact mul_inv_eq_one.mpr he
  exact mem_map.mpr ⟨_, hb, rfl⟩

theorem centralizingResidual_centralizes (L X : Subgroup G)
    (hL : IsLinearTwoBlock L 3) (hXM : X ≤ normalizer (L : Set G)) :
    centralizingResidual L X ≤ centralizer (L : Set G) := by
  apply linearThree_centralizes_of_normalizes_coreQuotient L _ hL
    (isPPerfect_embedded_pResidual 2 _)
    ((centralizingResidual_le L X).trans hXM)
  exact (commutator_mono (centralizingResidual_le_kernel L X hXM) le_rfl).trans
    (coreActionKernel_commutator L)

theorem centralizingResidual_normal_join (L X T : Subgroup G)
    (hL : IsLinearTwoBlock L 3) (hXM : X ≤ normalizer (L : Set G))
    (hTM : T ≤ normalizer (L : Set G)) (hTX : T ≤ normalizer (X : Set G)) :
    ((centralizingResidual L X).subgroupOf (X ⊔ (L ⊔ T))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  refine sup_le ?_ (sup_le ?_ ?_)
  · exact (le_inf hXM X.le_normalizer).trans (normalizes_centralizingResidual L X)
  · exact (le_centralizer_iff.mp (centralizingResidual_centralizes L X hL hXM)).trans
      (Subgroup.centralizer_le_normalizer _)
  · exact (le_inf hTM hTX).trans (normalizes_centralizingResidual L X)

theorem centralizingResidual_mem (L X : Subgroup G)
    [IsElementaryAbelian 3 (X ⧸ pCore 2 X)]
    (hX : Nat.card (X ⧸ pCore 2 X) = 9)
    (hline : Nat.card (centralizingLine L X) = 3) :
    centralizingResidual L X ∈ normalCubicResiduals X := by
  rw [← centralizingResidual_as_lift]
  exact normalCubicResiduals_map_subtype X _ (NormalCubicLines.lift_mem hX _ hline)

omit [Finite G] in
/-- Centralization on representatives gives fixed points for the literal quotient action. -/
theorem quotientAction_fixes_of_centralizes (X Y : Subgroup G)
    (t : normalizer (X : Set G)) (ht : (t : G) ∈ centralizer (Y : Set G)) :
    ∀ z ∈ normalCubicResidualImage X Y, normalCubicQuotientAction X t z = z := by
  rintro z ⟨y, hy, rfl⟩
  change quotientAut (pCore 2 X) (X.normalizerMonoidHom t)
    (QuotientGroup.mk' (pCore 2 X) y) = QuotientGroup.mk' (pCore 2 X) y
  rw [quotientAut_apply_mk]
  apply congrArg (QuotientGroup.mk' (pCore 2 X))
  apply Subtype.ext
  change (t : G) * (y : G) * (t : G)⁻¹ = y
  have he := mem_centralizer_iff.mp ht (y : G) hy
  rw [← he, mul_inv_cancel_right]

theorem cubic_images_distinct_of_inverted_fixed {Q : Type*} [Group Q] [Finite Q]
    (A B : Subgroup Q) (hA : Nat.card A = 3) (a : MulAut Q)
    (hinv : ∀ z ∈ A, a z = z⁻¹) (hfix : ∀ z ∈ B, a z = z) : A ≠ B := by
  intro heq
  have hb : A = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    rw [mem_bot]
    have he : z = z⁻¹ := (hfix z (heq ▸ hz)).symm.trans (hinv z hz)
    have h2 : z ^ 2 = 1 := by
      rw [pow_two]
      conv_lhs => lhs; rw [he]
      exact inv_mul_cancel z
    have h3 : z ^ 3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨z, hz⟩ : A))
      rw [hA] at hh
      exact congrArg Subtype.val hh
    simpa only [pow_succ, h2, one_mul] using h3
  rw [hb, Subgroup.card_bot] at hA
  norm_num at hA

/-- The centralizing residual is nontrivial as soon as its quotient line is cubic. -/
theorem centralizingResidual_ne_bot (L X : Subgroup G)
    [IsElementaryAbelian 3 (X ⧸ pCore 2 X)]
    (hX : Nat.card (X ⧸ pCore 2 X) = 9)
    (hline : Nat.card (centralizingLine L X) = 3) :
    centralizingResidual L X ≠ ⊥ := by
  intro heq
  have hc := (centralizingResidual_mem L X hX hline).2.2.2
  rw [heq] at hc
  have he : Nat.card ((⊥ : Subgroup G) ⧸ pCore 2 (⊥ : Subgroup G)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  omega

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
