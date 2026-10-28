module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.OriginalCubicFiltration

/-!
# Fixed-space bounds for the induced original-seed chief sections

The chief projection on the conjugate span restricts to the intersection
with the original seed. Its kernel is precisely the lower intersection, so
it embeds the original induced section into the actual chief factor. An
actor centralizing the original orbit fixes this image. Consequently the
cubic displacement of an induced section is bounded by the fixed-space
dimension on the corresponding actual chief factor.

Source: Aschbacher--Smith, 3.1.9(6), printed p.578, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterD ChapterE
open MathieuCode.NormalizedShadowRows.CubicFiltration
section
variable {G : Type*} [Group G] (H V : Subgroup G)
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length)

set_option backward.isDefEq.respectTransparency false

/-- The original chief projection restricted to the upper seed intersection. -/
def seedChiefProjection :
    (seedTerm (seedNormalizerAction H V) (originalSeed H V)
      (normalizerTerm H V s i.succ)).toSubmodule →ₗ[ZMod 2] Additive (s.Factor i) := by
  let f : (seedTerm (seedNormalizerAction H V) (originalSeed H V)
      (normalizerTerm H V s i.succ)).toSubmodule →ₗ[ZMod 2]
      (s.linearTerm i.succ).toSubmodule := {
    toFun := fun v => ⟨v.val.val,v.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact (s.factorProjection i).comp f

/-- The induced section retains exactly the original lower seed intersection as kernel. -/
theorem seedChiefProjection_ker : (seedChiefProjection H V s i).ker =
    (sectionLower (originalSeed H V).toRepresentation
      (seedTerm (seedNormalizerAction H V) (originalSeed H V) (normalizerTerm H V s i.castSucc))
      (seedTerm (seedNormalizerAction H V) (originalSeed H V) (normalizerTerm H V s i.succ))).toSubmodule := by
  ext v
  change s.factorProjection i ⟨v.val.val,v.property⟩ = 0 ↔ _
  change (⟨v.val.val,v.property⟩ : (s.linearTerm i.succ).toSubmodule) ∈
    (s.factorProjection i).ker ↔ _
  rw [s.factorProjection_ker]
  rfl

/-- Canonical injection of the original seed section into the actual group chief factor. -/
def seedChiefInjection :=
  Submodule.liftQ _ (seedChiefProjection H V s i) (seedChiefProjection_ker H V s i).ge

theorem seedChiefInjection_injective : Function.Injective (seedChiefInjection H V s i) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (seedChiefProjection_ker H V s i).le

/-- Every original element centralizing V fixes the image in every original chief factor. -/
theorem seedChiefInjection_fixed (A : Subgroup H)
    (hA : A.map H.subtype ≤ centralizer (V : Set G)) (v) :
    seedChiefInjection H V s i v ∈ fixedSpace (s.factorRepresentation i) A := by
  induction v using Submodule.Quotient.induction_on with
  | _ w =>
    intro a
    change s.factorRepresentation i a (s.factorProjection i ⟨w.val.val,w.property⟩) =
      s.factorProjection i ⟨w.val.val,w.property⟩
    rw [← s.factorLinearEquiv_mk, ← s.factorLinearEquiv_equivariant]
    apply (s.factorLinearEquiv i).congr_arg
    change Submodule.Quotient.mk
      ((s.linearTerm i.succ).toRepresentation a ⟨w.val.val,w.property⟩) =
        Submodule.Quotient.mk ⟨w.val.val,w.property⟩
    congr 1
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change ((a : H) : G) * ((w.val.val.toMul : H) : G) * ((a : H) : G)⁻¹ =
      ((w.val.val.toMul : H) : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact ((hA (mem_map_of_mem H.subtype a.property)) _ w.val.property).symm

variable [Finite G]

/-- Cubic movement in the original seed section is bounded by that same chief fixed space. -/
theorem originalSeedFactor_codim_le_fixed (A : Subgroup H)
    (hA : A.map H.subtype ≤ centralizer (V : Set G)) (b : seedNormalizer H V) :
    fixedCodim (originalSeedFactor H V s i) (zpowers b) ≤
      Module.finrank (ZMod 2) (fixedSpace (s.factorRepresentation i) A) := by
  have h := fixedCodim_add_finrank (originalSeedFactor H V s i) (zpowers b)
  let f := (seedChiefInjection H V s i).codRestrict
    (fixedSpace (s.factorRepresentation i) A) (seedChiefInjection_fixed H V s i A hA)
  have hf : Function.Injective f := by
    intro v w hvw
    exact seedChiefInjection_injective H V s i (congrArg Subtype.val hvw)
  have hle := LinearMap.finrank_le_finrank_of_injective hf
  omega

end

section
variable {G X : Type*} [Group G] [Finite G] [Group X] (H V : Subgroup G)
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  [IsElementaryAbelian 2 V]
set_option backward.isDefEq.respectTransparency false in
/-- The original cubic has a large section in every chief series, fixed by the same actor. -/
theorem cubic_large_fixedSpace (hVH : V ≤ H) (A : Subgroup H)
    (hA : A.map H.subtype ≤ centralizer (V : Set G))
    (B : Subgroup H) (q : H →* X) (hcub : CubicOrbitChiefs (V := V) B q)
    (htwo : ∀ s : SeriesOn ((conjugateSpan H V).subgroupOf H), s.noncentralCount = 2) :
    ∃ b : B,
      orderOf (actionHom (normalRepresentation ((conjugateSpan H V).subgroupOf H)) (b : H)) = 3 ∧
      orderOf (q (b : H)) = 3 ∧
      ∃ hn : ((b : H) : G) ∈ normalizer (V : Set G),
        orderOf (V.normalizerMonoidHom.rangeRestrict ⟨((b : H) : G),hn⟩) = 3 ∧
        ∀ s : SeriesOn ((conjugateSpan H V).subgroupOf H),
          ∃ i : Fin s.series.length, ¬ s.Central i ∧
            3 ≤ fixedCodim (originalSeedFactor H V s i) (zpowers ⟨(b : H),hn⟩) ∧
            3 ≤ Module.finrank (ZMod 2) (fixedSpace (s.factorRepresentation i) A) := by
  obtain ⟨b,hb,hqb,hn,hz,hc,_⟩ := hcub
  refine ⟨b,hb,hqb,hn,hz,?_⟩
  intro s
  obtain ⟨i,hi,hlarge⟩ := exists_large_originalSeedFactor H V hVH (b : H) hn hb hz hc s (htwo s)
  exact ⟨i,hi,hlarge,hlarge.trans (originalSeedFactor_codim_le_fixed H V s i A hA ⟨(b : H),hn⟩)⟩
end

end CFSG.Quasithin.Chapter8.MathieuShadowRows
