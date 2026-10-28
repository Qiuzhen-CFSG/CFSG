module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.ElementaryNine.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.QuotientActions
public import Theory.SpecificGroups.GL2.ThreeResidualImages
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.Quotient

/-!
# The actual elementary-nine image from the local elementary quotient

A two-perfect subgroup of GL₂(3) is trivial, cubic, or SL₂(3). Orbit counting
makes the cubic case fix a nonidentity point of the original P*. Relative
normalization by L₁T preserves the centralizer of L₁*, so the actual source
irreducibility excludes that case.

If L₁* centralizes P*, generation by P* and L₁*T* makes L₁* normal in H*.
Only then does the original quotient map identify L₁* with L₁/O₂(L₁).
When this local quotient is elementary abelian of exponent three, the join
with P* is elementary abelian. The strong-quasithin rank bound forces the
join to equal P*, contradicting noncontainment. Thus the matrix image
contains SL₂(3). The determinant gives the exact SL₂(3)/GL₂(3) alternative.

The terminal source adapters derive two-perfectness and relative normalization
from the genuine `LocalSetup`. They still require the independent local
quotient theorem, the `elementary` clause of `Extraspecial.CubicGeneration`.
Constructing that quotient from the actual simple or covered local model
remains a separate source obligation; these adapters do not complete 13.8.13.
No action-image or centralizer conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Notation
13.2.1 and Lemma 13.2.2, printed pp.877–878; proof of 13.8.13, printed
p.951 (PDF p.968), lines 48446–48454 of the extracted manuscript.
-/

public section

open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine
open Representation.AffineNine
open Matrix.GeneralLinearGroup
namespace SourceImage
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

variable {K : Type*} [Group K]

/-- Orbit counting on the actual coordinate plane gives a nonidentity
centralizing element when the matrix image is a three-group. -/
theorem fixed_point_of_three_image {P D : Subgroup K}
    (a : ConjugationCoordinates P) (hC : IsPGroup 3 (D.map a.action)) :
    P ⊓ centralizer (D : Set K) ≠ ⊥ := by
  let C := D.map a.action
  let : MulDistribMulAction C Translation :=
    MulDistribMulAction.compHom Translation (naturalAction.comp C.subtype)
  have hone : (1 : Translation) ∈ MulAction.fixedPoints C Translation := by
    intro c
    exact map_one (naturalAction c.val)
  obtain ⟨w, hw, hw1⟩ := hC.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    Translation (by rw [Nat.card_eq_fintype_card]; decide) hone
  let p := a.coordinate.symm w
  have hp1 : (p : K) ≠ 1 := by
    intro hp
    apply hw1
    have hp' : p = 1 := Subtype.ext hp
    have he : a.coordinate p = 1 := by rw [hp', map_one]
    exact (he.symm.trans (a.coordinate.apply_symm_apply w))
  have hpC : (p : K) ∈ centralizer (D : Set K) := by
    intro d hd
    have he := a.conjugates d p
    have hw' : naturalAction (a.action d) w = w :=
      hw ⟨a.action d, mem_map_of_mem a.action hd⟩
    rw [show a.coordinate p = w from a.coordinate.apply_symm_apply _, hw'] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  intro hbot
  apply hp1
  exact mem_bot.mp (hbot ▸ (show (p : K) ∈ P ⊓ centralizer (D : Set K) from
    ⟨p.property, hpC⟩))

/-- A nontrivial normal two-perfect image in an irreducible ternary plane
is the special linear subgroup. Normality is relative to the specified actor. -/
theorem special_le_of_irreducible {P D J : Subgroup K} [P.Normal]
    (a : ConjugationCoordinates P)
    (hD : IsPPerfect 2 D) (hn : J ≤ normalizer (D : Set K))
    (hirr : ∀ N : Subgroup K, N ≤ P → J ≤ normalizer (N : Set K) →
      N = ⊥ ∨ N = P)
    (hne : ¬ D ≤ centralizer (P : Set K)) :
    threeSpecialLinear ≤ a.action.range := by
  let C := D.map a.action
  have hp : IsPPerfect 2 C :=
    hD.of_surjective (a.action.subgroupMap D) (a.action.subgroupMap_surjective D)
  have hCne : C ≠ ⊥ := by
    intro hc
    apply hne
    rw [← a.ker_eq_centralizer]
    exact (Subgroup.map_eq_bot_iff _).mp hc
  rcases three_twoPerfect_subgroup C hp hCne with hc | hc
  · have hfixed := fixed_point_of_three_image a (IsPGroup.of_card (n := 1) hc)
    let N := P ⊓ centralizer (D : Set K)
    have hnN : J ≤ normalizer (N : Set K) :=
      (le_inf le_normalizer_of_normal
        (hn.trans (normalizer_le_normalizer_centralizer D))).trans
          inf_normalizer_le_normalizer_inf
    have he : N = P := (hirr N inf_le_left hnN).resolve_left hfixed
    exact (hne (le_centralizer_iff.mp (he ▸ (show N ≤ centralizer (D : Set K) from
      inf_le_right)))).elim
  · rw [← hc]
    exact map_le_range _ _

/-- The determinant has only two possible values, so there is no subgroup
strictly between the actual special and general linear groups. -/
private theorem eq_special_or_top {C : Subgroup LinearGroup}
    (hS : threeSpecialLinear ≤ C) : C = threeSpecialLinear ∨ C = ⊤ := by
  by_cases he : C ≤ threeSpecialLinear
  · exact Or.inl (le_antisymm he hS)
  right
  obtain ⟨x, hxC, hxS⟩ := Set.not_subset.mp he
  apply top_unique
  intro g _
  by_cases hg : g ∈ threeSpecialLinear
  · exact hS hg
  have hd : det g = det x := by
    exact (show ∀ a b : (ZMod 3)ˣ, a ≠ 1 → b ≠ 1 → a = b by decide) _ _ hg hxS
  have hprod : g * x⁻¹ ∈ threeSpecialLinear := by
    change det (g * x⁻¹) = 1
    rw [map_mul, map_inv, hd, mul_inv_cancel]
  have hm := C.mul_mem (hS hprod) hxC
  simpa only [inv_mul_cancel_right] using hm

variable {G : Type*} [Group G] [Finite G]
  {H L₁ T M Vα : Subgroup G}

omit [Finite G] in
private theorem star_join (A B : Subgroup G) (hA : A ≤ H) (hB : B ≤ H) :
    Source.starImage H (A ⊔ B) = Source.starImage H A ⊔ Source.starImage H B := by
  unfold Source.starImage
  rw [subgroupOf_sup hA hB, Subgroup.map_sup]

omit [Finite G] in
private theorem star_self : Source.starImage H H = ⊤ := by
  unfold Source.starImage
  rw [subgroupOf_self, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]

/-- A centralizing L₁* would be normal, hence its intrinsic two-core quotient
would identify with L₁* itself. The quasithin bound then forces L₁* into P*. -/
theorem not_centralizes_of_local_elementary
    (r : ReducedOdd 3 H L₁ T M Vα)
    [IsElementaryAbelian 3 (Source.starImage H r.P)]
    [IsElementaryAbelian 3 (L₁ ⧸ pCore 2 L₁)]
    (hc : Nat.card (Source.starImage H r.P) = 9)
    (hr : IsStronglyQuasithin H)
    (hn : T ≤ normalizer (L₁ : Set G))
    (hout : ¬ Source.starImage H L₁ ≤ Source.starImage H r.P) :
    ¬ Source.starImage H L₁ ≤ centralizer (Source.starImage H r.P : Set _) := by
  intro hcent
  have hJH : L₁ ⊔ T ≤ H := r.generated ▸ le_sup_right
  have hLH : L₁ ≤ H := le_sup_left.trans hJH
  have hgen : Source.starImage H r.P ⊔ Source.starImage H (L₁ ⊔ T) = ⊤ := by
    rw [← star_join r.P (L₁ ⊔ T) r.P_le hJH, ← r.generated]
    exact star_self
  have hnormal : (Source.starImage H L₁).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le ((le_centralizer_iff.mp hcent).trans (centralizer_le_normalizer _))
      (starImage_normalizes H (sup_le L₁.le_normalizer hn))
  let e := normalStarEquiv H L₁ hLH hnormal
  let : IsElementaryAbelian 3 (Source.starImage H L₁) :=
    IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  let : IsElementaryAbelian 3 (Source.starImage H r.P ⊔ Source.starImage H L₁ : Subgroup _) :=
    IsElementaryAbelian.sup_of_le_centralizer hcent
  have hquot : primeRank 3 (Source.Hstar H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup).trans
      (hr 3 Nat.prime_three (by decide))
  have hbound := (primeRank_le_iff_elementary_card_le (Source.Hstar H)).mp hquot
    (Source.starImage H r.P ⊔ Source.starImage H L₁) inferInstance
  have he := eq_of_le_of_card_ge
    (show Source.starImage H r.P ≤ Source.starImage H r.P ⊔ Source.starImage H L₁ from le_sup_left)
    (by simpa only [hc, show (3 : ℕ) ^ 2 = 9 from rfl] using hbound)
  exact hout (he.symm ▸ le_sup_right)

/-- Conditional source assembly: its only additional local input is the
intrinsic elementary quotient proved by the cubic-generation source owner. -/
theorem special_le_of_local_elementary
    (r : ReducedOdd 3 H L₁ T M Vα)
    [IsElementaryAbelian 3 (Source.starImage H r.P)]
    [IsElementaryAbelian 3 (L₁ ⧸ pCore 2 L₁)]
    (hc : Nat.card (Source.starImage H r.P) = 9)
    (hr : IsStronglyQuasithin H) (hp : IsPPerfect 2 L₁)
    (hn : T ≤ normalizer (L₁ : Set G))
    (hout : ¬ Source.starImage H L₁ ≤ Source.starImage H r.P)
    (a : ConjugationCoordinates (Source.starImage H r.P)) :
    threeSpecialLinear ≤ a.action.range := by
  let := r.Pstar_normal
  have hLH : L₁ ≤ H := le_sup_left.trans (r.generated ▸ le_sup_right)
  have hD := hp.of_surjective (starMap H L₁ hLH)
    (starMap_surjective H L₁ hLH)
  exact special_le_of_irreducible a hD
    (starImage_normalizes H (sup_le L₁.le_normalizer hn))
    (source_irreducible r) (not_centralizes_of_local_elementary r hc hr hn hout)

end SourceImage

open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {H L V V₁ V₂ V₃ M G₁ Vα : Subgroup G} {T : Sylow 2 G}

/-- The local setup supplies the actual two-residual and its relative
normalization. Only the elementary intrinsic quotient remains to be supplied. -/
theorem source_special_image_of_local_elementary
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (r : ReducedOdd 3 H (sourceOne L T V₁) (T : Subgroup G) M Vα)
    [IsElementaryAbelian 3 (Source.starImage H r.P)]
    [IsElementaryAbelian 3 (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁))]
    (hc : Nat.card (Source.starImage H r.P) = 9)
    (hr : IsStronglyQuasithin H)
    (hout : ¬ Source.starImage H (sourceOne L T V₁) ≤ Source.starImage H r.P)
    (a : ConjugationCoordinates (Source.starImage H r.P)) :
    threeSpecialLinear ≤ a.action.range := by
  exact SourceImage.special_le_of_local_elementary r hc hr
    (Subgroup.isPPerfect_embedded_pResidual 2 _)
    (ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.T_normalizes_one
      L T V₁ d.line_stable) hout a

/-- The precise SL₂(3)/GL₂(3) alternative for the original conjugation map,
conditional only on the same independent local quotient theorem. -/
theorem source_image_alternative_of_local_elementary
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (r : ReducedOdd 3 H (sourceOne L T V₁) (T : Subgroup G) M Vα)
    [IsElementaryAbelian 3 (Source.starImage H r.P)]
    [IsElementaryAbelian 3 (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁))]
    (hc : Nat.card (Source.starImage H r.P) = 9)
    (hr : IsStronglyQuasithin H)
    (hout : ¬ Source.starImage H (sourceOne L T V₁) ≤ Source.starImage H r.P)
    (a : ConjugationCoordinates (Source.starImage H r.P)) :
    a.action.range = threeSpecialLinear ∨ a.action.range = ⊤ :=
  SourceImage.eq_special_or_top (source_special_image_of_local_elementary d r hc hr hout a)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine

end
