module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsOmega
public import Theory.Representation.BinarySevenCode.PointStabilizerMap

/-!
# The actual two point-stabilizer factors before the terminal product

The supplied full S₇ action maps N_G(V)∩C_G(e) onto S₄×S₃, with its
original module centralizer as kernel. The two block preimages are normal
in that literal point normalizer and generate it; their images and both
letter-action formulas are retained.

These are the source M₁ and M₂ before taking prime-to-three residuals.
Identifying those residuals with the separately defined L₁ and L₂ remains
the local-factor obligation of qt-d-1231-terminal-product.
Source: Aschbacher--Smith, paragraph preceding 12.3.13, printed p.811.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- The original module normalizer restricted to the selected point. -/
abbrev pointNormalizer : Subgroup G := NormalizerModel.pointNormalizer P.point

/-- The original point action, marked by support and complementary letters. -/
def pointBlockAction : P.pointNormalizer →*
    (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3)) :=
  (WeightFourLocal.pointEquiv _ P.weight_four).toMonoidHom.comp
    (D.model.pointPermutation P.point)

theorem pointBlockAction_surjective
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : Function.Surjective P.pointBlockAction :=
  (WeightFourLocal.pointEquiv _ P.weight_four).surjective.comp
    (D.model.pointPermutation_surjective
      (MonoidHom.range_eq_top.mp (D.permutation_range_eq_top structural escape)) P.point)

theorem pointBlockAction_ker : P.pointBlockAction.ker =
    (centralizer (V : Set G)).subgroupOf P.pointNormalizer := by
  rw [pointBlockAction,MonoidHom.ker_comp_of_injective _ _
    (WeightFourLocal.pointEquiv _ P.weight_four).injective,D.model.pointPermutation_ker]

/-- This is the exact M_V point stabilizer used in the source. -/
theorem pointNormalizer_le_original
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    P.pointNormalizer ≤ normalizer (L : Set G) :=
  inf_le_left.trans (S.normalizer_le_component structural)

/-- The source point quotient, without changing its centralizer denominator. -/
def pointNormalizerQuotientEquiv
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    (P.pointNormalizer ⧸ (centralizer (V : Set G)).subgroupOf P.pointNormalizer) ≃*
      (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3)) :=
  D.model.weightFourPointQuotientEquiv
    (MonoidHom.range_eq_top.mp (D.permutation_range_eq_top structural escape))
    P.point P.weight_four

theorem pointNormalizerQuotientEquiv_apply
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (n : P.pointNormalizer) :
    P.pointNormalizerQuotientEquiv structural escape (QuotientGroup.mk'
      ((centralizer (V : Set G)).subgroupOf P.pointNormalizer) n) =
        P.pointBlockAction n := rfl

/-- The four-letter factor acts on the literal support of the chosen point. -/
theorem pointBlockAction_first (n : P.pointNormalizer)
    (i : WeightFourLocal.Support (D.model.coordinates P.point).toAdd) :
    (P.pointBlockAction n).1 (WeightFourLocal.fourLetters _ P.weight_four i) =
      WeightFourLocal.fourLetters _ P.weight_four
        (WeightFourLocal.supportPermutation _ (D.model.pointPermutation P.point n) i) :=
  WeightFourLocal.pointEquiv_first _ P.weight_four _ i

/-- The three-letter factor acts on the literal complementary support. -/
theorem pointBlockAction_second (n : P.pointNormalizer)
    (i : WeightTwoGeometry.Complement (D.model.coordinates P.point).toAdd) :
    (P.pointBlockAction n).2 (WeightFourLocal.threeLetters _ P.weight_four i) =
      WeightFourLocal.threeLetters _ P.weight_four
        (WeightTwoGeometry.complementPermutation _ (D.model.pointPermutation P.point n) i) :=
  WeightFourLocal.pointEquiv_second _ P.weight_four _ i

/-- The full preimage of the factor acting on the four support letters. -/
def firstPointFactor : Subgroup G :=
  (((⊤ : Subgroup (Equiv.Perm (Fin 4))).prod ⊥).comap P.pointBlockAction).map
    P.pointNormalizer.subtype

/-- The full preimage of the factor acting on the three complementary letters. -/
def secondPointFactor : Subgroup G :=
  (((⊥ : Subgroup (Equiv.Perm (Fin 4))).prod ⊤).comap P.pointBlockAction).map
    P.pointNormalizer.subtype

theorem firstPointFactor_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    (P.firstPointFactor.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (⊤ : Subgroup (Equiv.Perm (Fin 4))).prod ⊥ := by
  rw [firstPointFactor,←comap_subtype,
    comap_map_eq_self_of_injective P.pointNormalizer.subtype_injective]
  exact map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr
    (P.pointBlockAction_surjective structural escape)]; exact le_top)

theorem secondPointFactor_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    (P.secondPointFactor.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (⊥ : Subgroup (Equiv.Perm (Fin 4))).prod ⊤ := by
  rw [secondPointFactor,←comap_subtype,
    comap_map_eq_self_of_injective P.pointNormalizer.subtype_injective]
  exact map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr
    (P.pointBlockAction_surjective structural escape)]; exact le_top)

/-- The two actual preimages generate the full point normalizer. -/
theorem pointNormalizer_eq_factor_sup
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    P.pointNormalizer = P.firstPointFactor ⊔ P.secondPointFactor := by
  have hprod : (⊤ : Subgroup (Equiv.Perm (Fin 4))).prod ⊥ ⊔
      (⊥ : Subgroup (Equiv.Perm (Fin 4))).prod (⊤ : Subgroup (Equiv.Perm (Fin 3))) = ⊤ := by
    apply top_unique
    rintro ⟨a,b⟩ _
    have h := mul_mem_sup (show (a,1) ∈ (⊤ : Subgroup (Equiv.Perm (Fin 4))).prod
      (⊥ : Subgroup (Equiv.Perm (Fin 3))) from ⟨mem_top _,mem_bot.mpr rfl⟩)
      (show (1,b) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 4))).prod ⊤ from ⟨mem_bot.mpr rfl,mem_top _⟩)
    simpa only [Prod.mk_mul_mk,mul_one,one_mul] using h
  rw [firstPointFactor,secondPointFactor,←Subgroup.map_sup,
    comap_sup_eq _ _ _ (P.pointBlockAction_surjective structural escape),
    hprod,comap_top,←MonoidHom.range_eq_map,range_subtype]

private theorem pointFactor_normalized
    (A : Subgroup (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3))) [A.Normal] :
    P.pointNormalizer ≤ normalizer ((A.comap P.pointBlockAction).map
      P.pointNormalizer.subtype : Set G) := by
  have h := (A.comap P.pointBlockAction).le_normalizer_map P.pointNormalizer.subtype
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using h

/-- Relative normality of the original four-letter preimage. -/
theorem firstPointFactor_normalized :
    P.pointNormalizer ≤ normalizer (P.firstPointFactor : Set G) :=
  P.pointFactor_normalized ((⊤ : Subgroup (Equiv.Perm (Fin 4))).prod ⊥)

/-- Relative normality of the original three-letter preimage. -/
theorem secondPointFactor_normalized :
    P.pointNormalizer ≤ normalizer (P.secondPointFactor : Set G) :=
  P.pointFactor_normalized ((⊥ : Subgroup (Equiv.Perm (Fin 4))).prod ⊤)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
