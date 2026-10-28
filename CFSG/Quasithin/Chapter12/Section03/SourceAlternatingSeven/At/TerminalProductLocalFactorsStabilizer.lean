module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsStabilizer
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsOmega

/-!
# TerminalProductLocalFactorsStabilizer at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductLocalFactorsStabilizer`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
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

theorem pointBlockAction_surjective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : Function.Surjective P.pointBlockAction :=
  (WeightFourLocal.pointEquiv _ P.weight_four).surjective.comp
    (D.model.pointPermutation_surjective
      (MonoidHom.range_eq_top.mp (D.permutation_range_eq_top_at structural escape)) P.point)

theorem pointNormalizer_le_original_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    P.pointNormalizer ≤ normalizer (L : Set G) :=
  inf_le_left.trans (S.normalizer_le_component_at structural)

def pointNormalizerQuotientEquiv_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    (P.pointNormalizer ⧸ (centralizer (V : Set G)).subgroupOf P.pointNormalizer) ≃*
      (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3)) :=
  D.model.weightFourPointQuotientEquiv
    (MonoidHom.range_eq_top.mp (D.permutation_range_eq_top_at structural escape))
    P.point P.weight_four

theorem pointNormalizerQuotientEquiv_apply_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (n : P.pointNormalizer) :
    P.pointNormalizerQuotientEquiv_at structural escape (QuotientGroup.mk'
      ((centralizer (V : Set G)).subgroupOf P.pointNormalizer) n) =
        P.pointBlockAction n := rfl

theorem firstPointFactor_image_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    (P.firstPointFactor.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (⊤ : Subgroup (Equiv.Perm (Fin 4))).prod ⊥ := by
  rw [firstPointFactor,←comap_subtype,
    comap_map_eq_self_of_injective P.pointNormalizer.subtype_injective]
  exact map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr
    (P.pointBlockAction_surjective_at structural escape)]; exact le_top)

theorem secondPointFactor_image_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    (P.secondPointFactor.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (⊥ : Subgroup (Equiv.Perm (Fin 4))).prod ⊤ := by
  rw [secondPointFactor,←comap_subtype,
    comap_map_eq_self_of_injective P.pointNormalizer.subtype_injective]
  exact map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr
    (P.pointBlockAction_surjective_at structural escape)]; exact le_top)

theorem pointNormalizer_eq_factor_sup_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
    comap_sup_eq _ _ _ (P.pointBlockAction_surjective_at structural escape),
    hprod,comap_top,←MonoidHom.range_eq_map,range_subtype]

private theorem pointFactor_normalized_at
    (A : Subgroup (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3))) [A.Normal] :
    P.pointNormalizer ≤ normalizer ((A.comap P.pointBlockAction).map
      P.pointNormalizer.subtype : Set G) := by
  have h := (A.comap P.pointBlockAction).le_normalizer_map P.pointNormalizer.subtype
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using h

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

