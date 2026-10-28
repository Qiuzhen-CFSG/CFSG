module
public import CFSG.Quasithin.ChapterC.Section06.Original.Definitions
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Theory.GroupTheory.WreathTwoSylowMaximal
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Unique Sylow overgroups from the original C.6 quotient models

The binary PSL₂ Borel is the unique maximal Sylow overgroup. This lifts
through O₂ and extends across the normal two-residual supplement. In the
S₃ and S₃ wreath C₂ rows the quotient Sylow itself is maximal. All three
routes retain the actual quotient map and the supplied Sylow subgroup.
Source: Aschbacher--Smith C.6.1(i), printed pp.164--165.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section06.Original
variable {A : Type*} [Group A] [Finite A]

theorem linear_sylow_unique {n : ℕ} (h : ClassicalGroup.IsPSL A 2 (2^n))
    (S : Sylow 2 A) : Order.HasUniqueMaximalOver (S : Subgroup A) ⊤ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [←Nat.card_eq_fintype_card] using hF)
  let f := e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  apply hasUniqueMaximalOver_of_surjective f.toMonoidHom f.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff f.toMonoidHom).mpr f.injective]; exact bot_le)
  exact Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2 (S.mapSurjective f.surjective)

theorem residual_linear_sylow_unique {n : ℕ}
    (h : ClassicalGroup.IsPSL (pResidual 2 A) 2 (2^n))
    (S : Sylow 2 A) : Order.HasUniqueMaximalOver (S : Subgroup A) ⊤ := by
  obtain ⟨U,hU⟩ := S.exists_subgroupOf_eq_of_normal (pResidual 2 A)
  have hu := hasUniqueMaximalOver_map_subtype (linear_sylow_unique h U)
  rw [hU,subgroupOf_map_subtype,inf_comm] at hu
  have hh := hasUniqueMaximalOver_sup_of_normalizes
    (show (S : Subgroup A) ≤ normalizer (pResidual 2 A : Set A) from le_normalizer_of_normal) hu
  rwa [pResidual_sup_sylow_eq_top S] at hh

theorem linear_core_sylow_unique {n : ℕ}
    (h : ClassicalGroup.IsPSL (pResidual 2 (A ⧸ pCore 2 A)) 2 (2^n))
    (S : Sylow 2 A) : Order.HasUniqueMaximalOver (S : Subgroup A) ⊤ := by
  apply hasUniqueMaximalOver_of_surjective (QuotientGroup.mk' (pCore 2 A))
    (QuotientGroup.mk'_surjective _) ?_
    (residual_linear_sylow_unique h (S.mapSurjective (QuotientGroup.mk'_surjective _)))
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.le_sylow_of_normal S

theorem cubic_core_sylow_unique (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (S : Sylow 2 A) : Order.HasUniqueMaximalOver (S : Subgroup A) ⊤ := by
  have hc := isCoatom_of_index_three (S : Subgroup A) (SymmetricThreeTwoCore.sylow_index_three e S)
  refine ⟨hc.lt_top,(S : Subgroup A),⟨le_rfl,hc.covBy_top⟩,?_⟩
  intro N hN
  exact (hc.covBy_top.eq_or_eq hN.1 le_top).resolve_right hN.2.ne

theorem wreath_sylow_unique (S : Sylow 2 CubicWreath) :
    Order.HasUniqueMaximalOver (S : Subgroup CubicWreath) ⊤ := by
  let e := RegularWreathProduct.congr (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  have hc := wreath_two_sylow_isCoatom (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hu : Order.HasUniqueMaximalOver ((S : Subgroup CubicWreath).map e.toMonoidHom) ⊤ := by
    refine ⟨hc.lt_top,_,⟨le_rfl,hc.covBy_top⟩,?_⟩
    intro N hN
    exact (hc.covBy_top.eq_or_eq hN.1 le_top).resolve_right hN.2.ne
  exact hasUniqueMaximalOver_of_surjective e.toMonoidHom e.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]; exact bot_le) hu

theorem QuotientModels.sylow_unique (h : QuotientModels A) (S : Sylow 2 A) :
    Order.HasUniqueMaximalOver (S : Subgroup A) ⊤ := by
  change (∃ n, ClassicalGroup.IsPSL (pResidual 2 (A ⧸ pCore 2 A)) 2 (2^n)) ∨
    Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) ∨
    Nonempty ((A ⧸ pCore 2 A) ≃* CubicWreath) at h
  rcases h with hn | he | he
  · obtain ⟨n,hn⟩ := hn
    exact linear_core_sylow_unique hn S
  · exact cubic_core_sylow_unique (Classical.choice he) S
  · let e := Classical.choice he
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
    apply hasUniqueMaximalOver_of_surjective f hf ?_ (wreath_sylow_unique (S.mapSurjective hf))
    have hk : f.ker = pCore 2 A := by
      ext a
      change e (QuotientGroup.mk' (pCore 2 A) a) = 1 ↔ a ∈ pCore 2 A
      rw [map_eq_one_iff e e.injective]
      exact QuotientGroup.eq_one_iff a
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal S
end CFSG.Quasithin.ChapterC.Section06.Original
