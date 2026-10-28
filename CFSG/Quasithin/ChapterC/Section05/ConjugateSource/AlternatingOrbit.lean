module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingCommutator
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.FourModuleOrbit

/-!
# The actual alternating blocks in the four-module orbit

Transporting the characteristic commutator layer carries the original
TH-action on the blocks to the literal modules. Their elementarity and
commuting block supports supply the first two commutator facts. The
proved C.5.6(1) centralizer supplies the cross-commutation fact, so the
four-module theorem eliminates the cyclic and dihedral alternatives
without assuming a permutation table or either of those conclusions.

Source: Aschbacher–Smith, C.5.6(7), printed p.158.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G]
private theorem sourceModule_eq (K : Subgroup G) : sourceModule K = ⁅K.pCoreIn 2, K⁆ := by
  unfold sourceModule blockU
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rfl

theorem sourceModule_map_equiv (K : Subgroup G) (e : G ≃* G) :
    (sourceModule K).map e.toMonoidHom = sourceModule (K.map e.toMonoidHom) := by
  rw [sourceModule_eq, sourceModule_eq, map_commutator,
    map_pCoreIn_of_injective 2 K e.toMonoidHom e.injective]

variable [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.fourModuleSourceInputs
    (h : AlternatingPairSetup R K L) (hLS : sourceModule L ≤ ChapterB.baumann R)
    (M₀ T_H : Subgroup G) (x : G) (hx : x ∈ M₀)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M₀ = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M₀, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    FourModuleOrbit.SourceInputs M₀ T_H (sourceModule K) (sourceModule L) x := by
  have hm (g : G) : (sourceModule K).conjBy g = sourceModule (K.conjBy g) :=
    sourceModule_map_equiv K (MulAut.conj g)
  refine ⟨hindex, hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases hpair g hg with he | he
    · exact Or.inl ((hm g).trans (congrArg sourceModule he))
    · exact Or.inr ((hm g).trans (congrArg sourceModule he))
  · obtain ⟨t, ht, he⟩ := ht
    exact ⟨t, ht, (hm t).trans (congrArg sourceModule he)⟩
  · let : IsElementaryAbelian 2 (sourceModule K) := by
      let := h.block.2.1.elementary
      exact IsElementaryAbelian.map K.subtype
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer _)
  · intro he
    apply hnc
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    exact (map_subtype_le _).trans (h.commute.trans (centralizer_le (map_subtype_le _)))
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact le_centralizer_iff.mp ((le_inf hLS ((map_subtype_le _).trans h.commute)).trans
      (h.centralizer_centralizes_conjugate x hxR hnc))
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- The original two A₅ blocks yield the regular Klein-four action and
commuting conjugate-generated factors in C.5.6(7). -/
theorem AlternatingPairSetup.four_module_geometry
    (h : AlternatingPairSetup R K L) (hLS : sourceModule L ≤ ChapterB.baumann R)
    (M₀ T_H : Subgroup G) (x : G) (hx : x ∈ M₀)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M₀ = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M₀, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let d := h.fourModuleSourceInputs hLS M₀ T_H x hx hxR hindex hpair ht hnc
    IsKleinFour (FourModuleOrbit.action d.toInputs).range ∧
      IsKleinFour (M₀ ⧸ (FourModuleOrbit.action d.toInputs).ker) ∧
      (∀ i : Fin 4,
        (FourModuleOrbit.modules (sourceModule K) (sourceModule L) x i).conjBy (x ^ 2) =
          FourModuleOrbit.modules (sourceModule K) (sourceModule L) x i) ∧
      ⁅sourceModule K ⊔ (sourceModule K).conjBy x⁻¹,
        sourceModule L ⊔ (sourceModule L).conjBy x⁻¹⁆ = ⊥ := by
  have he := (h.fourModuleSourceInputs hLS M₀ T_H x hx hxR hindex hpair ht hnc).conclusion
  exact ⟨he.1, he.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
