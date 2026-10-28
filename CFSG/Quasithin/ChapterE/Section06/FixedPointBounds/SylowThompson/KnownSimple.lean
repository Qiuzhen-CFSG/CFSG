module
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.GenerationSource
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization
/-!
# Numeric E.6.26 on the original known-simple SQTK groups

Global SQTK attainment converts n(H)≤j into actual E-generation in even
order. Odd-order solvability gives rank-one generation in the other case.
The proved E.6.26 source therefore supplies the numeric containment with
no attainment callback. The original residual parabolic inherits SQTK;
its unchanged subgroup embedding and prescribed Sylow give the complete
small-parabolic preparation used in E.6.27.

This proves the actual known-simple source application and preserves the
broader legacy unrestricted finite-group E626Input interface separately.
Source: Aschbacher–Smith E.1.11–13 and E.6.26–27, pp.213–214,256–257.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

theorem source_isEGenerated_of_parameter_le_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (S : Sylow 2 G)
    {j : ℕ} (hj : 0 < j) (hn : generationParameter G ≤ j) : IsEGenerated j G := by
  by_cases ho : Odd (Nat.card G)
  · let : Group.IsSolvable G := odd_order_theorem G ho
    exact isEGenerated_one_of_solvable.mono hj
  · exact (source_generation_spec_knownSimple hG S ho).2.mono hn

namespace Section06.FixedPointBounds.SylowThompson
open ChapterB
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_E_6_26_knownSimple {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) {j : ℕ} (hjpos : 0 < j)
    (H : Subgroup G) (S : Sylow 2 H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hn : generationParameter H ≤ j)
    (hQA : sylowCentralizer (T : Subgroup G) V ≤ (S : Subgroup H).map H.subtype)
    (hAT : (S : Subgroup H).map H.subtype ≤ T)
    (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ ((S : Subgroup H).map H.subtype) j ≤ centralizer (V : Set G)) :
    H ≤ M ∧ normalizer ((S : Subgroup H).map H.subtype : Set G) ≤ M :=
  source_E_6_26_of_isEGenerated h hjpos H S
    (source_isEGenerated_of_parameter_le_knownSimple hH S hjpos hn) hQA hAT hj hJ

theorem small_parabolic_of_placement_knownSimple
    {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hU : U ≠ ⊥) (hUV : U ≤ V)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (P : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (g : G) (hg : g ∈ localNormalizer M V)
    (hQA : sylowCentralizer (T : Subgroup G) V ≤
      ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype).map (MulAut.conj g).toMonoidHom)
    (hAT : ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype).map (MulAut.conj g).toMonoidHom ≤ T)
    (hJA : thompsonJ (((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype).map (MulAut.conj g).toMonoidHom) j ≤
        centralizer (V : Set G))
    (S : Sylow 2 (centralizer (U : Set G)))
    (hS : (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
      (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H)
    (hn : generationParameter H ≤ j) :
    (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M := by
  let C := centralizer (U : Set G)
  let f : primeToResidual 2 C →* G := C.subtype.comp (primeToResidual 2 C).subtype
  let e : G ≃* G := MulAut.conj g
  let k := e.toMonoidHom.comp f
  have hk : Function.Injective k := e.injective.comp
    (C.subtype_injective.comp (primeToResidual 2 C).subtype_injective)
  obtain ⟨R, hR⟩ := exists_sylow_map k hk (residualSylow S) H hH.1.1.le
  have hRmap : (R : Subgroup (H.map k)).map (H.map k).subtype =
      ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype).map e.toMonoidHom := by
    rw [hR]
    change (residualSylow S : Subgroup (primeToResidual 2 C)).map
      (e.toMonoidHom.comp (C.subtype.comp (primeToResidual 2 C).subtype)) = _
    rw [← map_map, ← map_map, residualSylow_map, hS]
  have hgenH := source_isEGenerated_of_parameter_le_knownSimple
    (ParabolicCartan.residual_sqtk h hU hUV H) (ParabolicCartan.parabolicSylow S H hH)
    (Nat.zero_lt_one.trans_le hj1) hn
  have hD : H.map k ≤ M := (source_E_6_26_of_isEGenerated h
    (Nat.zero_lt_one.trans_le hj1) (H.map k) R (hgenH.map_equiv (H.equivMapOfInjective k hk))
    (hRmap.symm ▸ hQA) (hRmap.symm ▸ hAT) hj (hRmap.symm ▸ hJA)).1
  have hMM : M.map e.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hg.1)
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [hMM]
  simpa only [map_map] using hD


/-- The complete original small-parabolic preparation, with no E.6.26 callback. -/
theorem exists_preparation_knownSimple
    {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hU : U ≠ ⊥) (hUV : U ≤ V) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤
      M ⊓ centralizer (V : Set G)) :
    ∃ P : Sylow 2 ↥(M ⊓ centralizer (U : Set G)),
      normalizer ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype : Set G) ≤ M ∧
      ∀ S : Sylow 2 (centralizer (U : Set G)),
        (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
          (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
            (M ⊓ centralizer (U : Set G)).subtype →
        ∀ H : Subgroup (primeToResidual 2 (centralizer (U : Set G))),
          IsMinimalParabolicOver (residualSylow S) H → generationParameter H ≤ j →
          (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
            (centralizer (U : Set G)).subtype ≤ M := by
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥(M ⊓ centralizer (U : Set G)))
  obtain ⟨g, hg, _, hQA, hAT, hJA, hN⟩ := placement h hU hUV hj hJ P
  exact ⟨P, hN, small_parabolic_of_placement_knownSimple h hU hUV hj1 hj P g hg hQA hAT hJA⟩

end Section06.FixedPointBounds.SylowThompson
end CFSG.Quasithin.ChapterE
