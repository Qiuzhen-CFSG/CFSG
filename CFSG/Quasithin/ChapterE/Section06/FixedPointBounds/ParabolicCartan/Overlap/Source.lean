module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Overlap
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.GenerationSource
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
/-!
# Original maximal-overlap placement with E.6.26 discharged

The solvable unique maximal overgroup has genuine rank-one E-generation.
The new source E.6.26 theorem applies to its literal embedded image, giving
containment in M without an earlier containment or attainment premise.
The original Sylow conjugation and escape then identify this maximal
subgroup with the actual overlap. This is the precise Hall–Cartan consumer
of the source containment theorem.
Source: Aschbacher–Smith E.1.13, E.6.26–27, pp.214,256–257.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Overlap
open Subgroup ChapterB SylowThompson
universe u
variable {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]

theorem source_image_le_of_isEGenerated
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 Kc T M V) {j : ℕ} (hj1 : 0 < j)
    (hj : (j : ℕ∞) < globalR V)
    (f : X →* G) (hf : Function.Injective f) (S : Sylow 2 X)
    (A : Subgroup X) (hSA : (S : Subgroup X) ≤ A) (hgen : IsEGenerated j A)
    (hQS : sylowCentralizer (T : Subgroup G) V ≤ (S : Subgroup X).map f)
    (hST : (S : Subgroup X).map f ≤ T)
    (hJ : thompsonJ ((S : Subgroup X).map f) j ≤ centralizer (V : Set G)) :
    A.map f ≤ M := by
  obtain ⟨R,hR⟩ := exists_sylow_map f hf S A hSA
  exact (source_E_6_26_of_isEGenerated h hj1 (A.map f) R
    (hgen.map_equiv (A.equivMapOfInjective f hf))
    (hR.symm ▸ hQS) (hR.symm ▸ hST) hj (hR.symm ▸ hJ)).1

theorem source_maximal_image_le_of_placement
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 Kc T M V)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (f : X →* G) (hf : Function.Injective f) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤)
    (hsolv : Group.IsSolvable (minimalParabolicMax S hP))
    (hQS : sylowCentralizer (T : Subgroup G) V ≤ (S : Subgroup X).map f)
    (hST : (S : Subgroup X).map f ≤ T)
    (hJ : thompsonJ ((S : Subgroup X).map f) j ≤ centralizer (V : Set G)) :
    (minimalParabolicMax S hP).map f ≤ M := by
  let := hsolv
  exact source_image_le_of_isEGenerated h (Nat.zero_lt_one.trans_le hj1) hj f hf S _
    (minimalParabolicMax_spec S hP).2 (isEGenerated_one_of_solvable.mono hj1) hQS hST hJ

theorem source_residual_maximal_image_le
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V)
    (hU : U ≠ ⊥) (hUV : U ≤ V)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤ M ⊓ centralizer (V : Set G))
    (P : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (S : Sylow 2 (centralizer (U : Set G)))
    (hS : (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
      (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H)
    (hsolv : Group.IsSolvable (minimalParabolicMax (parabolicSylow S H hH)
      (minimalParabolic_subtype (residualSylow S) H hH))) :
    (minimalParabolicMax (parabolicSylow S H hH)
      (minimalParabolic_subtype (residualSylow S) H hH)).map
        (residualEmbedding U H) ≤ M := by
  obtain ⟨g, hg, _, hQS, hST, hJS, _⟩ := placement h hU hUV hj hJ P
  let e : G ≃* G := MulAut.conj g
  let f := residualEmbedding U H
  let k := e.toMonoidHom.comp f
  have hk : Function.Injective k := e.injective.comp (residualEmbedding_injective U H)
  have hR : (parabolicSylow S H hH : Subgroup H).map k =
      ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype).map e.toMonoidHom := by
    rw [← map_map, parabolicSylow_image, hS]
  have hA := source_maximal_image_le_of_placement h hj1 hj k hk
    (parabolicSylow S H hH) (minimalParabolic_subtype (residualSylow S) H hH)
    hsolv (hR.symm ▸ hQS) (hR.symm ▸ hST) (hR.symm ▸ hJS)
  have hMM : M.map e.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hg.1)
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [hMM]
  simpa only [map_map] using hA

/-- The intrinsic unique maximal subgroup equals the literal preimage of M.
This supplies the overlap equality for the marked Hall--Cartan transport;
escape is used only for the reverse containment supplied by uniqueness. -/
theorem source_residual_maximal_eq_overlap
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V)
    (hU : U ≠ ⊥) (hUV : U ≤ V)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤ M ⊓ centralizer (V : Set G))
    (P : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (S : Sylow 2 (centralizer (U : Set G)))
    (hS : (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
      (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H)
    (hsolv : Group.IsSolvable (minimalParabolicMax (parabolicSylow S H hH)
      (minimalParabolic_subtype (residualSylow S) H hH)))
    (hescape : ¬ (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M) :
    minimalParabolicMax (parabolicSylow S H hH)
      (minimalParabolic_subtype (residualSylow S) H hH) =
        M.comap (residualEmbedding U H) := by
  apply maximal_eq_overlap_of_image_le
    (residualEmbedding U H) (parabolicSylow S H hH)
    (minimalParabolic_subtype (residualSylow S) H hH)
  · rw [parabolicSylow_image, hS]
    exact (map_subtype_le _).trans inf_le_left
  · rwa [residualEmbedding_range]
  · exact source_residual_maximal_image_le h hU hUV hj1 hj hJ P S hS H hH hsolv

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Overlap

end
