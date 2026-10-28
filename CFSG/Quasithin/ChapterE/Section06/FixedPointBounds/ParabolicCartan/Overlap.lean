module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson


/-!
# Placing the unique maximal subgroup in the actual overlap

Let A be the unique maximal overgroup of the parabolic Sylow subgroup.
When A is solvable, E.1.13 gives n(A) ≤ 1. Apply E.6.26 to its actual
ambient image: it has the same Sylow image as the parabolic, so the source
rank, higher-Thompson and Q ≤ S ≤ T hypotheses apply. This proves A ≤ M.
The escaping parabolic and uniqueness then give A = H ∩ M.

For the original E.6.27 coordinates, `SylowThompson.placement` constructs an
M_V-conjugation satisfying those hypotheses. We apply the argument to the
composite of that conjugation with `residualEmbedding` and transport back.
Thus no extra placement, Sylow conjugacy, or overlap premise remains.

The explicit earlier inputs are genuine E.1.13 (`SourceE113`, produced by
qt-e01-parameter-reduction) and E.6.26 (`SylowThompson.E626Input`, assembled
by qt-e-06 from E.5.2). Solvability of the unique maximal subgroup is the
`IntrinsicHallCartanData.maximal_solvable` output of qt-e627-marked-hall-models.
The large-parameter hypothesis is used by that model producer, not by this
placement argument. `residual_maximal_image_le` supplies exactly `hmax` in
`residual_alternative_of_constructed_hall`; `residual_maximal_eq_overlap`
supplies the equality required to transport the intrinsic Hall data. The
parent qt-e627-parabolic-cartan retains their assembly, with the original
rank and higher-Thompson hypotheses supplied by qt-e06-fixed-point-bound.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.1.13,
printed p.214; E.2.2, pp.215--216; E.6.26--27, pp.256--257; B.6.1--8,
pp.112--114. The outside-family minimality used in Chapter 15 is not used.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Overlap
open Subgroup ChapterB SylowThompson
universe u
variable {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]

/-- The exact solvable-group conclusion of E.1.13. This is an explicit earlier
source input; it asserts neither an overlap nor a containment in M. -/
@[expose] def SourceE113 : Prop :=
  ∀ (Y : Type u) (_ : Group Y) (_ : Finite Y),
    Group.IsSolvable Y → generationParameter Y ≤ 1

/-- E.6.26 applied to the literal image of an overgroup of a Sylow subgroup.
The parameter is transported along the actual injective map. -/
theorem image_le_of_parameter_le
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 Kc T M V) (h626 : E626Input G)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (f : X →* G) (hf : Function.Injective f) (S : Sylow 2 X)
    (A : Subgroup X) (hSA : (S : Subgroup X) ≤ A)
    (hn : generationParameter A ≤ j)
    (hQS : sylowCentralizer (T : Subgroup G) V ≤ (S : Subgroup X).map f)
    (hST : (S : Subgroup X).map f ≤ T)
    (hJ : thompsonJ ((S : Subgroup X).map f) j ≤ centralizer (V : Set G)) :
    A.map f ≤ M := by
  obtain ⟨R, hR⟩ := exists_sylow_map f hf S A hSA
  have hnA : generationParameter (A.map f) ≤ j := by
    rw [← generationParameter_equiv (A.equivMapOfInjective f hf)]
    exact hn
  exact (h626 T V M h.nontrivial h.elementary h.le_sylow
    h.normal_in_sylow h.normalizer_le h.maximalTwoLocal h.normalizer_sylowCentralizer_le
    (fun N hN hQN => h.unique N hN (inf_le_right.trans hQN)) j (A.map f) R hj1 hnA
    (hR.symm ▸ hQS) (hR.symm ▸ hST) hj
    (hR.symm ▸ le_inf (thompsonJ_le _ j) hJ)).1

/-- A solvable unique maximal overgroup lies in M under the full local
hypotheses of E.6.26. Solvability enters only through E.1.13. -/
theorem maximal_image_le_of_placement
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 Kc T M V) (h626 : E626Input G) (h113 : SourceE113.{u})
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (f : X →* G) (hf : Function.Injective f) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤)
    (hsolv : Group.IsSolvable (minimalParabolicMax S hP))
    (hQS : sylowCentralizer (T : Subgroup G) V ≤ (S : Subgroup X).map f)
    (hST : (S : Subgroup X).map f ≤ T)
    (hJ : thompsonJ ((S : Subgroup X).map f) j ≤ centralizer (V : Set G)) :
    (minimalParabolicMax S hP).map f ≤ M := by
  exact image_le_of_parameter_le h h626 hj1 hj f hf S _
    (minimalParabolicMax_spec S hP).2
    ((h113 _ inferInstance inferInstance hsolv).trans hj1) hQS hST hJ

/-- The exact `hmax` argument of `residual_alternative_of_constructed_hall`,
in the original coordinates. P and the literal image equality are the data
already carried by `centralizer_le_of_parabolic_branches`; the source
higher-Thompson hypothesis constructs all the needed conjugated placements. -/
theorem residual_maximal_image_le
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (h626 : E626Input G) (h113 : SourceE113.{u})
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
  have hA := maximal_image_le_of_placement h h626 h113 hj1 hj k hk
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
theorem residual_maximal_eq_overlap
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (h626 : E626Input G) (h113 : SourceE113.{u})
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
  · exact residual_maximal_image_le h h626 h113 hU hUV hj1 hj hJ P S hS H hH hsolv

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Overlap

end
