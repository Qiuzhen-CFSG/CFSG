module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerModels
public import Theory.SpecificGroups.SymplecticFour.SixSectionNormalizer
public import Theory.AtlasPort.LinearGroups.G2.SixSectionNormalizer

/-!
# The original index-four bound removes the canonical rank-two rows

The literal map K_v -> K_v/O₂(K_v) -> model retains the perfect image of
L_v and its A₆ two-core quotient. Intersecting the selected Sylow of G_v
with K_v, then mapping it, puts a model Sylow within index four of the
normalizer of that same image. The native Sp₄ and G₂ normalizer bounds
contradict this; the argument needs no full-Sylow assumption.

Thus the contrary branch N_G(R_v)≤M has K_v/O₂(K_v) isomorphic to SL₄(2)
or SL₅(2). The final consumer applies this at the actual preferred escaping
point with nontrivial original C_V(L), discharging nonquasisimplicity and
retaining V, the fixed line, R=R_v and the nontrivial quotient image.

The binary-five exclusion and binary-four extension/module comparison still
have to complete12.6.17. The HS/J₄ exclusions, general12.6.13(3), blocks,
splitting and fixed-space elimination also remain; neither12.6.2 nor12.6.23
is asserted. Earlier invariance and TI retain producer qt-d-1222-source;
final source discharge remains with qt-d-12634-source.
Source: Aschbacher--Smith,12.6.4 and12.6.17, printed pp.824 and827,
combined manuscript of1 March2004.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem SourceHypothesis.nonsingular_exclude_small_normalizer_model
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    {F : Type*} [Group F] [Finite F]
    (hF : ∀ (A : Subgroup F) [Group.IsPerfect A],
      ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) →
      ∀ S : Sylow 2 F, (normalizer (A : Set F)).relIndex S ≤ 4 → False)
    (e : Star (Kv (v : G)) ≃* F) : False := by
  let C := Kv (v : G)
  let A₀ := (Lv L (v : G)).subgroupOf C
  let q := QuotientGroup.mk' (pCore 2 C)
  let f := e.toMonoidHom.comp q
  let A := A₀.map f
  have hAC : Lv L (v : G) ≤ C := (H.nonsingular_canonical_component D v hv).2.1
  let a : A₀ ≃* Lv L (v : G) := subgroupOfEquivOfLe hAC
  obtain ⟨eA⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let : Group.IsPerfect (Lv L (v : G)) := Lv_isPerfect_of_A6 L (v : G) eA
  let : Group.IsPerfect A₀ := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect A := Group.IsPerfect.map f
  have hk : f.ker ≤ pCore 2 C := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    exact e.injective (hx.trans e.map_one.symm)
  have hkA : IsPGroup 2 (f.subgroupMap A₀).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact (pCore_isPGroup.to_le hk).comap_subtype
  let b : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6) :=
    ((f.subgroupMap A₀).pCoreQuotientEquiv (f.subgroupMap_surjective A₀) hkA).symm.trans
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eA)
  obtain ⟨S,hS⟩ := H.nonsingular_local_model_sylow_index D v hv hTV hi f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact hF A b S ((relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite).trans hS)

/-- The original index-four geometry excludes every nonbinary Sp₄ and G₂
row of the canonical quotient, without a full-Sylow or normalizer-escape premise. -/
theorem SourceHypothesis.nonsingular_canonical_rankTwo_exclusions
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hn : 1 < F.degree) :
    ¬ Nonempty (Star (Kv (v : G)) ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) ∧
      ¬ Nonempty (Star (Kv (v : G)) ≃* Atlas.G2.Model F.Carrier) := by
  constructor
  · rintro ⟨e⟩
    exact H.nonsingular_exclude_small_normalizer_model D v hv hTV hi
      (fun A _ a S hS => Theory.SpecificGroups.SymplecticFour.no_six_section_of_small_sylow_normalizer_index
        F.card_eq hn A a S hS) e
  · rintro ⟨e⟩
    exact H.nonsingular_exclude_small_normalizer_model D v hv hTV hi
      (fun A _ a S hS => Atlas.G2.no_six_section_of_small_sylow_normalizer_index
        F.card_eq hn A a S hS) e

/-- Only the actual binary dimension-four and dimension-five groups remain
in the contrary normalizer branch of 12.6.17. -/
theorem SourceHypothesis.nonsingular_normalizer_binary_models
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)) ∨
      Nonempty (Star (Kv (v : G)) ≃* SL(5,ZMod 2)) := by
  rcases H.nonsingular_normalizer_models D v hv hTV hnot hs hi he hNM with h | h | ⟨F,hn,h⟩
  · exact .inl h
  · exact .inr h
  · have hh := H.nonsingular_canonical_rankTwo_exclusions D v hv hTV hi F hn
    exact (h.elim hh.1 hh.2).elim
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original preferred-point application discharges nonquasisimplicity
and retains the selected Sylow, R=R_v, and the nontrivial original quotient image. -/
theorem SourceHypothesis.exists_preferred_nonsingular_normalizer_models_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
      ¬ IsQuasisimple (Kv (w : G)) ∧
      (normalizer (Rv T L (w : G) : Set G) ≤ M L →
        ∃ S : Sylow 2 (Gv (w : G)),
          let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
          let J := Kv (w : G) ⊔ S₀
          let R₀ := starImage J (Rv T L (w : G))
          Tv T (w : G) ≤ S₀ ∧
          Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (w : G) : Set G))
            (Gv (w : G) ⊓ normalizer (Lv L (w : G) : Set G)) ∧
          (Tv T (w : G)).relIndex S₀ ≤ 4 ∧
          R L (Kv (w : G)) S₀ (w : G) = Rv T L (w : G) ∧ R₀ ≠ ⊥ ∧
          (Nonempty (Star (Kv (w : G)) ≃* SL(4,ZMod 2)) ∨
           Nonempty (Star (Kv (w : G)) ≃* SL(5,ZMod 2)))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,_⟩ :=
    H.exists_preferred_nonsingular_large_thompson_of_fixed D hTV hTI hz v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,fun hNM => ?_⟩
  obtain ⟨S,hTS,hN⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (w : G)
  refine ⟨S,hTS,hN,?_,H.nonsingular_R_eq_Rv_of_normalizer D w hw hs hNM S hTS,
    (H.nonsingular_normalizer_local_image D w hw hs hnot hNM S hTS).2.1,?_⟩
  · simpa only [hi] using Tv_relIndex_le T (w : G) _ (S.isPGroup'.map _) hTS
  · exact H.nonsingular_normalizer_binary_models D w hw hTV hnq hs hi hnot hNM
end CFSG.Quasithin.Chapter12.Section06
