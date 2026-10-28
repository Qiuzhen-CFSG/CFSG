module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.Normalization
public import Stellmacher.ElementaryAbelianMaxFusion

/-!
# Fusion of the chosen fixed subgroup into the Thompson center

Let E = C_W(J₁(T)) for the original prepared full or proper chosen module W,
and let Ω = Ω₁Z(J₁(T)). Every conjugate of E contained in Ω equals E.
Indeed J(T) centralizes both subgroups, and weak closure controls their set
fusion by N_G(J(T)). Source 15.1.9 places this normalizer in M, which
normalizes W. The conjugate therefore lies in W and centralizes J₁(T),
so cardinality gives equality. In particular N_G(Ω) normalizes the same E.

The original residual conclusion is consequently equivalent to containment
of the whole C_G(Ω₁Z(T))-conjugate span of E in Ω. The last theorem applies
this criterion to all four clauses of original 15.1.14, preserving the
literal chosen subgroup and singleton-centralizer overgroup. This span
containment remains an explicit mathematical obligation: no unconditional
15.1.14 or counterexample resolver is asserted here.

Source: Aschbacher--Smith, 15.1.9 and 15.1.13--14, printed pp.1089--1091.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Fusion into the original Thompson omega-center preserves the chosen fixed subgroup. -/
theorem PreparedChosenModule.thompsonFixed_conjugate_eq_of_le_omega
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M W) (g : G)
    (hg : (thompsonFixed T W).map (MulAut.conj g).toMonoidHom ≤
      omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1)) :
    (thompsonFixed T W).map (MulAut.conj g).toMonoidHom = thompsonFixed T W := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let E := thompsonFixed T W
  let Ω := omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1)
  have hr : 1 < ChapterB.twoRank (T : Subgroup G) := by
    let := h.elementary
    exact chosen_twoRank_gt_one_of_quadraticRatio_two T hM.1.2 h.le_selected
      h.normalized h.quadratic_ratio
  have hJJ : J ≤ ChapterB.thompsonJ (T : Subgroup G) 1 := by
    change elementaryAbelianMaxJ (T : Subgroup G) ≤ ChapterB.thompsonJ (T : Subgroup G) 1
    rw [← ChapterB.thompsonJ_zero]
    exact ChapterB.lemma_B_2_3_1 _ (by omega : 0 ≤ 1) hr
  have hJΩ : J ≤ centralizer (Ω : Set G) := by
    intro j hj e he
    exact (((mem_omegaOneCenterAmbient_iff _ e).mp he).2.2 j (hJJ hj)).symm
  have hJE : J ≤ normalizer (E : Set G) :=
    (hJ.trans (centralizer_le (inf_le_left.trans h.le_local))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hJEg : J ≤ normalizer (E.map (MulAut.conj g).toMonoidHom : Set G) :=
    (hJΩ.trans (centralizer_le hg)).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨n,hn,he⟩ := T.weakly_closed_normalizer_controls_set_fusion J
    (sSup_le fun _ hA => hA.1) (maxJ_weakly_closed_normalizer T)
    (E : Set G) (E.map (MulAut.conj g).toMonoidHom : Set G) hJE hJEg g rfl
  have hmap : E.map (MulAut.conj n).toMonoidHom = E.map (MulAut.conj g).toMonoidHom :=
    SetLike.coe_injective he
  have hnM : n ∈ M := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1 hn
  have hWmap : W.map (MulAut.conj n).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (h.normalized hnM)
  have hEgW : E.map (MulAut.conj g).toMonoidHom ≤ W := by
    rw [←hmap,←hWmap]
    exact map_mono inf_le_left
  have hEgE : E.map (MulAut.conj g).toMonoidHom ≤ E := by
    apply le_inf hEgW
    intro e he j hj
    exact ((mem_omegaOneCenterAmbient_iff _ e).mp (hg he)).2.2 j hj
  exact eq_of_le_of_card_ge hEgE (by rw [card_map_of_injective (MulAut.conj g).injective])

/-- The larger Thompson omega-center normalizer preserves the same chosen fixed subgroup. -/
theorem PreparedChosenModule.thompsonCenter_normalizer_le_fixed_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M W) :
    normalizer (omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) : Set G) ≤
      normalizer (thompsonFixed T W : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply h.thompsonFixed_conjugate_eq_of_le_omega hG T hM hJ g
  exact (map_mono (h.thompsonFixed_le_omega T hM)).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp hg)

/-- Original15.1.14 is equivalent to containment of the chosen fixed subgroup's
whole centralizer-conjugate span in the original Thompson omega-center. -/
theorem PreparedChosenModule.thompsonFixed_residual_iff_span_le_omega
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M W) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T W : Set G) ↔
    conjugateSpanBy (thompsonFixed T W) (centralizer (centralInvolutions T : Set G)) ≤
      omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) := by
  rw [h.thompsonFixed_residual_iff_normalizes hG T hM hJ]
  constructor
  · intro hn
    exact (conjugateSpanBy_le le_rfl hn).trans (h.thompsonFixed_le_omega T hM)
  · intro hspan g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply h.thompsonFixed_conjugate_eq_of_le_omega hG T hM hJ g
    apply le_trans ?_ hspan
    exact (map_mono (le_conjugateSpanBy _ _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy _ _) hg))

/-- A failure of the original residual conclusion supplies a conjugate leaving
the entire original Thompson omega-center, for the literal full or proper W. -/
theorem PreparedChosenModule.thompsonFixed_failure_conjugate_outside_omega
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M W)
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T W : Set G)) :
    ∃ g ∈ centralizer (centralInvolutions T : Set G),
      ¬ (thompsonFixed T W).map (MulAut.conj g).toMonoidHom ≤
        omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) := by
  have hn := mt (h.thompsonFixed_residual_iff_normalizes hG T hM hJ).mpr hnot
  obtain ⟨g,hg,hgn⟩ := SetLike.not_le_iff_exists.mp hn
  refine ⟨g,hg,fun hle => hgn ?_⟩
  exact mem_normalizer_iff_map_conj_eq.mpr
    (h.thompsonFixed_conjugate_eq_of_le_omega hG T hM hJ g hle)

/-- Apply the same-subgroup fusion criterion to all original 15.1.14 clauses.
The span hypothesis is still required for both full and proper source choices. -/
theorem PreparedChosenModule.thompsonFixed_source_clauses_of_span_le_omega
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M W)
    (hspan : conjugateSpanBy (thompsonFixed T W)
        (centralizer (centralInvolutions T : Set G)) ≤
      omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
      centralizer (thompsonFixed T W : Set G) ∧
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
        normalizer (thompsonFixed T W : Set G) ∧
      normalizer (thompsonFixed T W : Set G) ≤ Mc ∧
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  have hres := (h.thompsonFixed_residual_iff_span_le_omega hG T hM hJ).mpr hspan
  exact ⟨hres,h.thompsonFixed_normalizers hG T hM hJ hu hres⟩

end CFSG.Quasithin.Chapter15.Section01
