module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.RankObstruction
public import Theory.GroupTheory.ConjugateLayerExchange

/-!
# The conjugate hyperplane exchange and its actual unitary source consumer

The internal conjugator gives `V₅∨V₃ᵍ=V₅ᵍ∨V₃`. Since the un-conjugated
spaces centralize V, their images disappear in the literal automizer, leaving
the same action image for the conjugate hyperplane and the conjugate seed.
The seed has order eight and contains the original central line of order two,
so its image has rank at most two. The preceding rank obstruction makes the
pair a two-group, contrary to its Baer–Suzuki construction.

Only the earlier hyperplane identification and cross-displacement bounds
remain explicit; neither action-image rank nor a two-group conclusion is
assumed. The source point-parabolic calculations must produce those bounds.

Source: Aschbacher–Smith, Lemma 13.3.18, printed p.895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem induced_sup {V A B : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hB : B ≤ normalizer (V : Set G)) :
    inducedAutomizer V (A ⊔ B) = inducedAutomizer V A ⊔ inducedAutomizer V B := by
  unfold inducedAutomizer
  rw [subgroupOf_sup hA hB,Subgroup.map_sup]

omit [Finite G] in
/-- The source exchange equality identifies the images of the actual
conjugate hyperplane and conjugate seed in the automizer of V. -/
theorem conjugate_hyperplane_image_eq_seed
    {V A B I : Subgroup G} [IsElementaryAbelian 2 V]
    (g : G) (hBA : B ≤ A) (hAV : A ≤ V) (hg : g ∈ I)
    (hAN : A.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hc : ⁅I, A ⊔ A.map (MulAut.conj g).toMonoidHom⁆ ≤
      B ⊔ B.map (MulAut.conj g).toMonoidHom) :
    inducedAutomizer V (A.map (MulAut.conj g).toMonoidHom) =
      inducedAutomizer V (B.map (MulAut.conj g).toMonoidHom) := by
  have he := congrArg (inducedAutomizer V) (conjugate_layer_sup_exchange A B I g hBA hg hc)
  have hAVN := hAV.trans V.le_normalizer
  have hBVN := hBA.trans hAVN
  have hBgN := (map_mono hBA).trans hAN
  have hAVC : A ≤ centralizer (V : Set G) := hAV.trans (le_centralizer V)
  have hA0 := (inducedAutomizer_eq_bot_iff hAVN).mpr hAVC
  have hB0 := (inducedAutomizer_eq_bot_iff hBVN).mpr (hBA.trans hAVC)
  rw [induced_sup hAVN hBgN,induced_sup hAN hBVN,hA0,hB0,bot_sup_eq,sup_bot_eq] at he
  exact he.symm

/-- A central layer bounds the actual induced action rank by the source
quotient corank, without selecting a faithful model. -/
theorem image_rank_le_layer_corank
    {V B Z : Subgroup G} [IsElementaryAbelian 2 B]
    (hBN : B ≤ normalizer (V : Set G)) (hZB : Z ≤ B)
    (hZC : Z ≤ centralizer (V : Set G)) :
    rank (inducedAutomizer V B) ≤ subgroupCorank B Z := by
  have h := offender_corank_add (W := B) (A := B ⊓ centralizer (V : Set G))
    (B := Z) (le_inf hZB hZC) inf_le_left
  rw [← rank_inducedAutomizer V B hBN] at h
  omega

/-- The penultimate exchange identity forces a small action image, giving
the final two-group contradiction in the literal F.9 source setup. -/
theorem source_pair_isTwo_of_layer_exchange
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (g : G) (hg : g ∈ D.H)
    (hin : g ∈ D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom)
    (hseed : Nat.card D.Vplus = 8)
    (hhyper : subgroupCorank D.V (D.V ⊓ D.QH) ≤ 1)
    (hr : (3 : ℕ∞) < globalR D.V)
    (hc : ⁅D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom,
        (D.V ⊓ D.QH) ⊔ (D.V ⊓ D.QH).map (MulAut.conj g).toMonoidHom⁆ ≤
      D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom) :
    IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let := h.elementary
  let f := (MulAut.conj g).toMonoidHom
  let B := D.Vplus.map f
  let _ : IsElementaryAbelian 2 D.Vplus := IsElementaryAbelian.of_le h.plus_le
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hQ : D.QH.map f = D.QH := mem_normalizer_iff_map_conj_eq.mp
    (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D) hg)
  have hAg : (D.V ⊓ D.QH).map f = D.V.map f ⊓ D.QH := by
    rw [map_inf _ _ _ (MulAut.conj g).injective,hQ]
  have hAN : (D.V ⊓ D.QH).map f ≤ normalizer (D.V : Set G) := by
    rw [hAg]
    exact inf_le_right.trans (h.QH_le_T.trans h.T_normalizes_V)
  have hseedA : D.Vplus ≤ D.V ⊓ D.QH :=
    le_inf h.plus_le ((le_conjugateSpanBy D.Vplus D.H).trans h.UH_le_QH)
  have him := conjugate_hyperplane_image_eq_seed g hseedA inf_le_left hin hAN hc
  have hZmap : D.V₁.map f = D.V₁ := mem_normalizer_iff_map_conj_eq.mp
    ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hg)
  have hZB : D.V₁ ≤ B := hZmap ▸ map_mono h.point_lt.le
  have hZC : D.V₁ ≤ centralizer (D.V : Set G) :=
    (le_centralizer_iff.mp h.H_centralizes).trans (centralizer_le h.V_le_H)
  have hBN : B ≤ normalizer (D.V : Set G) := (map_mono hseedA).trans hAN
  have hBcard : Nat.card B = 8 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hseed
  have hZcard : Nat.card (D.V₁.subgroupOf B) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZB).toEquiv).trans h.point_card
  have hindex := (D.V₁.subgroupOf B).index_mul_card
  rw [hZcard,hBcard] at hindex
  have hcor : subgroupCorank B D.V₁ = 2 := by
    change Nat.log 2 (D.V₁.subgroupOf B).index = 2
    have hi : (D.V₁.subgroupOf B).index = 4 := by omega
    rw [hi]
    decide
  have hrank : rank (inducedAutomizer D.V (D.V.map f ⊓ D.QH)) ≤ 2 := by
    rw [← hAg,him]
    exact (image_rank_le_layer_corank hBN hZB hZC).trans_eq hcor
  by_contra hp
  have hh := source_pair_image_rank_three h g hg hhyper hr hp
  exact (not_le_of_gt (show 2 < 3 by decide)) (hh.trans hrank)

/-- The full terminal pair argument from the two literal cross-displacement
bounds. The quotient-centralization and layer-exchange steps are derived. -/
theorem source_pair_isTwo_of_cross_displacements
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (g : G) (hg : g ∈ D.H)
    (hin : g ∈ D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom)
    (hseed : Nat.card D.Vplus = 8)
    (hhyper : subgroupCorank D.V (D.V ⊓ D.QH) ≤ 1)
    (hr : (3 : ℕ∞) < globalR D.V)
    (hforward : ⁅D.V,(D.V ⊓ D.QH).map (MulAut.conj g).toMonoidHom⁆ ≤ D.Vplus)
    (hbackward : ⁅D.V.map (MulAut.conj g).toMonoidHom,D.V ⊓ D.QH⁆ ≤
      D.Vplus.map (MulAut.conj g).toMonoidHom) :
    IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let := h.elementary
  let _ : IsElementaryAbelian 2 (D.V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hs : D.Vplus ≤ D.V ⊓ D.QH :=
    le_inf h.plus_le ((le_conjugateSpanBy D.Vplus D.H).trans h.UH_le_QH)
  apply source_pair_isTwo_of_layer_exchange h g hg hin hseed hhyper hr
  exact conjugate_pair_commutator_bound D.V (D.V.map (MulAut.conj g).toMonoidHom)
    (D.V ⊓ D.QH) ((D.V ⊓ D.QH).map (MulAut.conj g).toMonoidHom)
    D.Vplus (D.Vplus.map (MulAut.conj g).toMonoidHom)
    inf_le_left (map_mono inf_le_left) hs (map_mono hs) hforward hbackward

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
