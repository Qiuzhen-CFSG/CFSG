module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Intersections
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.Representation.BinarySevenCode.NormalizerGeometry

/-!
# The corrected rank bound in the A₇ weak-closure argument

An element of C(U) outside N(V) puts U in an escaping intersection V ∩ Vᵍ.
The genuine intersection theorem makes every nonidentity word in U have weight
four. Such a code is totally isotropic in the six-dimensional natural module,
so its rank is at most three. Thus r(G,V) ≥ 3, which already supplies the
strict bound r > 1 needed by E.3.35 and the terminal source argument.

At rank three, coordinate separation controls the centralizer inside N(V),
and structural TI gives the corresponding equality inside N(L). No ambient
simplex-centralizer containment or rank-four bound is assumed or asserted.
The final w > 1 conclusion still requires exclusion of the actual W₁ actors.

Source: Aschbacher--Smith, 12.3.9--11, printed pp.810--811, and E.3.3--4.
The earlier source producer of LocalAnalysis remains explicit.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 ChapterE BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable (S : Setup T L V) (D : S.LocalAnalysis)
variable (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
include S D structural

/-- A genuine escaping ambient centralizer forces constant weight four. -/
theorem weight_four_of_escaping_centralizer {U : Subgroup G} (hUV : U ≤ V)
    (hesc : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    D.model.WeightFour U := by
  obtain ⟨g, hg, hgN⟩ := SetLike.not_le_iff_exists.mp hesc
  intro v hv hv1
  have hvG : (v : G) ≠ 1 := fun he => hv1 (Subtype.ext he)
  apply intersection_weight_four S D structural hgN (x := (v : G)) ?_ hvG
  refine ⟨v.property, ?_⟩
  refine ⟨v, hUV hv, ?_⟩
  change g * v.val * g⁻¹ = v.val
  exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hg) _ hv).symm

/-- The corrected replacement for the unjustified rank-four assertion:
every escaping-centralizer subgroup has rank at most three. -/
theorem escaping_subgroup_rank_le_three {U : Subgroup G} (hUV : U ≤ V)
    (hesc : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    Nat.log 2 (Nat.card U) ≤ 3 :=
  D.model.log_card_le_three_of_weight_four hUV
    (weight_four_of_escaping_centralizer S D structural hUV hesc)

/-- The actual source parameter satisfies r(G,V) ≥ 3, including the simplex case. -/
theorem globalR_ge_three : (3 : ℕ∞) ≤ globalR V := by
  let _ := S.chosen.elementary
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV, hesc⟩
  have hb := escaping_subgroup_rank_le_three S D structural hUV hesc
  have hr : 3 ≤ subgroupCorank V U := by
    rw [subgroupCorank, ← log_card_sub_log_card_eq_log_relIndex V U hUV,
      D.model.log_card_eq_six]
    omega
  exact_mod_cast hr

/-- The exact r-bound consumed by E.3.35 and the terminal A₇ argument. -/
theorem one_lt_globalR : (1 : ℕ∞) < globalR V :=
  lt_of_lt_of_le (by decide : (1 : ℕ∞) < 3) (globalR_ge_three S D structural)

/-- Every subgroup of corank at most two has its full centralizer in N(V). -/
theorem centralizer_normalizes_of_corank_le_two {U : Subgroup G} (hUV : U ≤ V)
    (hr : subgroupCorank V U ≤ 2) :
    centralizer (U : Set G) ≤ normalizer (V : Set G) := by
  apply centralizer_le_normalizer_of_corank_lt_globalR hUV
  apply lt_of_lt_of_le _ (globalR_ge_three S D structural)
  exact_mod_cast (show subgroupCorank V U < 3 by omega)

/-- The same full-centralizer control on every actual conjugate, as needed
when lifting a hyperplane of an offender's permutation image. -/
theorem conjugate_centralizer_normalizes_of_corank_le_two (g : G)
    {U : Subgroup G} (hUV : U ≤ V.map (MulAut.conj g).toMonoidHom)
    (hr : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) U ≤ 2) :
    centralizer (U : Set G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  apply centralizer_le_normalizer_of_corank_lt_globalR hUV
  rw [globalR_map_equiv]
  apply lt_of_lt_of_le _ (globalR_ge_three S D structural)
  exact_mod_cast (show subgroupCorank (V.map (MulAut.conj g).toMonoidHom) U < 3 by omega)

/-- The kernel of an offending conjugate action has rank at most three.
The conclusion uses the literal ambient centralizer and original conjugate. -/
theorem conjugate_centralizer_rank_le_three (g : G)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Nat.log 2 (Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) :
      Subgroup G)) ≤ 3 := by
  let _ := S.chosen.elementary
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hb := (globalR_ge_three S D structural).trans
    (globalR_le_conjugate_centralizer_corank g hn)
  have hb' : 3 ≤ subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)) := by exact_mod_cast hb
  rw [subgroupCorank, ← log_card_sub_log_card_eq_log_relIndex _ _ inf_le_left,
    card_map_of_injective (MulAut.conj g).injective, D.model.log_card_eq_six] at hb'
  omega

/-- Uniformly for every rank-three weight-four subgroup, the local centralizer
inside M=N(L) equals C_M(V). This is not an ambient containment assertion. -/
theorem local_rank_three_centralizer {U : Subgroup G} (hUV : U ≤ V)
    (hw : D.model.WeightFour U) (hr : Nat.log 2 (Nat.card U) = 3) :
    normalizer (L : Set G) ⊓ centralizer (U : Set G) =
      normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
  have hUne : U ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hr
    norm_num at hr
  apply le_antisymm
  · apply le_inf inf_le_left
    have hTI := inf_centralizer_le_normalizer_of_trivial_intersections
      (S.hypothesis.source_chosen_TI structural S.chosen) hUne hUV
    exact (le_inf hTI inf_le_right).trans
      (D.model.normalizer_inf_centralizer_of_weight_four_rank_three hUV hw hr).le
  · exact inf_le_inf_left _ (centralizer_le hUV)

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
