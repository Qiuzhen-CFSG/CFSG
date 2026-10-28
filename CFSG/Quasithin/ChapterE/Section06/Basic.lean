module

public import CFSG.Quasithin.ChapterE.Section06.Defs
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.TINormalizerControl

/-!
# Normalizers and centralizers in the E.6 setup

The uniqueness subgroup in E.6.1 normalizes both `V` and `Q = C_T(V)`.
Each is a nonidentity two-group, so its full normalizer is two-local and
lies in the unique maximal two-local `M`. The TI condition then controls
the local centralizers of every nonidentity subgroup of `V`.

These prove the preliminary observations, Lemma E.6.2 and the normality
clause E.6.5(3) in Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.245–246. The Sylow and structural clauses of E.6.5 are separate.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06

open Subgroup

universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}

namespace HypothesisE61

theorem sylow_le_normalizer (h : HypothesisE61 K T M V) :
    (T : Subgroup G) ≤ normalizer (V : Set G) :=
  (normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow

theorem normalizer_le (h : HypothesisE61 K T M V) :
    normalizer (V : Set G) ≤ M := by
  let _ := h.elementary
  exact normalizer_le_of_unique_maximalTwoLocal h.unique
    (IsElementaryAbelian.isPGroup 2 V) h.nontrivial (inf_le_left.trans inf_le_right)

theorem localNormalizer_eq (h : HypothesisE61 K T M V) :
    localNormalizer M V = normalizer (V : Set G) :=
  inf_eq_right.mpr h.normalizer_le

theorem centralizer_le (h : HypothesisE61 K T M V) :
    centralizer (V : Set G) ≤ M :=
  (Subgroup.centralizer_le_normalizer _).trans h.normalizer_le

theorem le_sylowCentralizer (h : HypothesisE61 K T M V) :
    V ≤ sylowCentralizer (T : Subgroup G) V := by
  let _ := h.elementary
  exact le_inf h.le_sylow V.le_centralizer

theorem sylowCentralizer_ne_bot (h : HypothesisE61 K T M V) :
    sylowCentralizer (T : Subgroup G) V ≠ ⊥ :=
  fun he => h.nontrivial (le_bot_iff.mp (he ▸ h.le_sylowCentralizer))

theorem normalizer_sylowCentralizer_le (h : HypothesisE61 K T M V) :
    normalizer (sylowCentralizer (T : Subgroup G) V : Set G) ≤ M := by
  exact normalizer_le_of_unique_maximalTwoLocal h.unique
    (T.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left))
    h.sylowCentralizer_ne_bot inf_le_right

/-- E.6.2: a subgroup outside `M` cannot centralize `V`. -/
theorem lemma_E_6_2 (h : HypothesisE61 K T M V) {L : Subgroup G}
    (hL : ¬ L ≤ M) : ⁅V, L⁆ ≠ ⊥ := by
  intro he
  exact hL ((le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp he)).trans h.centralizer_le)

theorem localCentralizer_le_normalizer (h : HypothesisE61 K T M V)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V) :
    M ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G) :=
  inf_centralizer_le_normalizer_of_trivial_intersections h.ti hU hUV

/-- For nonidentity subspaces, escape from `M` is exactly escape from
`N_G(V)`, the condition in the genuine global parameter `r`. -/
theorem centralizer_le_iff (h : HypothesisE61 K T M V)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V) :
    centralizer (U : Set G) ≤ M ↔ centralizer (U : Set G) ≤ normalizer (V : Set G) := by
  constructor
  · intro hc
    exact (le_inf hc le_rfl).trans (h.localCentralizer_le_normalizer hU hUV)
  · exact fun hc => hc.trans h.normalizer_le

/-- E.6.5(3), valid for every nonidentity subspace of `V`. -/
theorem normal_in_localCentralizer (h : HypothesisE61 K T M V)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V) :
    V ≤ M ⊓ centralizer (U : Set G) ∧
      (V.subgroupOf (M ⊓ centralizer (U : Set G))).Normal := by
  let _ := h.elementary
  have hVC : V ≤ M ⊓ centralizer (U : Set G) :=
    le_inf (h.le_sylow.trans h.sylow_le) (V.le_centralizer.trans (Subgroup.centralizer_le hUV))
  exact ⟨hVC, (normal_subgroupOf_iff_le_normalizer hVC).mpr
    (h.localCentralizer_le_normalizer hU hUV)⟩

end HypothesisE61
end CFSG.Quasithin.ChapterE.Section06
