module

public import CFSG.Quasithin.ChapterB.Section02.Baumann.Defs

/-!
# Rank equality and the fixed centers in Baumann's argument

The no-strong-offender bound is opposite to the maximum-elementary rank
bound B.2.4. Therefore equality holds, including for trivial action images.
The sharp case of B.2.4 puts a maximum elementary subgroup in C_R(V), and
gives both V and α(R) inside α(C_R(V)). In particular W = α(R)V really is
elementary abelian; this is needed before applying a dimension argument.

We also establish normality of C_R(V) in LR with relative, rather than
ambient, normality. Source: Aschbacher–Smith B.2.18, printed pp.80–81.
-/

namespace CFSG.Quasithin.ChapterB.BaumannArgument

open Stellmacher Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The action kernel is the full ambient centralizer of V. -/
public theorem actionMap_ker (V : Subgroup G) [V.Normal] :
    (actionMap V).ker = Subgroup.centralizer (V : Set G) :=
  QuotientGroup.ker_mk' _

omit [Finite G] in
/-- The first preliminary conclusion needs just the normalization part of (a). -/
public theorem centralizer_normal_in_join (V R L : Subgroup G) [V.Normal]
    (hL : L ≤ Subgroup.normalizer (R ⊓ Subgroup.centralizer (V : Set G) : Set G)) :
    ((R ⊓ Subgroup.centralizer (V : Set G)).subgroupOf (L ⊔ R)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (inf_le_left.trans le_sup_right)).mpr
  apply sup_le hL
  exact (le_inf R.le_normalizer Subgroup.le_normalizer_of_normal).trans
    Subgroup.inf_normalizer_le_normalizer_inf

/-- The upper and lower offender bounds agree for every maximum elementary
subgroup, including those acting trivially on V. -/
public theorem maximal_rank_equality (V R A : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) :
    fixedCodim V A = Nat.log 2 (Nat.card (A.map (actionMap V))) := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  by_cases hz : A.map (actionMap V) = ⊥
  · have hAC : A ≤ Subgroup.centralizer (V : Set G) := by
      rw [← actionMap_ker V]
      rwa [Subgroup.map_eq_bot_iff] at hz
    have hVC : V ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff.mp hAC
    simp [fixedCodim, inf_eq_left.mpr hVC, hz]
  · apply le_antisymm
    · have h := lemma_B_2_4_1 R V A hVR hA.1 0
        (by rw [maxOrder_eq_card_of_mem R A hA, Nat.sub_zero])
        (actionMap V) (actionMap_ker V) hz
      simpa only [Nat.sub_zero, fixedCodim] using h
    · exact hno A hA.1 (IsElementaryAbelian.map (actionMap V)) hz

/-- Every maximum elementary subgroup has the centralizing replacement
V C_A(V) of the same maximum order. -/
public theorem maximal_replacement (V R A : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) :
    V ⊔ (A ⊓ Subgroup.centralizer (V : Set G)) ∈ elementaryAbelianMaxSubgroups R :=
  (lemma_B_2_4_3 R V A hVR hA (actionMap V) (actionMap_ker V)
    (maximal_rank_equality V R A hVR hno hA)).1

/-- The centralizer has full two-rank; its maximum family is a subfamily
of that of R, and its fixed center contains V and α(R). -/
public theorem centralizer_rank_and_alpha (V R : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R) :
    twoRank (R ⊓ Subgroup.centralizer (V : Set G)) = twoRank R ∧
      elementaryAbelianMaxSubgroups (R ⊓ Subgroup.centralizer (V : Set G)) ⊆
        elementaryAbelianMaxSubgroups R ∧
      V ≤ thompsonAlpha (R ⊓ Subgroup.centralizer (V : Set G)) ∧
      thompsonAlpha R ≤ thompsonAlpha (R ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty R
  exact (lemma_B_2_4_3 R V A hVR hA (actionMap V) (actionMap_ker V)
    (maximal_rank_equality V R A hVR hno hA)).2

/-- The enlarged module W = α(R)V is elementary abelian. -/
public theorem alpha_sup_elementary (V R : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R) :
    IsElementaryAbelian 2 (thompsonAlpha R ⊔ V : Subgroup G) := by
  have h := centralizer_rank_and_alpha V R hVR hno
  let _ : IsElementaryAbelian 2 (thompsonAlpha (R ⊓ Subgroup.centralizer (V : Set G))) :=
    omegaOneCenterAmbient_elementaryAbelian _
  exact IsElementaryAbelian.of_le (sup_le h.2.2.2 h.2.2.1)

/-- The V-part of the fixed center is exactly C_V(J(R)). -/
public theorem alpha_inf_eq_fixed (V R : Subgroup G) [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) :
    thompsonAlpha R ⊓ V = V ⊓ Subgroup.centralizer (elementaryAbelianMaxJ R : Set G) := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.2, Subgroup.mem_centralizer_iff.mpr
      ((mem_omegaOneCenterAmbient_iff _ _).mp hx.1).2.2⟩
  · let E := V ⊓ Subgroup.centralizer (elementaryAbelianMaxJ R : Set G)
    let _ : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ V from inf_le_left)
    exact le_inf
      (elementary_centralizer_maxJ_le_omegaCenter R E (inf_le_left.trans hVR) inf_le_right)
      inf_le_left

omit [Finite G] in
/-- The enlarged subgroup remains in R. -/
public theorem alpha_sup_le (V R : Subgroup G) (hVR : V ≤ R) :
    thompsonAlpha R ⊔ V ≤ R := by
  apply sup_le _ hVR
  intro x hx
  exact (show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1)
    ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1

omit [Finite G] in
/-- The initial fixed-space supplement W = C_W(J(R))V. -/
public theorem alpha_sup_eq_fixed_sup (V R : Subgroup G) :
    thompsonAlpha R ⊔ V =
      ((thompsonAlpha R ⊔ V) ⊓ Subgroup.centralizer
        (elementaryAbelianMaxJ R : Set G)) ⊔ V := by
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply le_sup_of_le_left
    apply le_inf le_sup_left
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr
      ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2
  · exact sup_le inf_le_left le_sup_right

omit [Finite G] in
/-- Enlarging an acting subgroup by the action kernel leaves its fixed
codimension unchanged. -/
public theorem fixedCodim_preimage_image (V A : Subgroup G) [V.Normal] :
    fixedCodim V ((A.map (actionMap V)).comap (actionMap V)) = fixedCodim V A := by
  rw [comap_map_eq, actionMap_ker]
  have hf : V ⊓ centralizer ((A ⊔ centralizer (V : Set G) : Subgroup G) : Set G) =
      V ⊓ centralizer (A : Set G) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le
      (show A ≤ A ⊔ centralizer (V : Set G) from le_sup_left)))
    apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    apply sup_le (le_centralizer_iff.mp inf_le_right)
    exact le_centralizer_iff.mp (inf_le_left.trans (le_centralizer_iff.mp le_rfl))
  simp only [fixedCodim, hf]

omit [Finite G] in
/-- The source premise quantifies over every nontrivial elementary subgroup
of the faithful action image R*, with the genuine full inverse image acting
on V. This certifies the image-based formulation used by the rank lemmas. -/
public theorem noStrongOffenders_iff_quotient (V R : Subgroup G) [V.Normal] :
    NoStrongOffenders V R ↔
      ∀ E : Subgroup (G ⧸ centralizer (V : Set G)), E ≤ R.map (actionMap V) →
        IsElementaryAbelian 2 E → E ≠ ⊥ →
        Nat.log 2 (Nat.card E) ≤ fixedCodim V (E.comap (actionMap V)) := by
  constructor
  · intro h E hER hE hne
    let A := R ⊓ E.comap (actionMap V)
    have hmap : A.map (actionMap V) = E := by
      apply le_antisymm
      · rintro x ⟨a, ha, rfl⟩
        exact ha.2
      · intro x hx
        obtain ⟨a, ha, heq⟩ := hER hx
        exact ⟨a, ⟨ha, show actionMap V a ∈ E from heq.symm ▸ hx⟩, heq⟩
    have hb := h A inf_le_left (hmap.symm ▸ hE) (hmap.symm ▸ hne)
    have hf := fixedCodim_preimage_image V A
    rw [hmap] at hb hf
    rwa [hf]
  · intro h A hAR hAe hne
    have hb := h (A.map (actionMap V)) (map_mono hAR) hAe hne
    rwa [fixedCodim_preimage_image] at hb

end CFSG.Quasithin.ChapterB.BaumannArgument
