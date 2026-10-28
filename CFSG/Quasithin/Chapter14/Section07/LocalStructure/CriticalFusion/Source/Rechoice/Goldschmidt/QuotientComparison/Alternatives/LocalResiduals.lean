module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Basic
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual
public import Theory.GroupTheory.NormalSymmetricThreeMarked

/-!
# Local residual centralization in the comparison for 14.7.70

In a Goldschmidt triple, the local two-residuals have order dividing three
 times a power of two. A normal S₃ therefore makes each local residual either
 its cubic residual or a subgroup centralizing it. F.6.6 excludes the case
 where both centralize it, and the other cases make the two local residuals
 commute.

The literal L₁ and Y are two-perfect by their definitions. Their images
 lie in these local residuals. Thus a normal S₃ in the actual I/O₂(I) would
 make Y⁺ normalize L₁⁺, contradicting the preceding source geometry.
 No equality between the plus and bang quotients is used.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
 Lemma 14.7.70, printed p.1075 (PDF p.1092), and F.6.6, printed p.305.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives

private theorem local_residual_card {D : Type*} [Group D] [Finite D]
    (A : Subgroup D) (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) :
    ∃ n, Nat.card ((pResidual 2 A).map A.subtype) ∣ 3 * 2 ^ n := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hi : (pCore 2 A).index = 6 := by
    rw [index_eq_card, Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hc : Nat.card A = 3 * 2 ^ (n + 1) := by
    rw [← (pCore 2 A).index_mul_card, hi, hn, pow_succ]
    ring
  refine ⟨n + 1, ?_⟩
  rw [card_map_of_injective A.subtype_injective, ← hc]
  exact (pResidual 2 A).card_subgroup_dvd_card

/-- The local residuals of a Goldschmidt triple commute if there is a
normal symmetric-three subgroup. -/
private theorem local_residuals_commute_of_normal_symmetricThree
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (h : ChapterF.IsGoldschmidtTriple A B)
    (K : Subgroup D) [K.Normal] (e : K ≃* Equiv.Perm (Fin 3)) :
    (pResidual 2 A).map A.subtype ≤
      centralizer ((pResidual 2 B).map B.subtype : Set D) := by
  let X := (pResidual 2 A).map A.subtype
  let Y := (pResidual 2 B).map B.subtype
  let R := NormalSymmetricThreeMarked.residual K
  obtain ⟨S, hS⟩ := h.intersection_sylow
  have hx := NormalSymmetricThreeMarked.eq_residual_or_centralizes_of_card_dvd
    K e S X (isPPerfect_embedded_pResidual 2 A)
    (hS ▸ h.intersection_normalizes_left_residual) (local_residual_card A h.quotient_left.some)
  have hy := NormalSymmetricThreeMarked.eq_residual_or_centralizes_of_card_dvd
    K e S Y (isPPerfect_embedded_pResidual 2 B)
    (hS ▸ h.intersection_normalizes_right_residual) (local_residual_card B h.quotient_right.some)
  have hR : Nat.card R = 3 := NormalSymmetricThreeMarked.residual_card K e
  have hRK : R ≤ K := map_subtype_le _
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · change X ≤ centralizer (Y : Set D)
    rw [hx, hy]
    let : IsCyclic R := isCyclic_of_prime_card hR
    exact le_centralizer R
  · change X ≤ centralizer (Y : Set D)
    rw [hx]
    exact hRK.trans (le_centralizer_iff.mp hy)
  · change X ≤ centralizer (Y : Set D)
    rw [hy]
    exact hx.trans (centralizer_le hRK)
  · have hc : pResidual 2 D ≤ centralizer (K : Set D) := by
      rw [h.twoResidual_eq_sup]
      exact sup_le hx hy
    have hRC : R ≤ centralizer (K : Set D) := (map_pResidual_le 2 K.subtype).trans hc
    have hKR : K ≤ R :=
      (le_inf le_rfl (le_centralizer_iff.mp hRC)).trans
        (NormalSymmetricThreeMarked.inf_centralizer_residual_le K e)
    have hb := Nat.card_le_card_of_injective (inclusion hKR) (inclusion_injective hKR)
    rw [hR, Nat.card_congr e.toEquiv] at hb
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hb

private theorem perfect_le_local_residual {D : Type*} [Group D]
    (X A : Subgroup D) (hle : X ≤ A) (hp : IsPPerfect 2 X) :
    X ≤ (pResidual 2 A).map A.subtype := by
  let e := (subgroupOfEquivOfLe hle).symm
  have hh := map_mono (le_pResidual_of_isPPerfect (X.subgroupOf A)
    (hp.of_surjective e.toMonoidHom e.surjective)) (f := A.subtype)
  rwa [map_subgroupOf_eq_of_le hle] at hh

open Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The literal L₁ is two-perfect, directly from its residual definition. -/
theorem L₁_twoPerfect : IsPPerfect 2 (F.Li L 1) := by
  change IsPPerfect 2 ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
  exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)

/-- The literal Y is two-perfect, directly from its residual definition. -/
theorem Y_twoPerfect : IsPPerfect 2 (Y c) :=
  isPPerfect_embedded_pResidual 2 (YE c)

/-- Adjoining the original T to Y does not change its two-residual. -/
theorem YT_residual (h : Geometry d c) :
    (pResidual 2 (YT c)).map (YT c).subtype = Y c :=
  embedded_pResidual_join_pGroup (Y c) (T : Subgroup G) (Y_twoPerfect c)
    T.isPGroup' h.T_normalizes_Y

omit [Finite G] in
private theorem plus_perfect (A : Subgroup G) (hAI : A ≤ I c)
    (hA : IsPPerfect 2 A) : IsPPerfect 2 (plus c A) := by
  let e := (subgroupOfEquivOfLe hAI).symm
  exact (hA.of_surjective e.toMonoidHom e.surjective).of_surjective
    ((plusMap c).subgroupMap _) ((plusMap c).subgroupMap_surjective _)

/-- The plus image of each source residual lies in the corresponding
local two-residual, with no identification of the ambient quotients. -/
theorem source_images_le_local_residuals :
    plus c (F.Li L 1) ≤ (pResidual 2 (plus c (group F L))).map (plus c (group F L)).subtype ∧
    plus c (Y c) ≤ (pResidual 2 (plus c (YT c))).map (plus c (YT c)).subtype := by
  constructor
  · apply perfect_le_local_residual
    · exact map_mono (subgroupOf_mono _ le_sup_left)
    · exact plus_perfect c _ (L₁_le_I c) (L₁_twoPerfect (F := F) (L := L))
  · apply perfect_le_local_residual
    · exact map_mono (subgroupOf_mono _ le_sup_left)
    · exact plus_perfect c _ (Y_le_I c) (Y_twoPerfect c)

/-- The source nonnormality rules out every actual normal S₃ in I/O₂(I).
This is the centralization contradiction on printed p.1075. -/
theorem no_normal_symmetricThree (h : Geometry d c) (k : CoreFacts c)
    (K : Subgroup ((I c) ⧸ pCore 2 (I c))) [K.Normal]
    (e : K ≃* Equiv.Perm (Fin 3)) : False := by
  have hc := local_residuals_commute_of_normal_symmetricThree k.triple.quotient_twoCore K e
  obtain ⟨hl, hy⟩ := source_images_le_local_residuals c
  apply Y_plus_not_normalizes_L₁ d c h k.centralizes
  exact (hy.trans ((le_centralizer_iff.mp hc).trans
    (centralizer_le hl))).trans (Subgroup.centralizer_le_normalizer _)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives
