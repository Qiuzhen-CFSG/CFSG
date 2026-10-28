module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Preliminaries
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SylowLocalCore

/-!
# Relative residual normalizations and Sylow placement in 14.7.67

With D = C_{N(K)}(K/O₂(K)) and D₁ = O²(D ∩ N(L)), the original
Sylow subgroup normalizes both D and D₁. The two-core of K lies in T,
so adjoining it preserves the two-residual of D₁ and of L₁. Conjugation
modulo O₂(K) then gives the actual K- and D-normalizations.

Independently, D ∩ H ≤ T makes D ∩ T a normal two-subgroup of L₁T,
hence it lies in R₁. Restriction of the ambient Sylow subgroup to the
T-invariant product DR₁ proves R₁ ∈ Syl₂(DR₁), with an actual Sylow
witness. No maximality is inferred merely from being a two-subgroup.

These deductions do not yet prove D₁ = 1 or Baumann control. The remaining
steps are centralization on L/O₂(L), uniqueness over LT, and construction
of the four noncentral two-chief factors using 14.5.21.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.67(4), printed p.1070, PDF p.1087.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace ResidualNormalizer

omit [Finite G] in
private theorem normalizes_join_of_commutator {A B X : Subgroup G}
    (hc : ⁅X, A⁆ ≤ B) (hn : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx y hy
  have ha : A.map (MulAut.conj x).toMonoidHom ≤ A ⊔ B := by
    rintro _ ⟨a, ha, rfl⟩
    have hh := (A ⊔ B).mul_mem
      (mem_sup_right (hc (commutator_mem_commutator hx ha))) (mem_sup_left ha)
    change x * a * x⁻¹ ∈ A ⊔ B
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
  have hb : B.map (MulAut.conj x).toMonoidHom ≤ B :=
    (mem_normalizer_iff_map_conj_eq.mp (hn hx)).le
  have hjoin : (A ⊔ B).map (MulAut.conj x).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le ha (hb.trans le_sup_right)
  exact hjoin (mem_map_of_mem _ hy)

omit [Finite G] in
theorem T_normalizes_D : (T : Subgroup G) ≤ normalizer (D F : Set G) :=
  ((F.invariant 1).trans (H_normalizes_K F)).trans normalizer_K_normalizes_D

omit [Finite G] in
theorem K_core_le_T : (K F).pCoreIn 2 ≤ (T : Subgroup G) :=
  (pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)).trans
    ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1)))

omit [Finite G] in
theorem T_normalizes_D₁ (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (D₁ L F : Set G) :=
  ((le_inf T_normalizes_D (hTM.trans (normalizer (L : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

/-- O²(D₁O₂(K)) is exactly D₁; normality is relative to the product. -/
theorem D₁_core_residual (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (pResidual 2 (D₁ L F ⊔ (K F).pCoreIn 2 : Subgroup G)).map
      (D₁ L F ⊔ (K F).pCoreIn 2).subtype = D₁ L F :=
  embedded_pResidual_join_pGroup _ _ D₁_twoPerfect (isPGroup_pCoreIn 2 _)
    (K_core_le_T.trans (T_normalizes_D₁ hTM))

/-- The source KT-normalization follows from the literal section commutator. -/
theorem H_normalizes_D₁ (d : Data T L V F W)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    F.H ≤ normalizer (D₁ L F : Set G) := by
  rw [d.residual_product]
  refine sup_le ?_ (T_normalizes_D₁ hTM)
  have hn : K F ≤ normalizer ((D₁ L F ⊔ (K F).pCoreIn 2 : Subgroup G) : Set G) :=
    normalizes_join_of_commutator
      ((commutator_mono le_rfl (D₁_le.trans inf_le_left)).trans
        ((commutator_comm _ _).trans_le D_commutator))
      ((K F).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hr := hn.trans (normalizer_le_normalizer_characteristic_image
    (D₁ L F ⊔ (K F).pCoreIn 2) (pResidual 2 _))
  rwa [D₁_core_residual hTM] at hr

omit [Finite G] in
theorem Li_le_K : F.Li L 1 ≤ K F := by
  change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype ≤ _
  exact embedded_pResidual_mono 2 inf_le_right

theorem Li_twoPerfect : IsPPerfect 2 (F.Li L 1) := by
  change IsPPerfect 2 ((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype)
  exact isPPerfect_embedded_pResidual 2 _

omit [Finite G] in
theorem T_normalizes_Li (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
  change (T : Subgroup G) ≤ normalizer
    ((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype : Set G)
  exact ((le_inf hTM ((F.invariant 1).trans F.H.le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

/-- The second residual identity in the source uses the same O₂(K). -/
theorem Li_core_residual (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (pResidual 2 (F.Li L 1 ⊔ (K F).pCoreIn 2 : Subgroup G)).map
      (F.Li L 1 ⊔ (K F).pCoreIn 2).subtype = F.Li L 1 :=
  embedded_pResidual_join_pGroup _ _ Li_twoPerfect (isPGroup_pCoreIn 2 _)
    (K_core_le_T.trans (T_normalizes_Li hTM))

/-- In fact the whole section kernel D normalizes L₁. -/
theorem D_normalizes_Li (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    D F ≤ normalizer (F.Li L 1 : Set G) := by
  have hn : D F ≤ normalizer ((F.Li L 1 ⊔ (K F).pCoreIn 2 : Subgroup G) : Set G) :=
    normalizes_join_of_commutator ((commutator_mono le_rfl Li_le_K).trans D_commutator)
      (D_le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hr := hn.trans (normalizer_le_normalizer_characteristic_image
    (F.Li L 1 ⊔ (K F).pCoreIn 2) (pResidual 2 _))
  rwa [Li_core_residual hTM] at hr

/-- Centralization is on the actual quotient L₁/O₂(L₁). -/
theorem D_commutator_Li (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ⁅D F, F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
  have hi : (K F).pCoreIn 2 ⊓ F.Li L 1 ≤ (F.Li L 1).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 (K F)).to_le inf_le_left) inf_le_right
      ((le_inf ((Li_le_K.trans (K F).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
        (F.Li L 1).le_normalizer).trans inf_normalizer_le_normalizer_inf)
  exact (le_inf ((commutator_mono le_rfl Li_le_K).trans D_commutator)
    (le_normalizer_iff_commutator_le_right.mp (D_normalizes_Li hTM))).trans hi

omit [Finite G] in
private theorem core_ne_bot_of_normalized_twoPerfect
    {X M : Subgroup G} (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hp : IsPPerfect 2 X) (hchar : HasCharacteristicTwo M) (hne : X ≠ ⊥) :
    X.pCoreIn 2 ≠ ⊥ := by
  intro hbot
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow M (T.subtype hTM)).trans_eq (map_subgroupOf_eq_of_le hTM)
  have hXQ : X ≤ normalizer (M.pCoreIn 2 : Set G) :=
    (hXM.trans M.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hi : X ⊓ M.pCoreIn 2 ≤ X.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 M).to_le inf_le_right) inf_le_left
      ((le_inf X.le_normalizer hXQ).trans inf_normalizer_le_normalizer_inf)
  have hc : X ≤ centralizer (M.pCoreIn 2 : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [← hbot]
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp (hQT.trans hn))
      (le_normalizer_iff_commutator_le_right.mp hXQ)).trans hi
  have hXcore : X ≤ M.pCoreIn 2 := by
    intro x hx
    have hm : (⟨x, hXM hx⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
      intro y hy
      apply Subtype.ext
      exact mem_centralizer_iff.mp (hc hx) y (mem_map.mpr ⟨y, hy, rfl⟩)
    exact mem_map.mpr ⟨⟨x, hXM hx⟩, hchar hm, rfl⟩
  have he := hp.hom_eq_one_of_isPGroup ((isPGroup_pCoreIn 2 M).to_le hXcore)
    (MonoidHom.id X)
  apply hne
  apply bot_unique
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x, hx⟩)

end ResidualNormalizer

namespace Data
open ResidualNormalizer
variable (d : Data T L V F W)
include d

/-- The intersection statement is proved already at the level of the L₁ core. -/
theorem D_inf_Li_le_core : D F ⊓ F.Li L 1 ≤ (F.Li L 1).pCoreIn 2 := by
  have hLiH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  apply le_pCoreIn_of_normalizes
  · exact T.isPGroup'.to_le ((inf_le_inf_left _ hLiH).trans d.D_inf_H_le_sylow)
  · exact inf_le_right
  · exact (le_inf ((Li_le_K.trans (K F).le_normalizer).trans normalizer_K_normalizes_D)
      (F.Li L 1).le_normalizer).trans inf_normalizer_le_normalizer_inf

omit d [Finite G] in
theorem Ri_le_T : F.Ri L 1 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow _ (T.subtype (le_sup_right : (T : Subgroup G) ≤
    F.Li L 1 ⊔ (T : Subgroup G)))).trans_eq (map_subgroupOf_eq_of_le le_sup_right)

/-- D ∩ T is normal in L₁T and hence lies in its two-core R₁. -/
theorem D_inf_T_le_Ri : D F ⊓ (T : Subgroup G) ≤ F.Ri L 1 := by
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  have hJH : J ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have he : D F ⊓ J = D F ⊓ (T : Subgroup G) := le_antisymm
    (le_inf inf_le_left ((inf_le_inf_left _ hJH).trans d.D_inf_H_le_sylow))
    (le_inf inf_le_left (inf_le_right.trans le_sup_right))
  apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_right)
    (inf_le_right.trans le_sup_right)
  rw [← he]
  exact (le_inf ((hJH.trans (H_normalizes_K F)).trans normalizer_K_normalizes_D)
    J.le_normalizer).trans inf_normalizer_le_normalizer_inf

/-- The specified Sylow subgroup intersects the product DR₁ in R₁. -/
theorem T_inf_D_sup_Ri : (T : Subgroup G) ⊓ (D F ⊔ F.Ri L 1) = F.Ri L 1 := by
  apply le_antisymm _ (le_inf Ri_le_T le_sup_right)
  intro x hx
  have hn : F.Ri L 1 ≤ normalizer (D F : Set G) := Ri_le_T.trans T_normalizes_D
  have hp : x ∈ (D F : Set G) * (F.Ri L 1 : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hx.2
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  have haT : a ∈ (T : Subgroup G) := by
    have hh := (T : Subgroup G).mul_mem hx.1 ((T : Subgroup G).inv_mem (Ri_le_T hb))
    simpa only [mul_inv_cancel_right] using hh
  exact (F.Ri L 1).mul_mem (d.D_inf_T_le_Ri ⟨ha, haT⟩) hb

/-- Actual Sylow placement in DR₁, obtained by relative normal restriction. -/
theorem Ri_isSylowIn_D_sup_Ri : Chapter1.IsSylowIn 2 (F.Ri L 1) (D F ⊔ F.Ri L 1) := by
  let Y := D F ⊔ F.Ri L 1
  have hTR : (T : Subgroup G) ≤ normalizer (F.Ri L 1 : Set G) :=
    (le_sup_right : (T : Subgroup G) ≤ F.Li L 1 ⊔ (T : Subgroup G)).trans
      ((F.Li L 1 ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    (le_inf T_normalizes_D hTR).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨P, hP⟩ := (T.subtype (le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G))).exists_map_subtype_eq_inf_of_normalizes
    (N := Y) le_sup_left (sup_le Y.le_normalizer hTY)
  change (P : Subgroup Y).map Y.subtype =
    ((T : Subgroup G).subgroupOf (Y ⊔ (T : Subgroup G))).map
      (Y ⊔ (T : Subgroup G)).subtype ⊓ Y at hP
  rw [map_subgroupOf_eq_of_le le_sup_right] at hP
  exact ⟨P, hP.trans d.T_inf_D_sup_Ri⟩

/-- The second product-residual identity, with the original L two-core. -/
theorem D₁_L_core_residual
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (pResidual 2 (D₁ L F ⊔ L.pCoreIn 2 : Subgroup G)).map
      (D₁ L F ⊔ L.pCoreIn 2).subtype = D₁ L F := by
  have hTM := d.natural.sylow_normalizes structural
  have hQLT : L.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_mono_of_normalizes (le_sup_left : L ≤ L ⊔ (T : Subgroup G))
      (sup_le L.le_normalizer hTM)).trans
      ((pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
        (map_subgroupOf_eq_of_le le_sup_right))
  exact embedded_pResidual_join_pGroup _ _ D₁_twoPerfect (isPGroup_pCoreIn 2 _)
    (hQLT.trans (T_normalizes_D₁ hTM))

/-- Centralization on L/O₂(L) promotes normalization to all of LT. This
premise is the still separate L₃(2) section argument in the source. -/
theorem LT_normalizes_D₁_of_sectionCentralization
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hc : ⁅D₁ L F, L⁆ ≤ L.pCoreIn 2) :
    L ⊔ (T : Subgroup G) ≤ normalizer (D₁ L F : Set G) := by
  refine sup_le ?_ (T_normalizes_D₁ (d.natural.sylow_normalizes structural))
  have hn : L ≤ normalizer ((D₁ L F ⊔ L.pCoreIn 2 : Subgroup G) : Set G) :=
    normalizes_join_of_commutator ((commutator_comm _ _).trans_le hc)
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hr := hn.trans (normalizer_le_normalizer_characteristic_image
    (D₁ L F ⊔ L.pCoreIn 2) (pResidual 2 _))
  rwa [d.D₁_L_core_residual structural] at hr

/-- A nontrivial D₁ has nontrivial two-core. This is why maximal two-local
uniqueness applies to its normalizer, despite D₁ being a two-residual. -/
theorem D₁_core_ne_bot
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (hne : D₁ L F ≠ ⊥) : (D₁ L F).pCoreIn 2 ≠ ⊥ := by
  have hTM := d.natural.sylow_normalizes structural
  exact core_ne_bot_of_normalized_twoPerfect hTM (D₁_le.trans inf_le_right)
    (T_normalizes_D₁ hTM) D₁_twoPerfect
    (d.counterexample.qtke.evenCharacteristic T _
      (d.natural.maximal_unique structural uniqueness).1 hTM) hne

/-- The uniqueness/escape end of the D₁ argument, retaining precisely the
unproved section-centralization step as an explicit premise. -/
theorem D₁_eq_bot_of_sectionCentralization
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (hc : ⁅D₁ L F, L⁆ ≤ L.pCoreIn 2) : D₁ L F = ⊥ := by
  by_contra hne
  have hTM := d.natural.sylow_normalizes structural
  have hchar := normalizer_le_normalizer_characteristic_image (D₁ L F) (pCore 2 (D₁ L F))
  have hn : normalizer ((D₁ L F).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp ((d.natural.maximal_unique structural uniqueness).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN, hJN⟩)
    · exact isPGroup_pCoreIn 2 _
    · exact d.D₁_core_ne_bot structural uniqueness hne
    · exact (d.LT_normalizes_D₁_of_sectionCentralization structural hc).trans hchar
  exact d.K_not_le_normalizer_L hTM
    (((K_le_H F).trans (H_normalizes_D₁ d hTM)).trans (hchar.trans hn))

/-- The two intersection conclusions after the source centralization step. -/
theorem residual_intersections_of_sectionCentralization
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (hc : ⁅D₁ L F, L⁆ ≤ L.pCoreIn 2) :
    D₁ L F = ⊥ ∧ D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) := by
  have hz := d.D₁_eq_bot_of_sectionCentralization structural uniqueness hc
  exact ⟨hz, (D₁_eq_bot_iff_inf_le_sylow (d.natural.sylow_normalizes structural)).mp hz⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
