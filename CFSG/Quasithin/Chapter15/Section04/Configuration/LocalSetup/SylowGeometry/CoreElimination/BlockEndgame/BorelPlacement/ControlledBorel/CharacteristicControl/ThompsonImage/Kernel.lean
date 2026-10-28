module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.Offenders
public import Theory.GroupAction.PPerfectFixedCentralizer
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# The central omega action has exactly the block radical as kernel

Let D = K₁R and Q = O₂(D). The short-group definition and coprime
commutator idempotence give [U(K₁), K₁] = U(K₁). Apply the A × B lemma
to the commuting actions of K₁ and Q on U(K₁): irreducibility modulo the
K₁-fixed subgroup forces Q to centralize the whole layer. Thus
U(K₁) ≤ Ω₁(Z(Q)).

The given natural-module model identifies both the actual K₁/O₂(K₁)
quotient and its conjugation action, so C_{K₁}(U(K₁)) ≤ O₂(K₁).
Since K₁ is normal in D and D/K₁ is a two-group, C_D(U(K₁)) is a
normal two-group and lies in Q. This bounds the kernel on Ω₁(Z(Q));
the reverse inclusion was proved when constructing the action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.41,
printed p.31; C.1.7–13, pp.123–125; C.2.7, pp.145–146, used in the
rank-one block case of 15.4.20, p.1164.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.ThompsonImage
open Subgroup Stellmacher
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)

/-- Two-perfection makes the first block act fully on its commutator layer. -/
theorem firstLayer_commutator_first :
    ⁅FieldFourCentrality.firstLayer b, b.first⁆ = FieldFourCentrality.firstLayer b := by
  rw [← core_commutator_first b]
  exact commutator_isPPerfect_idempotent b.first (blockRadicalCore b)
    b.model.2.1.twoPerfect (isPGroup_pCoreIn 2 _) (first_normalizes_blockRadicalCore c b)

/-- The short-group irreducibility and the A × B lemma force the local
radical to centralize the first block's layer, as in C.1.11. -/
theorem firstLayer_centralizes_core :
    FieldFourCentrality.firstLayer b ≤ centralizer (blockRadicalCore b : Set G) := by
  let L := b.first
  let U := ChapterC.blockU L
  let Z := FieldFourCentrality.firstLayer b
  let Q := blockRadicalCore b
  let _ : IsElementaryAbelian 2 Z := b.model.2.1.elementary.map L.subtype
  have hLN : L ≤ normalizer (Z : Set G) :=
    le_sup_left.trans (localGroup_normalizes_firstLayer b)
  have hQN : Q ≤ normalizer (Z : Set G) :=
    (pCoreIn_le 2 (localGroup b)).trans (localGroup_normalizes_firstLayer b)
  have hLCQ : L ≤ normalizer (centralizer (Q : Set G) : Set G) :=
    (first_normalizes_blockRadicalCore c b).trans (normalizer_le_normalizer_centralizer Q)
  let _ : ((centralizer (Q : Set G)).subgroupOf L).Normal :=
    normal_subgroupOf_of_le_normalizer hLCQ
  let N := U ⊓ (centralizer (Q : Set G)).subgroupOf L
  let F := U ⊓ center L
  let _ : N.Normal := inferInstanceAs
    (ChapterC.blockU L ⊓ (centralizer (Q : Set G)).subgroupOf L).Normal
  let _ : F.Normal := inferInstanceAs (ChapterC.blockU L ⊓ center L).Normal
  have hfull : ⁅U, (⊤ : Subgroup L)⁆ = U := by
    apply map_injective L.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact firstLayer_commutator_first b
  have hcomm : ⁅Q, L⁆ ≤ centralizer (Z : Set G) := by
    rw [core_commutator_first b]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hirr := b.model.2.1.irreducible.2 (N ⊔ F) inferInstance
    le_sup_right (sup_le inf_le_left inf_le_left)
  have hNF : N ⊔ F = U := by
    rcases hirr with he | he
    · have hfix : ⁅Z ⊓ centralizer (Q : Set G), L⁆ = ⊥ := by
        apply commutator_eq_bot_iff_le_centralizer.mpr
        intro z hz
        obtain ⟨u, hu, rfl⟩ := hz.1
        have huN : u ∈ N := ⟨hu, hz.2⟩
        have heF : N ⊔ F = F := he
        have huF : u ∈ F := heF ▸ (show u ∈ N ⊔ F from (show N ≤ N ⊔ F from le_sup_left) huN)
        apply mem_centralizer_iff.mpr
        intro l hl
        exact congrArg Subtype.val ((mem_center_iff.mp huF.2) ⟨l, hl⟩)
      have hzero := b.model.2.1.twoPerfect.centralizes_of_commuting_fixed L Q Z
        (isPGroup_pCoreIn 2 (localGroup b)) hLN hQN hcomm hfix
      have hz : Z = ⊥ := (firstLayer_commutator_first b).symm.trans hzero
      have hu : U = ⊥ := (map_eq_bot_iff_of_injective U L.subtype_injective).mp hz
      exact False.elim (b.model.2.1.blockU_ne_bot hu)
    · exact he
  have hUN : U ≤ N := by
    rw [← hfull]
    apply commutator_le.mpr
    intro u hu l _
    rw [← hNF] at hu
    obtain ⟨n, hn, f, hf, rfl⟩ := mem_sup_of_normal_left.mp hu
    have hfcentral : Commute f l := (mem_center_iff.mp hf.2 l).symm
    rw [commutatorElement_mul_left_eq_conj_mul, hfcentral.commutator_eq,
      mul_one, mul_inv_cancel, one_mul]
    exact commutator_le_left N ⊤ (commutator_mem_commutator hn (mem_top l))
  intro z hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact (hUN hu).2

/-- The intrinsic block layer is contained in the literal central omega
layer of the local radical. -/
theorem firstLayer_le_omegaModule : FieldFourCentrality.firstLayer b ≤ omegaModule b := by
  intro z hz
  have he : IsElementaryAbelian 2 (FieldFourCentrality.firstLayer b) :=
    b.model.2.1.elementary.map b.first.subtype
  let _ := he
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨firstLayer_le_core b hz, elemPow_eq_one_of_isElementaryAbelian z hz,
      fun q hq => mem_centralizer_iff.mp (firstLayer_centralizes_core b hz) q hq⟩


/-- Faithfulness of the actual natural quotient module bounds the
centralizer of the block layer inside the first block. -/
theorem firstLayer_centralizer_in_first :
    b.first ⊓ centralizer (FieldFourCentrality.firstLayer b : Set G) ≤
      b.first.pCoreIn 2 := by
  have hintr : centralizer (ChapterC.blockU b.first : Set b.first) ≤
      pCore 2 b.first := by
    obtain ⟨_, _, F, _, _, _, _, ρ, ⟨model⟩, hρ⟩ := b.model
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply model.quotientIso.injective
    rw [map_one]
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (ChapterC.blockFixed b.first)
      (model.moduleIso.symm (Multiplicative.ofAdd v))
    have hu' : model.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed b.first) u) =
        Multiplicative.ofAdd v := by rw [hu, model.moduleIso.apply_symm_apply]
    have hconj : ChapterC.blockConjugate b.first x u = u := by
      apply Subtype.ext
      change x * (u : b.first) * x⁻¹ = (u : b.first)
      rw [← mem_centralizer_iff.mp hx u u.property, mul_inv_cancel_right]
    have hm := model.intertwining x u
    rw [hconj, hu'] at hm
    have hv := congrArg Multiplicative.toAdd hm.symm
    rw [hρ] at hv
    rw [map_one]
    exact hv
  intro x hx
  refine ⟨⟨x, hx.1⟩, hintr ?_, rfl⟩
  apply mem_centralizer_iff.mpr
  intro u hu
  exact Subtype.ext (mem_centralizer_iff.mp hx.2 u
    (mem_map_of_mem b.first.subtype hu))

/-- Since the local group has a two-group quotient by its normal first
block, the normal centralizer of that block's layer is a two-group. -/
theorem firstLayer_centralizer_in_localGroup :
    localGroup b ⊓ centralizer (FieldFourCentrality.firstLayer b : Set G) ≤
      blockRadicalCore b := by
  let D := localGroup b
  let L := b.first.subgroupOf D
  let C := (centralizer (FieldFourCentrality.firstLayer b : Set G)).subgroupOf D
  let R := (contraryCore c).subgroupOf D
  let _ : L.Normal := normal_subgroupOf_of_le_normalizer (localGroup_normalizes_first b)
  let _ : C.Normal := normal_subgroupOf_of_le_normalizer
    ((localGroup_normalizes_firstLayer b).trans
      (normalizer_le_normalizer_centralizer (FieldFourCentrality.firstLayer b)))
  have hgen : R ⊔ L = ⊤ := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show contraryCore c ≤ D from le_sup_right),
      map_subgroupOf_eq_of_le (show b.first ≤ D from le_sup_left),
      ← MonoidHom.range_eq_map, range_subtype]
    exact sup_comm _ _
  have hquot : IsPGroup 2 (D ⧸ L) :=
    quotient_isPGroup_of_sup_eq_top R L (isPGroup_pCoreIn 2 _).comap_subtype hgen
  have hC : IsPGroup 2 C := by
    intro x
    obtain ⟨n, hn⟩ := hquot (QuotientGroup.mk' L (x : D))
    have hxL : (x : D) ^ (2 ^ n) ∈ L := by
      apply (QuotientGroup.eq_one_iff ((x : D) ^ (2 ^ n))).mp
      change (QuotientGroup.mk' L) ((x : D) ^ (2 ^ n)) = 1
      rwa [map_pow]
    have hxcore : ((x : D) : G) ^ (2 ^ n) ∈ b.first.pCoreIn 2 :=
      firstLayer_centralizer_in_first b
        ⟨hxL, (centralizer (FieldFourCentrality.firstLayer b : Set G)).pow_mem
          x.property (2 ^ n)⟩
    obtain ⟨m, hm⟩ := isPGroup_pCoreIn 2 b.first
      ⟨((x : D) : G) ^ (2 ^ n), hxcore⟩
    refine ⟨n + m, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hm' := congrArg (fun y : b.first.pCoreIn 2 => (y : G)) hm
    simpa only [coe_pow, coe_one, pow_mul, pow_add] using hm'
  have hCC : C ≤ pCore 2 D := le_sSup ⟨inferInstance, hC⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hCC hx.2, rfl⟩

/-- The literal conjugation action on Ω₁(Z(Q)) has kernel Q. -/
theorem action_kernel_eq_core :
    (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b) := by
  apply le_antisymm _ (core_le_action_ker b)
  rw [action_ker]
  intro x hx
  exact firstLayer_centralizer_in_localGroup b
    ⟨x.property, centralizer_le (firstLayer_le_omegaModule b) hx⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.ThompsonImage
