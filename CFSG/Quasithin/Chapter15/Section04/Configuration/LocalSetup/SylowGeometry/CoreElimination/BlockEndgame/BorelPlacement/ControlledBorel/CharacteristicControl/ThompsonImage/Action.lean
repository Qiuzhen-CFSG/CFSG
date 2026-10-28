module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.Setup
public import Stellmacher.MaxElementaryOffender

/-!
# Conjugation on the central omega layer of the block radical

For D = K₁R and Q = O₂(D), construct the literal conjugation action on
V = Ω₁(Z(Q)). Its kernel is C_D(V), and Q lies in that kernel. Maximum
order elementary abelian subgroups of R satisfy the offender cardinal
inequality on V. Weak closure and the supplied characteristic-normalizer
control show that at least one of them is not contained in Q.

The identification C_D(V) = Q and the rank-one recognition of nontrivial
images remain separate results. None is included in the action definition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13,
pp.123–125; B.2.4/10, pp.75–77; C.2.7, pp.145–146, as used in the proof
of 15.4.20, p.1164.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)

namespace ThompsonImage
noncomputable section

abbrev localGroup : Subgroup G := b.first ⊔ contraryCore c

def omegaModule : Subgroup G := omegaOneCenterAmbient (blockRadicalCore b)

theorem localGroup_normalizes_first :
    localGroup b ≤ normalizer (b.first : Set G) :=
  sup_le b.first.le_normalizer b.core_normalizes

theorem localGroup_normalizes_firstLayer :
    localGroup b ≤ normalizer (FieldFourCentrality.firstLayer b : Set G) :=
  (localGroup_normalizes_first b).trans
    (normalizer_le_normalizer_characteristic_image b.first (ChapterC.blockU b.first))

theorem first_core_le_core : b.first.pCoreIn 2 ≤ blockRadicalCore b :=
  pCoreIn_mono_of_normalizes le_sup_left (localGroup_normalizes_first b)

theorem firstLayer_le_core : FieldFourCentrality.firstLayer b ≤ blockRadicalCore b :=
  (map_mono ChapterC.blockU_le_core).trans (first_core_le_core b)

theorem core_ne_bot : blockRadicalCore b ≠ ⊥ := by
  intro he
  have hz : b.first.pCoreIn 2 = ⊥ := bot_unique (he ▸ first_core_le_core b)
  exact b.model.2.1.core_ne_bot
    ((Subgroup.map_eq_bot_iff_of_injective _ b.first.subtype_injective).mp hz)

theorem omegaModule_ne_bot : omegaModule b ≠ ⊥ := by
  let _ : Nontrivial (blockRadicalCore b) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (core_ne_bot b)
  intro he
  exact omega_center_ne_bot (show IsPGroup 2 (blockRadicalCore b) from
    isPGroup_pCoreIn 2 (localGroup b))
    ((Subgroup.map_eq_bot_iff_of_injective _ (blockRadicalCore b).subtype_injective).mp he)

theorem localGroup_normalizes_core :
    localGroup b ≤ normalizer (blockRadicalCore b : Set G) :=
  (localGroup b).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (localGroup b) (pCore 2 (localGroup b)))

theorem localGroup_normalizes_module :
    localGroup b ≤ normalizer (omegaModule b : Set G) := by
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (omegaOneCenterAmbient (blockRadicalCore b)).map (MulAut.conj x).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective]
  have he : (blockRadicalCore b).map (MulAut.conj x).toMonoidHom = blockRadicalCore b :=
    mem_normalizer_iff_map_conj_eq.mp (localGroup_normalizes_core b hx)
  rw [he]
  rfl

def action : localGroup b →* MulAut (omegaModule b) :=
  (omegaModule b).normalizerMonoidHom.comp (inclusion (localGroup_normalizes_module b))

theorem action_apply (x : localGroup b) (v : omegaModule b) :
    ((action b x v : omegaModule b) : G) = (x : G) * (v : G) * (x : G)⁻¹ := rfl

theorem action_ker :
    (action b).ker = (centralizer (omegaModule b : Set G)).subgroupOf (localGroup b) := by
  ext x
  change inclusion (localGroup_normalizes_module b) x ∈
    (omegaModule b).normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

theorem omegaModule_le_core : omegaModule b ≤ blockRadicalCore b := by
  intro v hv
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hv).1

theorem omegaModule_elementary : IsElementaryAbelian 2 (omegaModule b) :=
  omegaOneCenterAmbient_elementaryAbelian _

theorem core_le_action_ker :
    (blockRadicalCore b).subgroupOf (localGroup b) ≤ (action b).ker := by
  rw [action_ker]
  intro x hx
  apply mem_centralizer_iff.mpr
  intro v hv
  exact (((mem_omegaOneCenterAmbient_iff _ _).mp hv).2.2 x hx).symm

theorem coreThompson_not_le_core (hQ : blockRadicalCore b ≤ contraryCore c) :
    ¬ coreThompson c ≤ blockRadicalCore b := by
  intro hJ
  apply first_not_le_M₁ c b
  apply le_trans ?_ ((coreThompson_normalizer_le c).trans c.core_characteristic_control)
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply elementaryAbelianMaxJ_map_eq_of_le (contraryCore c) (MulAut.conj x)
  exact ((map_mono hJ).trans
    (mem_normalizer_iff_map_conj_eq.mp (first_normalizes_blockRadicalCore c b hx)).le).trans hQ

theorem exists_maximum_not_le_core (hQ : blockRadicalCore b ≤ contraryCore c) :
    ∃ A ∈ elementaryAbelianMaxSubgroups (contraryCore c), ¬ A ≤ blockRadicalCore b := by
  by_contra! hn
  exact coreThompson_not_le_core b hQ (sSup_le hn)

def image (A : Subgroup G) : Subgroup (MulAut (omegaModule b)) :=
  (A.subgroupOf (localGroup b)).map (action b)

theorem image_le_range (A : Subgroup G) : image b A ≤ (action b).range :=
  map_le_range _ _

theorem image_core : image b (blockRadicalCore b) = ⊥ :=
  (Subgroup.map_eq_bot_iff _).mpr (core_le_action_ker b)

theorem image_ne_bot_iff_of_kernel
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b))
    {A : Subgroup G} (hA : A ≤ localGroup b) :
    image b A ≠ ⊥ ↔ ¬ A ≤ blockRadicalCore b := by
  simp only [image, ne_eq, Subgroup.map_eq_bot_iff, hker]
  constructor
  · intro h hAQ
    exact h (fun _ hx => hAQ hx)
  · intro h hAQ
    exact h (fun x hx => hAQ (show (⟨x, hA hx⟩ : localGroup b) ∈ A.subgroupOf (localGroup b) from hx))

theorem maximum_subgroupOf {A : Subgroup G}
    (hA : A ∈ elementaryAbelianMaxSubgroups (contraryCore c)) :
    A.subgroupOf (localGroup b) ∈
      elementaryAbelianMaxSubgroups ((contraryCore c).subgroupOf (localGroup b)) := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  refine ⟨fun _ hx => hA.1 hx, IsElementaryAbelian.subgroupOf (hA.1.trans le_sup_right), ?_⟩
  intro B hB hBe
  have hb := hA.2.2 (B.map (localGroup b).subtype)
    ((map_mono hB).trans (by rw [map_subgroupOf_eq_of_le (show contraryCore c ≤ localGroup b from le_sup_right)]))
    (hBe.map (localGroup b).subtype)
  rw [card_map_of_injective (localGroup b).subtype_injective] at hb
  simpa only [Nat.card_congr (subgroupOfEquivOfLe (hA.1.trans (show contraryCore c ≤ localGroup b from le_sup_right))).toEquiv] using hb

theorem maximum_offender_bound (hQ : blockRadicalCore b ≤ contraryCore c)
    {A : Subgroup G} (hA : A ∈ elementaryAbelianMaxSubgroups (contraryCore c)) :
    Nat.card ((omegaModule b).subgroupOf (localGroup b)) ≤
      Nat.card ↥((omegaModule b).subgroupOf (localGroup b) ⊓
        centralizer (A.subgroupOf (localGroup b) : Set (localGroup b))) *
          Nat.card (image b A) := by
  let V := (omegaModule b).subgroupOf (localGroup b)
  let _ : V.Normal := normal_subgroupOf_of_le_normalizer (localGroup_normalizes_module b)
  let _ : IsElementaryAbelian 2 (omegaModule b) := omegaModule_elementary b
  let _ : IsElementaryAbelian 2 V :=
    IsElementaryAbelian.subgroupOf ((omegaModule_le_core b).trans (pCoreIn_le 2 (localGroup b)))
  apply maxElementary_card_le_fixed_mul_image
    ((contraryCore c).subgroupOf (localGroup b)) V (A.subgroupOf (localGroup b))
    (fun _ hv => hQ (omegaModule_le_core b hv)) (maximum_subgroupOf b hA) (action b)
  rw [action_ker]
  ext x
  constructor
  · intro hx
    apply mem_centralizer_iff.mpr
    intro v hv
    exact Subtype.ext (mem_centralizer_iff.mp hx v hv)
  · intro hx
    apply mem_centralizer_iff.mpr
    intro v hv
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx
      ⟨v, (omegaModule_le_core b).trans (pCoreIn_le 2 (localGroup b)) hv⟩ hv)

theorem image_maximum_elementary {A : Subgroup G}
    (hA : A ∈ elementaryAbelianMaxSubgroups (contraryCore c)) :
    IsElementaryAbelian 2 (image b A) := by
  let _ : IsElementaryAbelian 2 (A.subgroupOf (localGroup b)) :=
    (maximum_subgroupOf b hA).2.1
  exact IsElementaryAbelian.map (action b)

theorem image_le_iff_of_kernel
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b))
    {A B : Subgroup G} (hA : A ≤ localGroup b) (hB : B ≤ localGroup b) :
    image b A ≤ image b B ↔ A ≤ B ⊔ blockRadicalCore b := by
  have hQD : blockRadicalCore b ≤ localGroup b := pCoreIn_le 2 _
  rw [image, image, Subgroup.map_le_map_iff, hker,
    ← subgroupOf_sup hB hQD]
  constructor
  · intro h x hx
    exact h (show (⟨x, hA hx⟩ : localGroup b) ∈ A.subgroupOf (localGroup b) from hx)
  · intro h x hx
    exact h hx

/-- The intrinsic commutator layer has its literal ambient realization. -/
theorem first_core_commutator :
    ⁅b.first.pCoreIn 2, b.first⁆ = FieldFourCentrality.firstLayer b := by
  change ⁅(pCore 2 b.first).map b.first.subtype, b.first⁆ =
    (⁅pCore 2 b.first, (⊤ : Subgroup b.first)⁆).map b.first.subtype
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]

/-- The displacement of Q under the block is exactly its defining layer. -/
theorem core_commutator_first :
    ⁅blockRadicalCore b, b.first⁆ = FieldFourCentrality.firstLayer b := by
  have hNQ := first_normalizes_blockRadicalCore c b
  have hNK := (pCoreIn_le 2 (localGroup b)).trans (localGroup_normalizes_first b)
  have hCfirst : ⁅blockRadicalCore b, b.first⁆ ≤ b.first :=
    le_normalizer_iff_commutator_le_right.mp hNK
  have hCQ : ⁅blockRadicalCore b, b.first⁆ ≤ blockRadicalCore b :=
    le_normalizer_iff_commutator_le_left.mp hNQ
  have hCcore : ⁅blockRadicalCore b, b.first⁆ ≤ b.first.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      ((show IsPGroup 2 (blockRadicalCore b) from isPGroup_pCoreIn 2 _).to_le hCQ)
      hCfirst (normalizer_commutator_ge_right _ _)
  apply le_antisymm
  · rw [← commutator_isPPerfect_idempotent b.first (blockRadicalCore b)
      b.model.2.1.twoPerfect (isPGroup_pCoreIn 2 (localGroup b)) hNQ]
    exact (commutator_mono hCcore le_rfl).trans (first_core_commutator b).le
  · rw [← first_core_commutator]
    exact commutator_mono (first_core_le_core b) le_rfl

/-- Kernel equality inside D is equivalent to the required ambient centralizer equality. -/
theorem action_kernel_eq_core_iff :
    (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b) ↔
      localGroup b ⊓ centralizer (omegaModule b : Set G) = blockRadicalCore b := by
  rw [← Subgroup.map_injective (localGroup b).subtype_injective |>.eq_iff,
    action_ker, subgroupOf_map_subtype,
    map_subgroupOf_eq_of_le (show blockRadicalCore b ≤ localGroup b from
      pCoreIn_le 2 (localGroup b)), inf_comm]

end
end ThompsonImage
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
