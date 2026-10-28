module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerSylow
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerCentralizer
public import Theory.GroupTheory.SpecificGroups.DihedralEightProductElementary
public import Theory.ElementaryAbelian.Quotient

/-!
# The Sylow overgroup normalizes both exceptional endpoint cores

Each A_i is an elementary sixteen-group inside Tf ≤ R. In the proved
D8 × D8 model every such subgroup is normal, so the original R normalizes
both actual cores. In particular R lies in the final plane normalizer H.
Its order sixty-four prevents containment in either endpoint, and its
intersection with either endpoint centralizer is exactly the common Tf.

Source: Aschbacher--Smith F.5.4(2--3), printed p.301. The relative subgroup
maps are retained; the earlier FusionFacts producer is the only local input.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G)
  (hf : FusionFacts c i z t)
include hf

omit [Finite G] in
theorem normalizer_A_le_Rimage (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) (b : Bool) : A c i b ≤ Rimage c i R :=
  (normalizer_A_le_TfImage c i z t hf b).trans (normalizer_TfImage_le_Rimage c i R hR)

theorem normalizer_R_normalizes_A (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) (b : Bool) :
    Rimage c i R ≤ normalizer (A c i b : Set G) := by
  obtain ⟨e⟩ := normalizer_R_iso c i z t hf R
  let B := (A c i b).subgroupOf (Rimage c i R)
  have hAR := normalizer_A_le_Rimage c i z t hf R hR b
  let := hf.A_elementary b
  have hB : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hAR).symm.toMonoidHom
      (subgroupOfEquivOfLe hAR).symm.surjective
  have hcard : Nat.card (B.map e.toMonoidHom) = 16 := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv,hf.A_card]
  have hnormal : B.Normal := MulEquiv.normal_map_iff.mp
    (DihedralGroup.product_elementary_sixteen_normal _ (hB.map _) hcard)
  exact (normal_subgroupOf_iff_le_normalizer hAR).mp hnormal

theorem normalizer_R_le_H (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) : Rimage c i R ≤ H c i :=
  normalizer_R_normalizes_A c i z t hf R hR true

theorem normalizer_R_not_le_M (R : Sylow 2 (C c i)) (b : Bool) :
    ¬ Rimage c i R ≤ M c i b := by
  intro hR
  have hRE : Rimage c i R ≤ E c i b := le_inf hR (Rimage_le_C c i R)
  have hd := card_dvd_of_le hRE
  obtain ⟨e⟩ := hf.E_iso b
  rw [normalizer_R_card c i z t hf,Nat.card_congr e.toEquiv] at hd
  norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hd

omit [Finite G] in
theorem normalizer_E_card (b : Bool) : Nat.card (E c i b) = 96 := by
  obtain ⟨e⟩ := hf.E_iso b
  rw [Nat.card_congr e.toEquiv]
  norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

theorem normalizer_R_inf_E (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) (b : Bool) :
    Rimage c i R ⊓ E c i b = TfImage c i := by
  have hle : TfImage c i ≤ Rimage c i R ⊓ E c i b :=
    le_inf (normalizer_TfImage_le_Rimage c i R hR) (TfImage_le_E c i b)
  have hdivR := card_dvd_of_le (show Rimage c i R ⊓ E c i b ≤ Rimage c i R from inf_le_left)
  have hdivE := card_dvd_of_le (show Rimage c i R ⊓ E c i b ≤ E c i b from inf_le_right)
  rw [normalizer_R_card c i z t hf] at hdivR
  rw [normalizer_E_card c i z t hf] at hdivE
  have hcard : Nat.card (Rimage c i R ⊓ E c i b : Subgroup G) ≤ 32 :=
    Nat.le_of_dvd (by decide) (show Nat.card (Rimage c i R ⊓ E c i b : Subgroup G) ∣ 32 from
      Nat.dvd_gcd hdivR hdivE)
  exact (eq_of_le_of_card_ge hle (by rw [normalizer_TfImage_card c i z t hf];exact hcard)).symm

theorem normalizer_R_inf_M (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) (b : Bool) :
    Rimage c i R ⊓ M c i b = TfImage c i := by
  rw [←normalizer_R_inf_E c i z t hf R hR b,E,←inf_assoc,
    inf_eq_left.mpr (inf_le_left.trans (Rimage_le_C c i R))]

/-- The original exceptional hypothesis selects the strict Sylow overgroup
and supplies the proved first-stage normalizer conclusions simultaneously. -/
theorem source_normalizer_sylow_setup (hex : Source.Exceptional c i) :
    ∃ R : Sylow 2 (C c i), Tf c i < (R : Subgroup (C c i)) ∧
      Nonempty (Rimage c i R ≃* DihedralGroup 4 × DihedralGroup 4) ∧
      ∀ b, centralizer (A c i b : Set G) = A c i b ∧
        Rimage c i R ≤ normalizer (A c i b : Set G) ∧
        Rimage c i R ⊓ M c i b = TfImage c i ∧
        ¬ Rimage c i R ≤ M c i b := by
  obtain ⟨S,hS⟩ := hf.sylow
  have hT : IsPGroup 2 (Source.sylowImage c i) := hS ▸ S.isPGroup'
  obtain ⟨R,hR⟩ := exists_strict_sylow c i hT hex
  exact ⟨R,hR,normalizer_R_iso c i z t hf R,fun b =>
    ⟨A_self_centralizer c i z t hf b,
      normalizer_R_normalizes_A c i z t hf R hR.le b,
      normalizer_R_inf_M c i z t hf R hR.le b,
      normalizer_R_not_le_M c i z t hf R b⟩⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
