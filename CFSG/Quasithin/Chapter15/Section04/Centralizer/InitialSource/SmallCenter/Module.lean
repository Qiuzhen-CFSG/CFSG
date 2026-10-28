module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SolvableSource
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Irreducibility of the original module when the central omega subgroup has order two

A nonzero M-invariant subgroup of V(M) meets the center of the original Sylow
subgroup. Elementary abelianness places this intersection in Ω₁(Z(T)); its
order two makes the intersection the entire seed. M-invariance then contains
the original normal closure V(M). Thus V(M) is irreducible without any
pushing-up or model input. Every actual family member moves this whole module,
so the proved source rank formula yields dimension two or four.

Source: Aschbacher--Smith 15.4.7, printed p.1158, and 15.4.12(3), pp.1160--1161.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every nonzero invariant subgroup contains the original central seed and
therefore the entire normal closure. -/
theorem localV_minimal (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hchar : HasCharacteristicTwo M)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (W : Subgroup G) (hWV : W ≤ localV T M)
    (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ ∨ W = localV T M := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  let := localV_elementary T M hTM hchar
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  have hWT := hWV.trans (localV_le_sylow T M hTM hchar)
  let E := W.subgroupOf (T : Subgroup G)
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hWT).mpr (hTM.trans hMW)
  have hE : E ≠ ⊥ := by
    intro he
    have hm := congrArg (Subgroup.map (T : Subgroup G).subtype) he
    rw [map_subgroupOf_eq_of_le hWT,Subgroup.map_bot] at hm
    exact hW hm
  let D := (center (T : Subgroup G) ⊓ E).map (T : Subgroup G).subtype
  have hD : D ≠ ⊥ := by
    intro he
    exact center_inf_ne_bot_of_normal T.isPGroup' E hE
      ((map_eq_bot_iff_of_injective _ (T : Subgroup G).subtype_injective).mp he)
  have hDW : D ≤ W := by
    exact (map_mono inf_le_right).trans_eq (map_subgroupOf_eq_of_le hWT)
  have hDZ : D ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    rintro x ⟨y,hy,rfl⟩
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨y.property,elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := W) y hy.2,?_⟩
    intro t ht
    exact congrArg Subtype.val ((mem_center_iff.mp hy.1) ⟨t,ht⟩)
  have heq : D = omegaOneCenterAmbient (T : Subgroup G) :=
    eq_of_le_of_card_ge hDZ (by
      rw [hZ]
      exact Nat.succ_le_of_lt (D.one_lt_card_iff_ne_bot.mpr hD))
  have hZW : omegaOneCenterAmbient (T : Subgroup G) ≤ W := heq ▸ hDW
  have hWM : W ≤ M := hWV.trans (localV_le (T : Subgroup G) M)
  let : (W.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hWM).mpr hMW
  have hi : internalModule T M ≤ W.subgroupOf M := normalClosure_le_normal (by
    intro z hz
    exact hZW hz)
  exact le_antisymm hWV ((map_mono hi).trans_eq (map_subgroupOf_eq_of_le hWM))

/-- The original moved module of any specified family member is the whole V(M). -/
theorem member_moved_eq {κ : GroupClass} {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input κ T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    ⁅localV T M,X⁆ = localV T M := by
  have hc := h.ambient.evenCharacteristic T M h.maximal h.sylow_le
  rcases localV_minimal T M h.sylow_le hc hZ (movedModule T M X)
    h.moved_le h.moved_normalized with he | he
  · have hr := h.moved_rank
    change Group.rank (movedModule T M X) = 2*s at hr
    rw [he] at hr
    have hb : Group.rank (⊥ : Subgroup G) = 0 := Group.rank_eq_zero _
    rw [hb] at hr
    rcases h.parameter with hs | hs <;> omega
  · exact he

/-- The actual local module has precisely the source one- or two-plane dimension. -/
theorem member_rank {κ : GroupClass} {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input κ T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    Group.rank (localV T M) = 2*s := by
  rw [←member_moved_eq h hZ]
  exact h.moved_rank

/-- A family member has no nontrivial fixed summand in the original module. -/
theorem member_fixed_eq_bot {κ : GroupClass} {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input κ T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    localV T M ⊓ centralizer (X : Set G) = ⊥ := by
  have hnX := (normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal
  have hn : M ≤ normalizer (localV T M ⊓ centralizer (X : Set G) : Set G) :=
    (le_inf (localV_normalized (T : Subgroup G) M)
      (hnX.trans (normalizer_le_normalizer_centralizer X))).trans
      inf_normalizer_le_normalizer_inf
  rcases localV_minimal T M h.sylow_le
    (h.ambient.evenCharacteristic T M h.maximal h.sylow_le) hZ _ inf_le_left hn with he | he
  · exact he
  · have hz : ⁅localV T M,X⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (he.symm.le.trans inf_le_right)
    have hr := h.moved_rank
    rw [hz,Group.rank_eq_zero] at hr
    rcases h.parameter with hs | hs <;> omega

/-- Every member in the same original maximal local has the same factor count. -/
theorem member_parameter_eq {κ : GroupClass} {T : Sylow 2 G} {M X Y : Subgroup G} {s t : ℕ}
    (hX : Input κ T M X s) (hY : Input κ T M Y t)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) : s = t := by
  have hx := member_rank hX hZ
  have hy := member_rank hY hZ
  omega

/-- In the original empty-family setup every maximal local has a module of
rank two or four, with no characteristic-pair premise. -/
theorem source_local_ranks
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    ∀ M ∈ maximalLocals T, Group.rank (localV T M) = 2 ∨ Group.rank (localV T M) = 4 := by
  obtain ⟨_,hex,_⟩ := SolvableSource.source_family_data hA hC h311 h29 hB hG T hempty hmany
  intro M hM
  obtain ⟨X,s,hs⟩ := hex M hM
  have hr := member_rank hs hZ
  rcases hs.parameter with he | he
  · exact Or.inl (by simpa only [he,mul_one] using hr)
  · exact Or.inr (by simpa only [he] using hr)

end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
