module

public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.SylowNormalIntersection
public import GorensteinWalter.Defs

/-!
# Recovering the original maximal overgroup from an involution centralizer

A normal even subgroup K contains an involution in the center of the
prescribed Sylow two-subgroup T. If its centralizer in K is maximal and
H = KT, uniqueness of the maximal overgroup M of T forces M = C_H(t).
The proof retains the actual subgroup, element and intersection M ∩ K.

Source application: the odd PSL₂ branch of Aschbacher–Smith E.2.2,
printed pp.215–216. The intrinsic model maximality is proved separately.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

/-- The normal subgroup supplies a marked central Sylow involution. -/
theorem normal_even_subgroup_central_sylow_involution (T : Sylow 2 H)
    (K : Subgroup H) [K.Normal] (heven : 2 ∣ Nat.card K) :
    ∃ t : K, GorensteinWalter.IsInvolution t ∧ (t : H) ∈ (T : Subgroup H) ∧
      (T : Subgroup H) ≤ centralizer ({(t : H)} : Set H) := by
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_eq_of_normal K
  have hPne : (P : Subgroup K) ≠ ⊥ := P.ne_bot_of_dvd_card heven
  let KT := K.subgroupOf (T : Subgroup H)
  have hKT : KT ≠ ⊥ := by
    intro he
    apply hPne
    apply le_bot_iff.mp
    intro x hx
    have hxT : (x : H) ∈ (T : Subgroup H) := by
      have hh : x ∈ (T : Subgroup H).subgroupOf K := hP ▸ hx
      exact hh
    have hh : (⟨x, hxT⟩ : T) ∈ KT := x.property
    rw [he, mem_bot] at hh
    exact mem_bot.mpr (Subtype.ext (show (x : H) = 1 from congrArg (fun y : T => (y : H)) hh))
  let : Nontrivial KT := (nontrivial_iff_ne_bot KT).mpr hKT
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨Z, _, hZK, hZcard, hZcent⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal KT (p := 2) inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZcard])
  let t : K := ⟨z.val.val, hZK z.property⟩
  have htorder : orderOf t = 2 := by
    rw [← orderOf_injective K.subtype K.subtype_injective t]
    change orderOf ((z.val : T) : H) = 2
    exact (orderOf_injective (T : Subgroup H).subtype Subtype.val_injective z.val).trans
      ((orderOf_injective Z.subtype Z.subtype_injective z).trans hz)
  refine ⟨t, (orderOf_eq_prime_iff.mp htorder).symm, z.val.property, ?_⟩
  intro a ha
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mem_center_iff.mp (hZcent z.property) (⟨a, ha⟩ : T))

/-- An intrinsic maximal involution centralizer identifies the original maximal overgroup. -/
theorem minimalParabolic_max_eq_involution_centralizer
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (t : K) (hmax : IsCoatom (centralizer ({t} : Set K)))
    (hfix : (T : Subgroup H) ≤ centralizer ({(t : H)} : Set H)) :
    ChapterB.minimalParabolicMax T hP = centralizer ({(t : H)} : Set H) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K = centralizer ({t} : Set K) := by
  let M := ChapterB.minimalParabolicMax T hP
  let C := centralizer ({(t : H)} : Set H)
  have hCne : C ≠ ⊤ := by
    intro he
    apply hmax.ne_top
    apply top_unique
    intro k _
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (show (k : H) ∈ C by rw [he]; trivial)
  have hCM : C ≤ M := hP.1.le_maximal
    ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩ hfix
    (lt_top_iff_ne_top.mpr hCne)
  have hMKne : M.subgroupOf K ≠ ⊤ := by
    intro he
    have hKM : K ≤ M := by
      intro k hk
      exact show (⟨k, hk⟩ : K) ∈ M.subgroupOf K from he ▸ mem_top _
    have hh := sup_le hKM (ChapterB.minimalParabolicMax_spec T hP).2
    rw [hgen] at hh
    exact (ChapterB.minimalParabolicMax_spec T hP).1.ne_top (top_unique hh)
  have hKM : centralizer ({t} : Set K) ≤ M.subgroupOf K := by
    intro k hk
    apply hCM
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hk)
  have heK : M.subgroupOf K = centralizer ({t} : Set K) :=
    (hmax.le_iff_eq hMKne).mp hKM
  refine ⟨le_antisymm ?_ hCM, heK⟩
  intro m hm
  have hh : m ∈ K ⊔ (T : Subgroup H) := hgen ▸ mem_top _
  obtain ⟨k, hk, a, ha, rfl⟩ := mem_sup_of_normal_left.mp hh
  have hkM : k ∈ M := by
    have h := M.mul_mem hm (M.inv_mem ((ChapterB.minimalParabolicMax_spec T hP).2 ha))
    simpa only [mul_inv_cancel_right] using h
  have hkC : k ∈ C := by
    have h : (⟨k, hk⟩ : K) ∈ centralizer ({t} : Set K) := heK ▸ hkM
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp h))
  exact C.mul_mem hkC (hfix ha)

end CFSG.Quasithin.ChapterE.Structure
