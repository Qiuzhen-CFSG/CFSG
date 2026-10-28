module

public import Theory.GroupTheory.Hall.Conjugacy
public import CFSG.Quasithin.Chapter4.Section01.NormalizerUniqueness

/-!
# Transfer from the intrinsic Hall witness to every Hall subgroup

Hall subgroups of the solvable overlap H∩M are conjugate inside that overlap.
Since M normalizes the centralizer of L₀/O₂(L₀), trivial intersection with this
kernel transfers under that conjugacy. Thus faithfulness of the Cartan witness
suffices for the literal arbitrary Hall subgroup in the Chapter 10 contract.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10

private theorem hall_inf_eq_bot_of_conjugacy
    {X : Type*} [Group X] [Finite X] {π : Set Nat.Primes}
    {J C B Y : Subgroup X} (hsolv : Group.IsSolvable J)
    (hJC : J ≤ normalizer (C : Set X)) (hBJ : B ≤ J)
    (hB : IsHallSubgroup π (B.subgroupOf J))
    (hY : IsHallSubgroup π (Y.subgroupOf J)) (hYC : Y ⊓ C = ⊥) :
    B ⊓ C = ⊥ := by
  obtain ⟨j, hj⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hY hB
  have hY' : Y.subgroupOf J ⊓ C.subgroupOf J = ⊥ := by
    apply bot_unique
    intro y hy
    have hh : (y : X) ∈ Y ⊓ C := hy
    rw [hYC, mem_bot] at hh
    exact Subtype.ext hh
  have hjC : j ∈ normalizer (C.subgroupOf J : Set J) :=
    le_normalizer_comap J.subtype (hJC j.property)
  have hC : (C.subgroupOf J).map (MulAut.conj j).toMonoidHom = C.subgroupOf J := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using mem_normalizer_iff_map_conj_eq.mp hjC
  have hB' : B.subgroupOf J ⊓ C.subgroupOf J = ⊥ := by
    rw [hj, ← hC,
      ← map_inf _ _ (MulAut.conj j).toMonoidHom (MulAut.conj j).injective,
      hY', Subgroup.map_bot]
  apply bot_unique
  intro b hb
  have hh : (⟨b, hBJ hb.1⟩ : J) ∈ B.subgroupOf J ⊓ C.subgroupOf J := hb
  rw [hB', mem_bot] at hh
  exact congrArg Subtype.val hh

/-- Faithfulness for one Hall subgroup of a solvable overlap gives faithfulness
for all Hall subgroups, with the same ambient section and subtype map. -/
theorem source_hall_sectionKernel_faithful_of_hall_conjugacy
    {G : Type*} [Group G] [Finite G] {H M X : Subgroup G}
    (hMX : M ≤ normalizer (X : Set G))
    (hsolv : Group.IsSolvable (M.subgroupOf H))
    {π : Set Nat.Primes} {B Y : Subgroup H}
    (hBM : B ≤ M.subgroupOf H)
    (hB : IsHallSubgroup π (B.subgroupOf (M.subgroupOf H)))
    (hY : IsHallSubgroup π (Y.subgroupOf (M.subgroupOf H)))
    (hYC : Y ⊓ (Chapter4.sectionCentralizer X).subgroupOf H = ⊥) :
    B.map H.subtype ⊓ Chapter4.sectionCentralizer X = ⊥ := by
  let C := Chapter4.sectionCentralizer X
  have hNC : normalizer (X : Set G) ≤ normalizer (C : Set G) := by
    have hC : C ≤ normalizer (X : Set G) :=
      ((Chapter4.le_sectionCentralizer_iff C X).mp le_rfl).1
    have hh := Chapter4.sectionCentralizerIn_normalized
      (M := normalizer (X : Set G)) (X := X) le_rfl
    rwa [Chapter4.sectionCentralizerIn, inf_eq_right.mpr hC] at hh
  have hMC : M.subgroupOf H ≤ normalizer (C.subgroupOf H : Set H) :=
    (comap_mono (hMX.trans hNC)).trans (le_normalizer_comap H.subtype)
  have hBC := hall_inf_eq_bot_of_conjugacy hsolv hMC hBM hB hY hYC
  apply bot_unique
  rintro x ⟨hx, hxC⟩
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hx
  have hh : b ∈ B ⊓ C.subgroupOf H := ⟨hb, hxC⟩
  rw [hBC, mem_bot] at hh
  exact congrArg Subtype.val hh

end CFSG.Quasithin.Chapter10
