module
public import Theory.GroupTheory.SmallMoverFamily
public import Glauberman.ThompsonPair
public import Glauberman.BaumannNormalizer

/-!
# Baumann control from a maximum small mover

A maximum small mover is the centralizer in T of its full fixed subgroup
on U: any larger centralizer would still satisfy the small-mover bounds.
If the ordinary Thompson subgroup lies in that mover, the fixed subgroup
lies in its central omega, so the Baumann subgroup lies in the mover too.
Injective maps preserve these literal Thompson, central-omega and Baumann
subgroups, including maps into an infinite amalgam.

Source application: Meierfrankenfeld--Stellmacher (1993), (5.1), printed
p.913. `NonbinarySymplectic.CriticalReduction.RootProductBaumann` supplies
the actual replacement edge and the Thompson containment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

/-- A maximum small mover is the full centralizer, inside T, of its fixed
subgroup on U. A larger centralizer would itself be an admissible mover. -/
theorem maximum_smallMover_fixed_centralizer
    (U Q T M : Subgroup G) (k : ℕ) (hM : M ∈ Subgroup.SmallMover.Maximal U Q T k) :
    T ⊓ centralizer ((U ⊓ centralizer (M : Set G) : Subgroup G) : Set G) = M := by
  let C := U ⊓ centralizer (M : Set G)
  let B := T ⊓ centralizer (C : Set G)
  have hMB : M ≤ B := by
    intro m hm
    exact ⟨hM.1.1 hm,fun c hc => (hc.2 m hm).symm⟩
  have hC : C ≤ U ⊓ centralizer (B : Set G) := by
    intro c hc
    exact ⟨hc.1,fun b hb => (hb.2 c hc).symm⟩
  have hi : (centralizer (B : Set G)).relIndex U ≤ (centralizer (M : Set G)).relIndex U := by
    rw [←inf_relIndex_left U (centralizer (B : Set G)),
      ←inf_relIndex_left U (centralizer (M : Set G))]
    exact relIndex_le_of_le_left hC index_ne_zero_of_finite
  have hs : Subgroup.SmallMover.Admissible U Q T k B :=
    ⟨inf_le_left,hi.trans (hM.1.2.1.trans
      (relIndex_le_of_le_right hMB index_ne_zero_of_finite)),hi.trans hM.1.2.2⟩
  exact (eq_of_le_of_card_ge hMB (hM.2 B hs)).symm

/-- If all maximum abelian subgroups lie in M, its full fixed subgroup
on an elementary layer lies in the actual central omega of J(T). -/
theorem smallMover_fixed_le_thompson_omega
    (U T M : Subgroup G) [IsElementaryAbelian 2 U]
    (hUT : U ≤ T) (hJM : thompsonSubgroup T ≤ M) :
    U ⊓ centralizer (M : Set G) ≤ omegaCenterIn (thompsonSubgroup T) := by
  obtain ⟨A,hA⟩ := thompsonAbelianSubgroups_nonempty T
  have hCA : U ⊓ centralizer (M : Set G) ≤ A :=
    le_maximum_abelian_of_centralizes hA (inf_le_left.trans hUT)
      (inf_le_right.trans (centralizer_le ((le_sSup hA).trans hJM)))
  intro x hx
  apply (mem_omegaCenterIn_iff _ _).mpr
  exact ⟨le_sSup hA (hCA hx),centralizer_le hJM hx.2,
    elemPow_eq_one_of_isElementaryAbelian x hx.1⟩

/-- The source Baumann subgroup lies in a maximum small mover whenever
the whole ordinary Thompson subgroup does. No quotient kernel is removed. -/
theorem baumann_le_maximum_smallMover
    (U Q T M : Subgroup G) [IsElementaryAbelian 2 U] (k : ℕ)
    (hUT : U ≤ T) (hJM : thompsonSubgroup T ≤ M)
    (hM : M ∈ Subgroup.SmallMover.Maximal U Q T k) : baumannSubgroup T ≤ M := by
  have hC := smallMover_fixed_le_thompson_omega U T M hUT hJM
  have hB : baumannSubgroup T ≤
      T ⊓ centralizer ((U ⊓ centralizer (M : Set G) : Subgroup G) : Set G) :=
    inf_le_inf_left T (centralizer_le hC)
  exact hB.trans_eq (maximum_smallMover_fixed_centralizer U Q T M k hM)
end Glauberman

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G D : Type*} [Group G] [Group D]

/-- The all-abelian Thompson subgroup follows the actual injective map,
even when the target ambient group is infinite. -/
theorem thompson_map_injective (T : Subgroup G) (i : G →* D) (hi : Function.Injective i) :
    (thompsonSubgroup T).map i = thompsonSubgroup (T.map i) := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    apply sSup_le
    intro A hA
    exact map_le_iff_le_comap.mp (le_sSup (maximum_abelian_map_of_injective i hi hA))
  · apply sSup_le
    intro A hA
    have hAi : A ≤ i.range := hA.1.trans (map_le_range i T)
    have hAm : (A.comap i).map i = A := map_comap_eq_self hAi
    have hAc : A.comap i ∈ thompsonAbelianSubgroups T :=
      (maximum_abelian_map_iff_of_injective i hi).mp (hAm.symm ▸ hA)
    exact hAm.symm.trans_le (map_mono (le_sSup hAc))

/-- Central omega transport retains every fixed central attachment. -/
theorem omegaCenterIn_map_injective (T : Subgroup G) (i : G →* D) (hi : Function.Injective i) :
    (omegaCenterIn T).map i = omegaCenterIn (T.map i) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨hyT,hyC,hy2⟩ := (mem_omegaCenterIn_iff _ _).mp hy
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨mem_map_of_mem i hyT,?_,by rw [←map_pow,hy2,map_one]⟩
    rintro _ ⟨t,ht,rfl⟩
    simpa only [map_mul] using congrArg i (hyC t ht)
  · intro hx
    obtain ⟨hxT,hxC,hx2⟩ := (mem_omegaCenterIn_iff _ _).mp hx
    obtain ⟨y,hy,rfl⟩ := hxT
    refine ⟨y,(mem_omegaCenterIn_iff _ _).mpr ⟨hy,?_,?_⟩,rfl⟩
    · intro t ht
      apply hi
      simpa only [map_mul] using hxC (i t) (mem_map_of_mem i ht)
    · apply hi
      simpa only [map_pow,map_one] using hx2

/-- The ordinary Thompson subgroup centralizes its own central omega. -/
theorem thompson_le_baumann (T : Subgroup G) : thompsonSubgroup T ≤ baumannSubgroup T := by
  intro x hx
  refine ⟨thompsonSubgroup_le T hx,?_⟩
  intro z hz
  exact (((mem_omegaCenterIn_iff _ _).mp hz).2.1 x hx).symm

/-- The literal Baumann subgroup also commutes with the edge embedding. -/
theorem baumann_map_injective (T : Subgroup G) (i : G →* D) (hi : Function.Injective i) :
    (baumannSubgroup T).map i = baumannSubgroup (T.map i) := by
  unfold baumannSubgroup
  rw [←map_inf_centralizer_of_injective i hi,omegaCenterIn_map_injective _ i hi,
    thompson_map_injective T i hi]
end Glauberman
