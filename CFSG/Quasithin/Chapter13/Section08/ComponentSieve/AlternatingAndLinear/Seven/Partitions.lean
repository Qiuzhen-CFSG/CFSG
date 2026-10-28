module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PartitionCore
import Mathlib.Tactic
/-!
# The two seven-point partition stabilizers

The four-plus-three block action is exactly the setwise stabilizer of the
first four points. The second subgroup is defined by preservation of the
partition `{{0,1},{2,3},{4,5},{6}}`, so block permutation is allowed.
The two-core calculation is transported through a faithful group map and
an equality of the actual subgroup images. It never assumes ambient normality.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959 (1 March 2004 manuscript).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open Equiv

/-- The first block, in zero-based coordinates. -/
def fourBlock : Set (Fin 7) := Set.range (fun i : Fin 4 =>
  (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7) (Sum.inl i))

/-- The distinguished block consists precisely of coordinates zero through three. -/
theorem fourBlock_eq : fourBlock = {i | i.val < 4} := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

/-- The product action is the actual partition stabilizer. -/
theorem mem_fourThreeStabilizer_iff (g : S7) :
    g ∈ fourThreeStabilizer ↔ Set.MapsTo g fourBlock fourBlock := by
  let e : Fin 4 ⊕ Fin 3 ≃ Fin 7 := finSumFinEquiv
  constructor
  · rintro ⟨x, rfl⟩ i ⟨j, rfl⟩
    refine ⟨x.1 j, ?_⟩
    change e (Sum.inl (x.1 j)) = e ((Equiv.sumCongr x.1 x.2) (e.symm (e (Sum.inl j))))
    rw [e.symm_apply_apply]
    rfl
  · intro h
    let s : Perm (Fin 4 ⊕ Fin 3) := e.symm.permCongr g
    have hs : Set.MapsTo s (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := h ⟨i, rfl⟩
      refine ⟨k, ?_⟩
      change Sum.inl k = e.symm (g (e (Sum.inl i)))
      rw [← hk]
      exact (e.symm_apply_apply _).symm
    obtain ⟨x, hx⟩ := Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hs
    refine ⟨x, ?_⟩
    apply Equiv.ext
    intro i
    have hi := congrArg e (Equiv.congr_fun hx (e.symm i))
    change e ((sumCongr x.1 x.2) (e.symm i)) = e (e.symm (g (e (e.symm i)))) at hi
    change e ((sumCongr x.1 x.2) (e.symm i)) = g i
    simpa only [e.apply_symm_apply] using hi

open Subgroup
variable {H : Type*} [Group H]

/-- Elements in the intrinsic two-core have even seven-point image. -/
theorem mapped_fourThreeCore_even (φ : H →* S7) (hφ : Function.Injective φ)
    (P : Subgroup H) (hP : P.map φ = fourThreeStabilizer)
    {a : H} (ha : a ∈ (pCore 2 P).map P.subtype) : (φ a).sign = 1 := by
  obtain ⟨b, hb, rfl⟩ := ha
  let e : P ≃* fourThreeStabilizer :=
    (P.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hP)
  have hmem : e b ∈ pCore 2 fourThreeStabilizer := by
    rw [← pCore_map_iso 2 e]
    exact mem_map_of_mem _ hb
  exact fourThreeCore_even (e b) hmem


/-- Labels of the three pairs and the remaining singleton. -/
def pairBlock (i : Fin 7) : Fin 4 := ⟨i.val / 2, by omega⟩

/-- The actual stabilizer of `{{0,1},{2,3},{4,5},{6}}`. -/
def pairStabilizer : Subgroup S7 where
  carrier := {g | ∀ i j, pairBlock (g i) = pairBlock (g j) ↔ pairBlock i = pairBlock j}
  one_mem' := by intro i j; rfl
  mul_mem' := by
    intro g h hg hh i j
    exact (hg (h i) (h j)).trans (hh i j)
  inv_mem' := by
    intro g hg i j
    simpa using (hg (g⁻¹ i) (g⁻¹ j)).symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
