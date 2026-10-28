module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Models

public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Marked coefficient planes and their stabilizers

We use the actual setwise stabilizer in the given representation. A cubic
that cycles two vectors naturally stabilizes their binary span, and a nonzero
such orbit has dimension two. These small linear facts supply the line marking
in the block alternatives of Aschbacher--Smith 15.3.31, printed p.1132.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- The existing actual subspace stabilizer, in the coefficient notation. -/
abbrev planeStabilizer (ρ : Representation (ZMod 2) A V) (W : Submodule (ZMod 2) V) :=
  Representation.BinaryOffender.subspaceStabilizer ρ W

/-- Stabilizer membership can be checked on the actual image subspace. -/
theorem mem_planeStabilizer_iff_map (ρ : Representation (ZMod 2) A V)
    (W : Submodule (ZMod 2) V) (g : A) :
    g ∈ planeStabilizer ρ W ↔ W.map (ρ g) = W := by
  constructor
  · intro h
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact (h v).mpr hv
    · intro v hv
      obtain ⟨w,rfl⟩ := (ρ.apply_bijective g).surjective v
      exact ⟨w,(h w).mp hv,rfl⟩
  · intro h v
    constructor
    · intro hv
      obtain ⟨w,hw,he⟩ := h.symm ▸ hv
      exact (ρ.apply_bijective g).injective he ▸ hw
    · intro hv
      exact h ▸ Submodule.mem_map_of_mem hv

/-- A cubic preserving a subspace in one direction stabilizes it setwise. -/
theorem mem_planeStabilizer_of_cube (ρ : Representation (ZMod 2) A V)
    (W : Submodule (ZMod 2) V) (g : A) (hg : g ^ 3 = 1)
    (h : ∀ v ∈ W, ρ g v ∈ W) : g ∈ planeStabilizer ρ W := by
  have hcube (v : V) : ρ g (ρ g (ρ g v)) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    rw [show g*g*g = g^3 by simp [pow_succ], hg, map_one]
    rfl
  intro v
  exact ⟨fun hv => hcube v ▸ h _ (h _ hv), h v⟩

/-- The standard two-generator presentation of the marked plane. -/
def pairPlane (u v : V) : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {u,v}

/-- The natural order-three action on a binary plane stabilizes that plane. -/
theorem mem_planeStabilizer_of_pair_cycle (ρ : Representation (ZMod 2) A V)
    (g : A) (hg : g ^ 3 = 1) (u v : V)
    (hu : ρ g u = v) (hv : ρ g v = u + v) :
    g ∈ planeStabilizer ρ (pairPlane u v) := by
  apply mem_planeStabilizer_of_cube ρ _ g hg
  have hh : pairPlane u v ≤ (pairPlane u v).comap (ρ g) := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · change ρ g x ∈ pairPlane u v
      rw [hx, hu]
      exact Submodule.subset_span (by simp)
    · change ρ g x ∈ pairPlane u v
      rw [Set.mem_singleton_iff.mp hx, hv]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  exact fun w hw => hh hw

/-- A nonzero natural cubic orbit spans an actual plane. -/
theorem pairPlane_finrank_of_cycle (ρ : Representation (ZMod 2) A V)
    (g : A) (u v : V) (hu : ρ g u = v) (hv : ρ g v = u + v)
    (hu0 : u ≠ 0) : Module.finrank (ZMod 2) (pairPlane u v) = 2 := by
  have hv0 : v ≠ 0 := by
    intro h
    apply hu0
    exact (ρ.apply_bijective g).injective (by rw [hu, h, map_zero])
  have huv : v ≠ u := by
    intro h
    rw [h, hu, h] at hv
    apply hu0
    have htwo : u + u = (0 : V) := by
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact hv.trans htwo
  have hi : LinearIndependent (ZMod 2) ![u,v] := by
    apply linearIndependent_fin2.mpr
    change v ≠ 0 ∧ ∀ a : ZMod 2, a • v ≠ u
    refine ⟨hv0, ?_⟩
    intro a
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    rcases hb a with rfl | rfl
    · simpa only [zero_smul] using hu0.symm
    · simpa only [one_smul] using huv
  have hr : Set.range ![u,v] = ({u,v} : Set V) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have he := finrank_span_eq_card hi
  rw [hr] at he
  exact he

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
