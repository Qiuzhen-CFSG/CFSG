module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ThreeSpace

/-!
# The three-step intrinsic flag of a derived G₂ Sylow

Conjugation transports all three spaces together. The fixed-vector and
successive displacement descriptions make the flag intrinsic even under
binary operators which need not initially be field-linear.

Source: Aschbacher--Smith, opening §11.1, printed pp.760--761.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.OrthogonalCover.SylowFlag
open Representation Representation.OneCohomology
variable (F : Type*) [Field F] [CharP F 2]

/-- A flag together with its intrinsic displacement descriptions. -/
structure IntrinsicFlag (Q : Subgroup (D F)) where
  space : Fin 3 → Submodule F (Space F)
  dimension : ∀ i, Module.finrank F (space i) = i.val + 1
  nested : Monotone space
  invariant : ∀ i, ∀ q : Q, space i ≤ (space i).comap (derivedAction F q.val)
  unique : ∀ (i : Fin 3) (W : Submodule F (Space F)), Module.finrank F W = i.val + 1 →
    (∀ q : Q, W ≤ W.comap (derivedAction F q.val)) → W = space i
  first : ∀ x, x ∈ space 0 ↔ ∀ q : Q, derivedAction F q.val x = x
  next : ∀ (i : Fin 2) x, x ∈ space i.succ ↔
    ∀ q : Q, derivedAction F q.val x - x ∈ space i.castSucc

/-- The marked third space transported by the same derived-group element. -/
def movedThreeSpace (g : D F) : Submodule F (Space F) :=
  (naturalThreeSpace F).map (derivedAction F g)

theorem movedThreeSpace_finrank (g : D F) : Module.finrank F (movedThreeSpace F g) = 3 :=
  (Transport.finrank_map _ _ _).trans (naturalThreeSpace_finrank F)

theorem movedThreeSpace_invariant (g : D F) :
    ∀ q : movedSylow F g, movedThreeSpace F g ≤
      (movedThreeSpace F g).comap (derivedAction F q.val) :=
  Transport.invariant_map _ g (U F) (naturalThreeSpace F) (naturalThreeSpace_invariant F)

theorem movedThreeSpace_unique [Finite F] (g : D F) (W : Submodule F (Space F))
    (hW : ∀ q : movedSylow F g, W ≤ W.comap (derivedAction F q.val))
    (hdim : Module.finrank F W = 3) : W = movedThreeSpace F g := by
  have he := invariant_three_unique F (W.comap (derivedAction F g))
    (Transport.invariant_comap _ g (U F) W hW)
    ((Transport.finrank_comap _ _ _).trans hdim)
  have hm := congrArg (Submodule.map (derivedAction F g)) he
  rw [Submodule.map_comap_eq_of_surjective ((derivedAction F).apply_bijective g).surjective] at hm
  exact hm

theorem movedThreeSpace_displacement (g : D F) (x : Space F) :
    (∀ q : movedSylow F g, derivedAction F q.val x - x ∈ movedPlane F g) ↔
      x ∈ movedThreeSpace F g := by
  obtain ⟨y,rfl⟩ := ((derivedAction F).apply_bijective g).surjective x
  rw [movedSylow, movedPlane, Transport.displacement_conjugate, displacement_mem_plane_iff]
  change y ∈ naturalThreeSpace F ↔
    y ∈ ((naturalThreeSpace F).map (derivedAction F g)).comap (derivedAction F g)
  rw [Submodule.comap_map_eq_of_injective ((derivedAction F).apply_bijective g).injective]

/-- One actual conjugating element constructs the entire intrinsic flag. -/
def movedIntrinsicFlag [Finite F] (g : D F) : IntrinsicFlag F (movedSylow F g) where
  space := ![movedLine F g, movedPlane F g, movedThreeSpace F g]
  dimension := by
    intro i
    fin_cases i
    · exact movedLine_finrank F g
    · exact movedPlane_finrank F g
    · exact movedThreeSpace_finrank F g
  nested := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num [Fin.le_def] at hij
    all_goals dsimp
    all_goals first
      | exact le_rfl
      | exact movedLine_le_plane F g
      | exact Submodule.map_mono (naturalPlane_le_naturalThreeSpace F)
      | exact (movedLine_le_plane F g).trans (Submodule.map_mono (naturalPlane_le_naturalThreeSpace F))
  invariant := by
    intro i
    fin_cases i
    · exact movedLine_invariant F g
    · exact movedPlane_invariant F g
    · exact movedThreeSpace_invariant F g
  unique := by
    intro i W hd hW
    fin_cases i
    · exact movedLine_unique F g W hW hd
    · exact movedPlane_unique F g W hW hd
    · exact movedThreeSpace_unique F g W hW hd
  first := by
    intro x
    change x ∈ movedLine F g ↔ _
    rw [← movedLine_fixed]
    rfl
  next := by
    intro i x
    fin_cases i
    · exact (moved_displacement_iff F g x).symm
    · exact (movedThreeSpace_displacement F g x).symm

/-- Every actual Sylow of the derived group has this three-step flag. -/
theorem exists_intrinsicFlag [Finite F] (Q : Sylow 2 (D F)) : Nonempty (IntrinsicFlag F Q) := by
  obtain ⟨g,hg⟩ := exists_marking F Q
  rw [hg]
  exact ⟨movedIntrinsicFlag F g⟩

end Atlas.G2.Natural.OrthogonalCover.SylowFlag
