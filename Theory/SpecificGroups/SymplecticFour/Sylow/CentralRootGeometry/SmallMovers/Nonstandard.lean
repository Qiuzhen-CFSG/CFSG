module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Fixed
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.PlaneFamily

/-!
# Saturation of small movers outside the standard plane radical

The fixed-space equations place any small mover outside the standard plane
radical in a finite-parameter plane subgroup. Its moving index is sixteen;
the small-mover inequality and the plane's order force equality with the
whole plane subgroup. An explicit fixed-plane embedding proves the converse
index computation.

This is the nonstandard-plane branch of MS93 (5.4), printed p.915. It applies
to arbitrary subgroups of the Sylow group, including intermediate binary
subgroups; no F4-linearity or elementary hypothesis is imposed.
-/

@[expose] public section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem eq_finitePlane_of_small_not_le_wing (hF : Nat.card F=4)
    (E : Subgroup (unipotent (F := F))) (hmove : movingIndex E ≤ Nat.card E)
    (hE : movingIndex E ≤ 16) (hout : ¬ E ≤ wing true) :
    ∃ l : F, E=finitePlane l := by
  obtain ⟨l,hl⟩ := exists_plane_coordinates_of_not_le_wing hF E hE hout
  have hle : E ≤ finitePlane l := by
    intro g hg
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
    exact (element_mem_finitePlane l b u w v).mpr (hl b u w v hg)
  refine ⟨l,eq_of_le_of_card_ge hle ?_⟩
  rw [card_finitePlane,hF]
  have hh := movingIndex_eq_sixteen_of_not_le_wing hF E hE hout
  norm_num
  simpa only [hh] using hmove

theorem finrank_fixed_ge_two_of_le_finitePlane
    (E : Subgroup (unipotent (F := F))) (l : F) (hE : E ≤ finitePlane l) :
    2 ≤ Module.finrank F (fixed E) := by
  let p : (F × F) →ₗ[F] fixed E :=
    { toFun := fun a => ⟨Sum.elim ![a.1,-l*a.2] ![0,a.2], by
        apply (mem_fixed_iff E _).mpr
        intro b u w v hg
        obtain ⟨rfl,rfl⟩ := (element_mem_finitePlane l b u w v).mp (hE hg)
        simp only [Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one,
          Matrix.cons_val_fin_one,mul_zero,add_zero]
        constructor
        · ring
        · exact ⟨by simp,by simp⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        funext i
        rcases i with i | i <;> fin_cases i <;> simp [mul_add]
      map_smul' := by
        intro c x
        apply Subtype.ext
        funext i
        rcases i with i | i <;> fin_cases i <;> simp [mul_left_comm] }
  have hp : Function.Injective p := by
    intro x y he
    have hv := congrArg (fun z : fixed E => z.val) he
    exact Prod.ext (congrFun hv (.inl 0)) (congrFun hv (.inr 1))
  simpa using LinearMap.finrank_le_finrank_of_injective hp

theorem finitePlane_not_le_wing (l : F) : ¬ finitePlane l ≤ wing true := by
  intro h
  have hm : element 1 0 l 0 ∈ finitePlane l :=
    (element_mem_finitePlane l 1 0 l 0).mpr ⟨rfl,by simp⟩
  have hh := (element_mem_wing true 1 0 l 0).mp (h hm)
  exact one_ne_zero hh

theorem movingIndex_finitePlane (hF : Nat.card F=4) (l : F) :
    movingIndex (finitePlane l)=16 := by
  have hle := finrank_fixed_le_two_of_not_le_wing (finitePlane l) (finitePlane_not_le_wing l)
  have hge := finrank_fixed_ge_two_of_le_finitePlane (finitePlane l) l le_rfl
  have hfix := le_antisymm hle hge
  have hh := (fixed (finitePlane l)).finrank_quotient_add_finrank
  have hdim : Module.finrank F (Vector (F := F))=4 := by simp [Vector]
  rw [hfix,hdim] at hh
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed (finitePlane l))=2 := by omega
  norm_num [movingIndex,hF,hquot]
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
