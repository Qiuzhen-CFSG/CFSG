module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.Center
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-!
# Coordinates for the middle parabolic in GL₄(2)

The coordinate line and hyperplane force block sizes 1,2,1. Nine binary
entries determine the action. Eight explicit involutions are the identity,
six elementary transvections and the swap of the two middle coordinates.
All are constructed as actual linear automorphisms and preserve the flag's
line and hyperplane. The full flag stabilizer has lower middle entry zero.

These coordinates support the middle-node calculation in Aschbacher--Smith
13.8.25, printed p.962 (PDF p.979).
-/

@[expose] public section

namespace BinaryLinear.MiddleParabolic
abbrev V := Fin 4 → ZMod 2
abbrev Params := Fin 9 → ZMod 2

def line : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {Pi.single 0 1}
def plane : Submodule (ZMod 2) V :=
  (LinearMap.proj 2).ker ⊓ (LinearMap.proj 3).ker
def hyperplane : Submodule (ZMod 2) V := (LinearMap.proj 3).ker

theorem mem_line (v : V) : v ∈ line ↔ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp
  · intro hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [hv.1, hv.2.1, hv.2.2]

theorem line_le_plane : line ≤ plane := by
  intro v hv
  exact ⟨(mem_line v).mp hv |>.2.1, (mem_line v).mp hv |>.2.2⟩
theorem plane_le_hyperplane : plane ≤ hyperplane := inf_le_right

def block (p : Params) (v : V) : V :=
  ![v 0 + p 0 * v 1 + p 1 * v 2 + p 2 * v 3,
    p 3 * v 1 + p 4 * v 2 + p 5 * v 3,
    p 6 * v 1 + p 7 * v 2 + p 8 * v 3, v 3]

def coordinates (g : BinaryLinear.GL V) : Params :=
  ![g (Pi.single 1 1) 0, g (Pi.single 2 1) 0, g (Pi.single 3 1) 0,
    g (Pi.single 1 1) 1, g (Pi.single 2 1) 1, g (Pi.single 3 1) 1,
    g (Pi.single 1 1) 2, g (Pi.single 2 1) 2, g (Pi.single 3 1) 2]

private theorem binary (a : ZMod 2) : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

private theorem fixes_e0 {g : BinaryLinear.GL V} (hg : g ∈ parabolic line) :
    g (Pi.single 0 1) = Pi.single 0 1 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    ((hg _).mpr (Submodule.mem_span_singleton_self _))
  rcases binary a with rfl | rfl
  · have hz : g (Pi.single 0 1) = 0 := by simpa using ha.symm
    have := g.map_eq_zero_iff.mp hz
    exact False.elim ((by decide : (Pi.single 0 (1 : ZMod 2) : V) ≠ 0) this)
  · simpa using ha.symm

private theorem fixes_last {g : BinaryLinear.GL V} (hg : g ∈ parabolic hyperplane) (v : V) :
    g v 3 = v 3 := by
  have he : g v 3 = 0 ↔ v 3 = 0 := hg v
  rcases binary (g v 3) with h | h <;> rcases binary (v 3) with h' | h'
  · exact h.trans h'.symm
  · exfalso; simpa [h'] using he.mp h
  · exfalso; simpa [h] using he.mpr h'
  · exact h.trans h'.symm

private theorem expansion (v : V) :
    v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 +
        v 2 • Pi.single 2 1 + v 3 • Pi.single 3 1 := by
  ext i
  fin_cases i <;> simp

theorem apply_eq_block {g : BinaryLinear.GL V} (hg : g ∈ parabolic line ⊓ parabolic hyperplane)
    (v : V) : g v = block (coordinates g) v := by
  have he := congrArg g (expansion v)
  simp only [map_add, map_smul, fixes_e0 hg.1] at he
  ext i
  fin_cases i
  · simpa [block, coordinates, mul_comm] using congrFun he 0
  · simpa [block, coordinates, mul_comm] using congrFun he 1
  · simpa [block, coordinates, mul_comm] using congrFun he 2
  · exact fixes_last hg.2 v

theorem coordinates_injective :
    Function.Injective (fun g : ↥(parabolic line ⊓ parabolic hyperplane) => coordinates g.val) := by
  intro g h he
  apply Subtype.ext
  ext v
  change coordinates g.val = coordinates h.val at he
  rw [apply_eq_block g.property, apply_eq_block h.property, he]
def actorFun (k : Fin 8) (v : V) : V :=
  match k with
  | 0 => v
  | 1 => ![v 0+v 1,v 1,v 2,v 3]
  | 2 => ![v 0+v 2,v 1,v 2,v 3]
  | 3 => ![v 0,v 1+v 3,v 2,v 3]
  | 4 => ![v 0,v 1,v 2+v 3,v 3]
  | 5 => ![v 0,v 1+v 2,v 2,v 3]
  | 6 => ![v 0,v 2,v 1,v 3]
  | 7 => ![v 0,v 1,v 2+v 1,v 3]

private theorem actor_add : ∀ (k : Fin 8) (v w : V),
    actorFun k (v+w) = actorFun k v + actorFun k w := by
  intro k v w
  fin_cases k <;> ext i <;> fin_cases i <;> simp [actorFun] <;> ring

private theorem actor_smul : ∀ (k : Fin 8) (a : ZMod 2) (v : V),
    actorFun k (a • v) = a • actorFun k v := by
  intro k a v
  fin_cases k <;> ext i <;> fin_cases i <;> simp [actorFun, mul_add]

private theorem actor_involution : ∀ (k : Fin 8) (v : V),
    actorFun k (actorFun k v) = v := by decide +kernel

def actor (k : Fin 8) : BinaryLinear.GL V where
  toFun := actorFun k
  invFun := actorFun k
  left_inv := by exact actor_involution k
  right_inv := by exact actor_involution k
  map_add' := by exact actor_add k
  map_smul' := by exact actor_smul k

@[simp] theorem actor_apply (k : Fin 8) (v : V) : actor k v = actorFun k v := rfl
@[simp] theorem actor_inv (k : Fin 8) : (actor k)⁻¹ = actor k := rfl

theorem actor_mem (k : Fin 8) : actor k ∈ parabolic line ⊓ parabolic hyperplane := by
  have ht : ∀ (k : Fin 8) (v : V),
      ((actorFun k v) 1 = 0 ∧ (actorFun k v) 2 = 0 ∧ (actorFun k v) 3 = 0 ↔
        v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0) ∧ ((actorFun k v) 3 = 0 ↔ v 3 = 0) := by
    decide +kernel
  constructor
  · intro v
    rw [mem_line, mem_line]
    exact (ht k v).1
  · intro v
    exact (ht k v).2

private theorem parabolic_of_maps {W : Submodule (ZMod 2) V} {g : BinaryLinear.GL V}
    (h : ∀ v ∈ W, g v ∈ W) : g ∈ parabolic W := by
  let f : W → W := fun v => ⟨g v, h v v.property⟩
  have hf : Function.Injective f := by
    intro u v he
    exact Subtype.ext (g.injective (congrArg Subtype.val he))
  intro v
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨g v, hv⟩
    exact g.injective (congrArg Subtype.val hw) ▸ w.property
  · exact h v

theorem mem_plane_parabolic {g : BinaryLinear.GL V}
    (hg : g ∈ parabolic line ⊓ parabolic hyperplane) :
    g ∈ parabolic plane ↔ coordinates g 6 = 0 := by
  constructor
  · intro h
    have he : Pi.single 1 (1 : ZMod 2) ∈ plane := by constructor <;> simp
    exact ((h _).mpr he).1
  · intro h
    apply parabolic_of_maps
    intro v hv
    change v 2 = 0 ∧ v 3 = 0 at hv
    rw [apply_eq_block hg]
    constructor <;> change _ = 0 <;> simp [block, hv.1, hv.2, h]


end BinaryLinear.MiddleParabolic

end
