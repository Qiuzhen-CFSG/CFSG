module

public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.Frattini.PGroup
/-!
# The special five-root subgroup in even-characteristic G₂

The root multiplication law puts all commutators in the highest-root group;
commutators of the second and fifth root groups realize every highest-root
element. The center calculation identifies this with the whole center. Squares
are central in characteristic two, so the finite two-group Frattini formula
identifies its Frattini subgroup with the same elementary abelian group.
Thus the subgroup is special of order q⁵ and center order q. Identifying this
subgroup with the first local two-core is a separate parabolic calculation.

Source: Aschbacher--Smith, Notation F.1.11 and F.1.12(I)(3), printed pp. 262--263.
-/

@[expose] public section

namespace Atlas.G2.LieParabolicSetup
open Explicit
open scoped commutatorElement
variable {F : Type*} [Field F]

theorem fiveRoot_commutator (t u : Fin 6 → F) (ht : t 5 = 0) (hu : u 5 = 0) :
    ⁅unipotentProduct t, unipotentProduct u⁆ =
      rootA (-(u 1 * t 4) + 3 * u 2 * t 3 + t 1 * u 4 - 3 * t 2 * u 3) := by
  have ha : ∀ a : F, rootA a = unipotentProduct ![a,0,0,0,0,0] := by
    intro a
    simp [unipotentProduct]
  rw [ha, commutatorElement_def, unipotentProduct_inv, unipotentProduct_inv,
    unipotentProduct_mul, unipotentProduct_mul, unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters, unipotentInverseParameters, ht, hu]
  ring

def radicalCentral (a : F) : radical₁ (F := F) := ⟨rootA a, rootA_mem_radical₁ a⟩

theorem radicalCentral_mem_center (a : F) :
    radicalCentral a ∈ Subgroup.center (radical₁ (F := F)) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  obtain ⟨t,_,ht⟩ := g.prop
  change g.val * rootA a = rootA a * g.val
  rw [← ht]
  exact (unipotentProduct_commute_rootA t a).eq

theorem radical₁_commutator_le_center :
    commutator (radical₁ (F := F)) ≤ Subgroup.center (radical₁ (F := F)) := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  obtain ⟨t,ht,he⟩ := x.prop
  obtain ⟨u,hu,hf⟩ := y.prop
  have hc : ⁅x,y⁆ = radicalCentral
      (-(u 1*t 4)+3*u 2*t 3+t 1*u 4-3*t 2*u 3) := by
    apply Subtype.ext
    change ⁅x.val,y.val⁆ = _
    rw [← he, ← hf]
    exact fiveRoot_commutator t u ht hu
  rw [hc]
  exact radicalCentral_mem_center _

theorem radicalCentral_mem_commutator (a : F) :
    radicalCentral a ∈ commutator (radical₁ (F := F)) := by
  let x : radical₁ (F := F) := ⟨unipotentProduct ![0,a,0,0,0,0], ⟨_, rfl, rfl⟩⟩
  let y : radical₁ (F := F) := ⟨unipotentProduct ![0,0,0,0,1,0], ⟨_, rfl, rfl⟩⟩
  have hc : ⁅x,y⁆ = radicalCentral a := by
    apply Subtype.ext
    change ⁅x.val,y.val⁆ = rootA a
    simpa [x,y] using
      fiveRoot_commutator (F := F) ![0,a,0,0,0,0] ![0,0,0,0,1,0] rfl rfl
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

variable [CharP F 2]

theorem radical₁_commutator_eq_center :
    commutator (radical₁ (F := F)) = Subgroup.center (radical₁ (F := F)) := by
  apply le_antisymm radical₁_commutator_le_center
  intro g hg
  have hm : g.val ∈ highestRoot (F := F) := by
    rw [← center_map_eq_highestRoot radical₁ le_rfl (fiveRootSubgroup_le_unipotent _ _)]
    exact ⟨g,hg,rfl⟩
  obtain ⟨a,ha⟩ := hm
  have he : g = radicalCentral a.toAdd := Subtype.ext ha.symm
  rw [he]
  exact radicalCentral_mem_commutator _

theorem fiveRoot_square (t : Fin 6 → F) (ht : t 5 = 0) :
    unipotentProduct t ^ 2 = rootA (-(t 1*t 4)+3*t 2*t 3) := by
  have ha : ∀ a : F, rootA a = unipotentProduct ![a,0,0,0,0,0] := by
    intro a
    simp [unipotentProduct]
  rw [ha, pow_two, unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters, ht, CharTwo.add_self_eq_zero]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem radical₁_square_mem_center (x : radical₁ (F := F)) :
    x ^ 2 ∈ Subgroup.center (radical₁ (F := F)) := by
  obtain ⟨t,ht,he⟩ := x.prop
  have hs : x ^ 2 = radicalCentral (-(t 1*t 4)+3*t 2*t 3) := by
    apply Subtype.ext
    change x.val ^ 2 = _
    rw [← he]
    exact fiveRoot_square _ ht
  rw [hs]
  exact radicalCentral_mem_center _


theorem radical₁_isTwoGroup [Finite F] : IsPGroup 2 (radical₁ (F := F)) := by
  obtain ⟨n,_,hn⟩ := field_card (F := F)
  apply IsPGroup.of_card (n := n * 5)
  rw [card_radical₁, hn, pow_mul]

theorem radical₁_frattini_eq_center [Finite F] :
    frattini (radical₁ (F := F)) = Subgroup.center (radical₁ (F := F)) := by
  let : Fact (IsPGroup 2 (radical₁ (F := F))) := ⟨radical₁_isTwoGroup⟩
  apply le_antisymm
  · rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    apply (Subgroup.closure_le _).mpr
    rintro x (hx | ⟨y,rfl⟩)
    · exact radical₁_commutator_le_center hx
    · exact radical₁_square_mem_center y
  · rw [← radical₁_commutator_eq_center]
    exact commutator_le_frattini_of_isPGroup (p := 2)

theorem radical₁_center_elementary : IsElementaryAbelian 2 (Subgroup.center (radical₁ (F := F))) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    let e := centerEquivHighestRoot (radical₁ (F := F)) le_rfl
      (fiveRootSubgroup_le_unipotent _ _)
    apply e.injective
    rw [map_pow, map_one, pow_two]
    change (e x).toAdd + (e x).toAdd = 0
    exact CharTwo.add_self_eq_zero _

theorem radical₁_commutator_ne_bot [Finite F] : commutator (radical₁ (F := F)) ≠ ⊥ := by
  intro h
  have hc := card_center_radical₁ (F := F)
  rw [← radical₁_commutator_eq_center, h] at hc
  have hb : Nat.card (⊥ : Subgroup (radical₁ (F := F))) = 1 := by simp
  have hq := Finite.one_lt_card (α := F)
  omega

/-- The five-root group is special, with the complete source structure rather
than just the order notation: its nontrivial derived, Frattini, and center
subgroups coincide, and that subgroup is elementary abelian of order q. -/
theorem radical₁_special [Finite F] :
    IsPGroup 2 (radical₁ (F := F)) ∧
    commutator (radical₁ (F := F)) ≠ ⊥ ∧
    commutator (radical₁ (F := F)) = Subgroup.center (radical₁ (F := F)) ∧
    frattini (radical₁ (F := F)) = Subgroup.center (radical₁ (F := F)) ∧
    IsElementaryAbelian 2 (Subgroup.center (radical₁ (F := F))) ∧
    Nat.card (radical₁ (F := F)) = Nat.card F ^ 5 ∧
    Nat.card (Subgroup.center (radical₁ (F := F))) = Nat.card F :=
  ⟨radical₁_isTwoGroup, radical₁_commutator_ne_bot, radical₁_commutator_eq_center,
    radical₁_frattini_eq_center, radical₁_center_elementary, card_radical₁, card_center_radical₁⟩

end Atlas.G2.LieParabolicSetup
