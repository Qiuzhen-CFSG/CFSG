module
public import Theory.AtlasPort.OtherSporadic.GroupTheory.RankThreePrimitivity
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

/-!
# Three stabilizer suborbits

A fixed point and two complementary orbits give an explicit orbit-quotient
coordinate in Fin 3. The subdegrees 1,1755,2304 imply primitivity by block
size divisibility. This is the action-theoretic opening of Aschbacher–Smith
J.5.4–5, printed pp.445–446, independent of any group recognition.
-/

@[expose] public section
noncomputable section
namespace MulAction.ThreeSuborbits
open MulAction
attribute [local instance] Classical.propDecidable
variable {K Ω : Type*} [Group K] [MulAction K Ω]
variable (a b c : Ω)

def family (x : Ω) : Fin 3 := if x=a then 0 else if x∈orbit K b then 1 else 2


@[simp] theorem family_zero (x : Ω) : family (K:=K) a b x=0 ↔ x=a := by
  classical
  simp only [family]
  split_ifs <;> simp_all

@[simp] theorem family_one (hab : a∉orbit K b) (x : Ω) : family (K:=K) a b x=1 ↔ x∈orbit K b := by
  classical
  by_cases hx:x=a
  · subst x; simp [family,hab]
  · simp [family,hx]

@[simp] theorem family_two (hcover : orbit K c=(({a}:Set Ω)∪orbit K b)ᶜ) (x : Ω) : family (K:=K) a b x=2 ↔ x∈orbit K c := by
  classical
  rw [hcover]
  simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_singleton_iff]
  by_cases hx:x=a <;> by_cases hb:x∈orbit K b <;> simp [family,hx,hb]

theorem transitive (hab : a∉orbit K b)
    (hcover : orbit K c=(({a}:Set Ω)∪orbit K b)ᶜ) {x y : Ω} (h : family (K:=K) a b x=family (K:=K) a b y) :
    ∃k:K,k•x=y := by
  classical
  by_cases hx:x=a
  · have hy:y=a:=(family_zero a b y).mp (h.symm.trans ((family_zero a b x).mpr hx))
    subst x; subst y; exact ⟨1,one_smul _ _⟩
  by_cases hb:x∈orbit K b
  · have hy:y∈orbit K b:=(family_one a b hab y).mp
      (h.symm.trans ((family_one a b hab x).mpr hb))
    rw [← orbit_eq_iff] at hb hy
    exact mem_orbit_iff.mp ((orbit_eq_iff.mp (hy.trans hb.symm)))
  · have hc:x∈orbit K c:=by rw [hcover]; exact fun h=>h.elim hx hb
    have hy:y∈orbit K c:=(family_two a b c hcover y).mp
      (h.symm.trans ((family_two a b c hcover x).mpr hc))
    rw [← orbit_eq_iff] at hc hy
    exact mem_orbit_iff.mp (orbit_eq_iff.mp (hy.trans hc.symm))

theorem invariant (hfix : ∀k:K,k•a=a) (k:K) (x:Ω) : family (K:=K) a b (k•x)=family (K:=K) a b x := by
  classical
  have ha : k•x=a ↔ x=a := by
    constructor
    · intro h; exact (MulAction.injective k) (h.trans (hfix k).symm)
    · rintro rfl; exact hfix k
  have hb : k•x∈orbit K b ↔ x∈orbit K b := by rw [← orbit_eq_iff,orbit_smul,orbit_eq_iff]
  simp only [family,ha,hb]

theorem surjective (hab : a∉orbit K b)
    (hcover : orbit K c=(({a}:Set Ω)∪orbit K b)ᶜ) : Function.Surjective (family (K:=K) a b) := by
  intro i
  fin_cases i
  · exact ⟨a,(family_zero a b a).mpr rfl⟩
  · exact ⟨b,(family_one a b hab b).mpr (mem_orbit_self b)⟩
  · exact ⟨c,(family_two a b c hcover c).mpr (mem_orbit_self c)⟩

def orbitEquiv (hfix : ∀k:K,k•a=a) (hab : a∉orbit K b)
    (hcover : orbit K c=(({a}:Set Ω)∪orbit K b)ᶜ) : orbitRel.Quotient K Ω ≃ Fin 3 :=
  (show orbitRel.Quotient K Ω ≃ Quotient (Setoid.ker (family (K:=K) a b)) from
    Quotient.congrRight (fun x y => by
      change orbitRel K Ω x y ↔ family (K:=K) a b x=family (K:=K) a b y
      rw [orbitRel_apply]
      constructor
      · rintro ⟨k,rfl⟩; exact invariant a b hfix k y
      · intro h; exact transitive a b c hab hcover h.symm)).trans
    (Setoid.quotientKerEquivOfSurjective _ (surjective a b c hab hcover))

theorem rank_three (hfix : ∀k:K,k•a=a) (hab : a∉orbit K b)
    (hcover : orbit K c=(({a}:Set Ω)∪orbit K b)ᶜ) : Nat.card (orbitRel.Quotient K Ω)=3 := by
  rw [Nat.card_congr (orbitEquiv a b c hfix hab hcover),Nat.card_fin]

theorem fiber_card [Finite Ω] (hab : a∉orbit K b)
    (hcover : orbit K c=(({a}:Set Ω)∪orbit K b)ᶜ) (i:Fin 3) :
    Nat.card {x:Ω // family (K:=K) a b x=i}=
      (![1,Nat.card (orbit K b),Nat.card (orbit K c)] : Fin 3→ℕ) i := by
  fin_cases i
  · have he : {x:Ω // family (K:=K) a b x=0} ≃ ({a}:Set Ω) :=
      Equiv.subtypeEquivRight (fun x=>family_zero a b x)
    change Nat.card {x:Ω // family (K:=K) a b x=0}=1
    rw [Nat.card_congr he]; simp
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun x=>family_one a b hab x))
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun x=>family_two a b c hcover x))

end MulAction.ThreeSuborbits

namespace MulAction
variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]
    [IsPretransitive G Ω]

/-- The subdegrees of the Rudvalis action force primitivity by block divisibility. -/
theorem primitive_of_subdegrees_1755_2304 (a b c : Ω)
    (hab : a∉orbit (stabilizer G a) b)
    (hcover : orbit (stabilizer G a) c=
      (({a}:Set Ω)∪orbit (stabilizer G a) b)ᶜ)
    (hb : Nat.card (orbit (stabilizer G a) b)=1755)
    (hc : Nat.card (orbit (stabilizer G a) c)=2304)
    (hΩ : Nat.card Ω=4060) : IsPreprimitive G Ω := by
  let d : Fin 3→ℕ := ![1,1755,2304]
  apply Atlas.GroupTheory.primitive_of_rankThree_nondivisibility a
    (ThreeSuborbits.family (K:=stabilizer G a) a b)
    ((ThreeSuborbits.family_zero a b a).mpr rfl)
    (fun _ _ h=>ThreeSuborbits.transitive a b c hab hcover h) d rfl
  · intro i
    simpa only [hb,hc] using ThreeSuborbits.fiber_card a b c hab hcover i
  · change Nat.card Ω=4060; exact hΩ
  · rw [hΩ]; change ¬1756∣4060; decide
  · rw [hΩ]; change ¬2305∣4060; decide
end MulAction
