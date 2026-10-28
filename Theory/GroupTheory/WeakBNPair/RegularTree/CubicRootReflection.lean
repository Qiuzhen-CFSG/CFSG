module
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootCartanCentralizer
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# Prescribed involution classes at cubic path endpoints

An odd one-step path stabilizer makes evaluation on exits injective on the
path two-core. At a cubic endpoint there are only two exits, so a nontrivial
root has order two and its normalizer centralizes it. Conjugation by a
Cartan-centralizing involution moving the preceding vertex therefore gives
a reflection in the prescribed root involution class. The argument retains
the actual path radical and requires no faithfulness of the ambient action.

Source application: DGS, *Groups and Graphs* (1985), (14.2), pp.210--211,
the binary commuting endpoint of (11.7).
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.Walk
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

/-- Odd extensions and a cubic endpoint bound its nontrivial root by two. -/
theorem cubic_pathRoot_card_two
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {a b : V} (p : Γ.Walk a b) (hpnil : ¬p.Nil)
    (hval : Nat.card (Γ.neighborSet b)=3)
    (c : pathExit p)
    (hodd : Odd (Nat.card (pathFixer (X := X) (p.concat c.property.1))))
    (x : X) (hx : x∈pathRoot (X := X) p) (hx1 : x≠1) :
    Nat.card (pathRoot (X := X) p)=2 := by
  let _ : Finite (Γ.neighborSet b) := Nat.finite_of_card_ne_zero (by rw [hval]; decide)
  let _ : Finite (pathExit p) := Finite.of_injective
    (fun z : pathExit p => (⟨z.val,z.property.1⟩ : Γ.neighborSet b))
    (fun _ _ he => Subtype.ext (congrArg (fun z : Γ.neighborSet b => z.val) he))
  let f : pathRoot (X := X) p → pathExit p := fun y =>
    ⟨(y:X) • (c:V),pathRoot_smul_exit hact p c y⟩
  have hf : Function.Injective f := fun y z he =>
    pathRoot_smul_injective p c.property.1 hodd (congrArg Subtype.val he)
  let _ : Finite (pathRoot (X := X) p) := Finite.of_injective f hf
  have hc := card_pathExit p hpnil
  have hle := Nat.card_le_card_of_injective f hf
  have hne : pathRoot (X := X) p≠⊥ := by
    intro he
    rw [he] at hx
    exact hx1 hx
  have htwo := (pathRoot (X := X) p).one_lt_card_iff_ne_bot.mpr hne
  rw [hval] at hc
  omega

/-- A Cartan-centralizing mover conjugates the involution of a cubic root
into a reflection, retaining the specified conjugacy class. -/
theorem cubic_pathRoot_conjugate_reflection
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {a b : V} (p : Γ.Walk a b) (hpnil : ¬p.Nil)
    (hval : Nat.card (Γ.neighborSet b)=3)
    (K : Subgroup X) (hK : K≤pathFixer (X := X) p)
    (hodd : ∀ {c} (hc : Γ.Adj b c), c≠p.penultimate →
      Odd (Nat.card (pathFixer (X := X) (p.concat hc))))
    (x : X) (hx : x∈pathRoot (X := X) p) (hx1 : x≠1) (hx2 : x*x=1)
    (t : X) (htb : t • b=b) (htmove : t • p.penultimate≠p.penultimate)
    (ht2 : t*t=1) (htK : t∈centralizer (K : Set X)) :
    (t*x*t⁻¹) • b=b ∧ (t*x*t⁻¹) • p.penultimate≠p.penultimate ∧
      (t*x*t⁻¹)*(t*x*t⁻¹)=1 ∧ t*x*t⁻¹∈centralizer (K : Set X) := by
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right ht2
  have hc : Γ.Adj b (t • p.penultimate) := by
    simpa only [htb] using hact t (p.adj_penultimate hpnil).symm
  have ho := hodd hc htmove
  have hcard := cubic_pathRoot_card_two hact p hpnil hval ⟨_,hc,htmove⟩ ho x hx hx1
  have hxK : x∈centralizer (K : Set X) := by
    apply mem_centralizer_iff.mpr
    intro k hk
    have hh := normalizer_le_centralizer_of_card_two (pathRoot (X := X) p) hcard
      (pathFixer_le_normalizer_pathRoot p (hK hk))
    exact (mem_centralizer_iff.mp hh x hx).symm
  refine ⟨?_,?_,?_,(centralizer (K : Set X)).mul_mem
    ((centralizer (K : Set X)).mul_mem htK hxK) ((centralizer (K : Set X)).inv_mem htK)⟩
  · rw [mul_smul,mul_smul,hti,htb,(pathRoot_fixes p hx).1,htb]
  · intro he
    have he' : x • (t • p.penultimate)=t • p.penultimate := by
      have hh := congrArg (fun z : V => t⁻¹ • z) he
      simp only [mul_smul,inv_smul_smul] at hh
      simpa only [hti] using hh
    have hh : x∈pathRoot (X := X) p ⊓ MulAction.stabilizer X (t • p.penultimate) := ⟨hx,he'⟩
    rw [pathRoot_inf_stabilizer_eq_bot p hc ho] at hh
    exact hx1 hh
  · calc
      _ = t*(x*x)*t⁻¹ := by group
      _ = 1 := by rw [hx2,mul_one,mul_inv_cancel]
end Theory.GroupTheory.WeakBNPair.RegularTree
