module

public import Theory.Character.InvolutionSum

/-!
# Involution sums over conjugacy representatives

A separating and exhaustive family of involution representatives partitions
the involutions into conjugacy classes. Orbit–stabilizer evaluates the size
of each class, giving the involution sum of any class function.

Source: the orbit–stabilizer theorem; this extends the single-class formula
in `Theory.Character.InvolutionSum`.
-/

public section
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.Character

/-- Sum a class function over a complete, nonredundant family of involution classes. -/
theorem involutionSum_of_representatives
    {H I : Type*} [Group H] [Finite H] [Finite I]
    (a : I → H) (ha : ∀ i, orderOf (a i) = 2)
    (hcover : ∀ u : H, orderOf u = 2 → ∃ i, IsConj (a i) u)
    (hsep : ∀ i j, IsConj (a i) (a j) → i = j)
    (f : ClassFunction H) (hf : IsClassFunction f) :
    involutionSum f = ∑ i, (Nat.card H : ℂ) /
      Nat.card (Subgroup.centralizer ({a i} : Set H)) * f (a i) := by
  classical
  let F : (Σ i, (ConjClasses.mk (a i)).carrier) → {u : H // orderOf u = 2} :=
    fun p => ⟨p.2.1, by
      have hc : IsConj (a p.1) p.2.1 := p.2.property
      obtain ⟨g, hg⟩ := isConj_iff.mp hc
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq _).trans (ha p.1)⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, u⟩ ⟨j, v⟩ he
      have huv : u.val = v.val := congrArg Subtype.val he
      have hij : i = j := hsep i j
        ((show IsConj (a i) u.val from u.property).trans
          (huv ▸ (show IsConj (a j) v.val from v.property).symm))
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext huv)
    · intro u
      obtain ⟨i, hi⟩ := hcover u.val u.property
      exact ⟨⟨i, ⟨u.val, hi⟩⟩, rfl⟩
  change (∑ u : {u : H // orderOf u = 2}, f u) = _
  rw [← Fintype.sum_bijective F hF (fun p => f p.2.val) (fun u => f u.val) (fun _ => rfl),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have hv (u : (ConjClasses.mk (a i)).carrier) : f u.val = f (a i) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (show IsConj (a i) u.val from u.property)
    rw [← hg]
    exact hf _ _
  simp only [hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct H) (a i)
  have he : Nat.card (MulAction.stabilizer (ConjAct H) (a i)) =
      Nat.card (Subgroup.centralizer ({a i} : Set H)) := by
    apply Nat.card_congr
    exact {
      toFun := fun g => ⟨ConjAct.ofConjAct g.val, by
        simpa only [Subgroup.mem_centralizer_singleton_iff,
          MulAction.mem_stabilizer_iff, ConjAct.smul_def,
          mul_inv_eq_iff_eq_mul] using g.property⟩
      invFun := fun g => ⟨ConjAct.toConjAct g.val, by
        simpa only [Subgroup.mem_centralizer_singleton_iff,
          MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul,
          mul_inv_eq_iff_eq_mul] using g.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc' : Nat.card (ConjClasses.mk (a i)).carrier *
      Nat.card (Subgroup.centralizer ({a i} : Set H)) = Nat.card H := by
    simpa only [ConjAct.orbit_eq_carrier_conjClasses, ← Nat.card_eq_fintype_card,
      he, Nat.card_congr (ConjAct.ofConjAct (G := H)).toEquiv] using hc
  have hn : (Nat.card (Subgroup.centralizer ({a i} : Set H)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({a i} : Set H))).ne'
  congr 1
  apply (eq_div_iff hn).mpr
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast hc'

end Theory.Character
