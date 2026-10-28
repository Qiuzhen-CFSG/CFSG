module

public import Theory.GroupTheory.WordSubgroup

/-! Paired Schreier transfers bound a subgroup in a product. The source representative may be only a point map; word induction retains the target group element alongside it. This is used to identify literal ATLAS generators with actual projective matrices. -/

public section
open Subgroup
namespace Theory.GroupTheory

theorem evalWord_prod {G H : Type*} [Group G] [Group H] {n : Nat}
    (a : Fin n → G) (b : Fin n → H) (w : List (Fin n)) :
    evalWord (fun i => (a i,b i)) w = (evalWord a w,evalWord b w) := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [evalWord,ih]; rfl

theorem card_le_of_paired_transitions {V G : Type*} [Fintype V] [DecidableEq V]
    [Group G] [Finite G] {n m p : Nat}
    (a : Fin n → Equiv.Perm V) (b : Fin n → G) (inv : Fin n → Fin n)
    (ha : ∀i,a (inv i)=(a i)⁻¹) (hb : ∀i,b (inv i)=(b i)⁻¹)
    (c : Fin p → Equiv.Perm V) (d : Fin p → G) (inv' : Fin p → Fin p)
    (hc : ∀i,c (inv' i)=(c i)⁻¹) (hd : ∀i,d (inv' i)=(d i)⁻¹)
    (rep : Fin m → V → V) (repG : Fin m → G)
    (act : Fin n → Fin m → Fin m) (factor : Fin n → Fin m → List (Fin p))
    (initial : Fin m) (hInitial : ∀x,rep initial x=x) (hInitialG : repG initial=1)
    (hStep : ∀i r x,a i (rep r x)=rep (act i r) (evalWord c (factor i r) x))
    (hStepG : ∀i r,b i*repG r=repG (act i r)*evalWord d (factor i r)) :
    Nat.card (wordSubgroup (fun i => (a i,b i)) inv (fun i => Prod.ext (ha i) (hb i))) ≤
      m * Nat.card (wordSubgroup (fun i => (c i,d i)) inv' (fun i => Prod.ext (hc i) (hd i))) := by
  classical
  let H := wordSubgroup (fun i => (a i,b i)) inv (fun i => Prod.ext (ha i) (hb i))
  let K := wordSubgroup (fun i => (c i,d i)) inv' (fun i => Prod.ext (hc i) (hd i))
  have decompose (h : H) : ∃t : Fin m × K,
      (∀x,h.val.1 x=rep t.1 (t.2.val.1 x)) ∧ h.val.2=repG t.1*t.2.val.2 := by
    obtain ⟨w,hw⟩ := h.property
    suffices ∃t : Fin m × K,
        (∀x,(evalWord (fun i => (a i,b i)) w).1 x=rep t.1 (t.2.val.1 x)) ∧
        (evalWord (fun i => (a i,b i)) w).2=repG t.1*t.2.val.2 by
      simpa only [hw] using this
    clear hw h
    induction w with
    | nil => exact ⟨(initial,1),fun x => (hInitial x).symm,by simp [evalWord,hInitialG]⟩
    | cons i w ih =>
      obtain ⟨⟨r,k⟩,hk,hkg⟩ := ih
      let v := evalWord (fun j => (c j,d j)) (factor i r)
      refine ⟨(act i r,⟨v*k.val,K.mul_mem ⟨factor i r,rfl⟩ k.property⟩),?_,?_⟩
      · intro x
        change a i ((evalWord (fun i => (a i,b i)) w).1 x)=_
        rw [hk x,hStep]
        simp only [v,evalWord_prod,Prod.fst_mul,Equiv.Perm.mul_apply]
      · change b i*(evalWord (fun i => (a i,b i)) w).2=_
        rw [hkg,← mul_assoc,hStepG,mul_assoc]
        simp only [v,evalWord_prod,Prod.snd_mul]
  let f : H → Fin m × K := fun h => (decompose h).choose
  have hf : Function.Injective f := by
    intro h k he
    apply Subtype.ext
    apply Prod.ext
    · apply Equiv.ext
      intro x
      have hh := (decompose h).choose_spec.1 x
      have hk := (decompose k).choose_spec.1 x
      change h.val.1 x=rep (f h).1 ((f h).2.val.1 x) at hh
      change k.val.1 x=rep (f k).1 ((f k).2.val.1 x) at hk
      rw [he] at hh
      exact hh.trans hk.symm
    · have hh := (decompose h).choose_spec.2
      have hk := (decompose k).choose_spec.2
      change h.val.2=repG (f h).1*(f h).2.val.2 at hh
      change k.val.2=repG (f k).1*(f k).2.val.2 at hk
      rw [he] at hh
      exact hh.trans hk.symm
  simpa only [Nat.card_prod,Nat.card_fin] using Nat.card_le_card_of_injective f hf
end Theory.GroupTheory
