module
public import Theory.SpecificGroups.SL2.OddBorelMarking
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Full odd tori in a binary SL₂ pair Borel

An odd subgroup of the paired Sylow normalizer of order `(q - 1)^2`
becomes the full diagonal torus under one pair of inner markings. The
literal projection kernels are cyclic of order `q - 1`, disjoint, and
generate the original subgroup. Simultaneous Borel diagonalization and
finite cardinality give the equivalence with the two unit groups.

Source application: Aschbacher–Smith 10.2.3(4), printed pp.746–747.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
set_option backward.isDefEq.respectTransparency false
variable {F X : Type*} [Field F] [Finite F] [CharP F 2] [Group X] [Finite X]

omit [Finite X] in
/-- A full odd subgroup in the pair Borel is the full split torus, with one common marking. -/
theorem full_pair_borel_torus_coordinates
    (S : Sylow 2 (SL(2,F) × SL(2,F)))
    (q : X →* SL(2,F) × SL(2,F)) (hq : Function.Injective q)
    (hN : q.range ≤ normalizer (S : Set (SL(2,F) × SL(2,F))))
    (ho : Odd (Nat.card X)) (hc : Nat.card X = (Nat.card F - 1)^2) :
    ∃ (a b : SL(2,F)) (d : X ≃* Fˣ × Fˣ),
      ∀ x : X, ((MulAut.conj a).prodCongr (MulAut.conj b)) (q x) =
        (diag2 ((d x).1 : F) (Units.ne_zero _),
          diag2 ((d x).2 : F) (Units.ne_zero _)) := by
  have hor : Odd (Nat.card q.range) := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hq).toEquiv]
    exact ho
  obtain ⟨a,b,d,_,hd⟩ := pair_sylow_odd_subgroup_diagonal_coordinates S q.range hN hor
  let f := d.comp q.rangeRestrict
  have hi : Function.Injective f := by
    intro x y he
    apply hq
    apply ((MulAut.conj a).prodCongr (MulAut.conj b)).injective
    have hx : ((MulAut.conj a).prodCongr (MulAut.conj b)) (q x) =
        (diag2 ((f x).1 : F) (Units.ne_zero _),diag2 ((f x).2 : F) (Units.ne_zero _)) := hd (q.rangeRestrict x)
    have hy : ((MulAut.conj a).prodCongr (MulAut.conj b)) (q y) =
        (diag2 ((f y).1 : F) (Units.ne_zero _),diag2 ((f y).2 : F) (Units.ne_zero _)) := hd (q.rangeRestrict y)
    rw [hx,hy,he]
  have hcard : Nat.card X = Nat.card (Fˣ × Fˣ) := by
    rw [hc,Nat.card_prod,Nat.card_units,pow_two]
  let e := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hcard⟩)
  exact ⟨a,b,e,fun x => hd (q.rangeRestrict x)⟩

omit [Finite F] [CharP F 2] in
private theorem diagonal_unit_eq_one (z : Fˣ) : diag2 (z : F) z.ne_zero = 1 ↔ z = 1 := by
  constructor
  · intro h
    apply Units.ext
    have he := congrArg (fun g : SL(2,F) => g.val 0 0) h
    simpa [diag2_coe'] using he
  · intro h
    subst z
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe']

/-- Both literal projection kernels have the full torus order and generate the original group. -/
theorem full_pair_borel_coordinate_kernels
    (S : Sylow 2 (SL(2,F) × SL(2,F)))
    (q : X →* SL(2,F) × SL(2,F)) (hq : Function.Injective q)
    (hN : q.range ≤ normalizer (S : Set (SL(2,F) × SL(2,F))))
    (ho : Odd (Nat.card X)) (hc : Nat.card X = (Nat.card F - 1)^2) :
    let q₁ := (MonoidHom.fst SL(2,F) SL(2,F)).comp q
    let q₂ := (MonoidHom.snd SL(2,F) SL(2,F)).comp q
    Nat.card q₁.ker = Nat.card F - 1 ∧ Nat.card q₂.ker = Nat.card F - 1 ∧
      Disjoint q₁.ker q₂.ker ∧ q₁.ker ⊔ q₂.ker = ⊤ ∧
      IsCyclic q₁.ker ∧ IsCyclic q₂.ker := by
  dsimp only
  let q₁ := (MonoidHom.fst SL(2,F) SL(2,F)).comp q
  let q₂ := (MonoidHom.snd SL(2,F) SL(2,F)).comp q
  obtain ⟨a,b,d,hd⟩ := full_pair_borel_torus_coordinates S q hq hN ho hc
  let r₁ := (MonoidHom.fst Fˣ Fˣ).comp d.toMonoidHom
  let r₂ := (MonoidHom.snd Fˣ Fˣ).comp d.toMonoidHom
  have hker₁ : q₁.ker = r₁.ker := by
    ext x
    change (q x).1 = 1 ↔ (d x).1 = 1
    have hh := congrArg Prod.fst (hd x)
    change (MulAut.conj a) (q x).1 = diag2 ((d x).1 : F) (Units.ne_zero _) at hh
    rw [←(MulAut.conj a).map_eq_one_iff,hh,diagonal_unit_eq_one]
  have hker₂ : q₂.ker = r₂.ker := by
    ext x
    change (q x).2 = 1 ↔ (d x).2 = 1
    have hh := congrArg Prod.snd (hd x)
    change (MulAut.conj b) (q x).2 = diag2 ((d x).2 : F) (Units.ne_zero _) at hh
    rw [←(MulAut.conj b).map_eq_one_iff,hh,diagonal_unit_eq_one]
  have hr₁ : Function.Surjective r₁ := Prod.fst_surjective.comp d.surjective
  have hr₂ : Function.Surjective r₂ := Prod.snd_surjective.comp d.surjective
  have cardker (r : X →* Fˣ) (hr : Function.Surjective r) : Nat.card r.ker = Nat.card F - 1 := by
    have hm := r.ker.card_mul_index
    rw [index_ker,r.range_eq_top_of_surjective hr,card_top,Nat.card_units,hc,pow_two] at hm
    have hp : 0 < Nat.card F - 1 := by have := Finite.one_lt_card (α := F); omega
    exact Nat.eq_of_mul_eq_mul_right hp hm
  have hk₁ : Nat.card q₁.ker = Nat.card F - 1 := hker₁ ▸ cardker r₁ hr₁
  have hk₂ : Nat.card q₂.ker = Nat.card F - 1 := hker₂ ▸ cardker r₂ hr₂
  have hdis : Disjoint q₁.ker q₂.ker := by
    apply disjoint_def.mpr
    intro x hx hy
    apply hq
    rw [map_one]
    exact Prod.ext hx hy
  have hsup : q₁.ker ⊔ q₂.ker = ⊤ := by
    apply eq_top_of_card_eq
    rw [card_sup_eq_mul_of_normalizes_of_disjoint q₁.ker q₂.ker
      (by rw [normalizer_eq_top]; exact le_top) hdis,hk₁,hk₂,hc,pow_two]
  refine ⟨hk₁,hk₂,hdis,hsup,?_,?_⟩
  · rw [hker₁]
    apply isCyclic_of_injective (r₂.comp r₁.ker.subtype)
    intro x y he
    apply Subtype.ext
    apply d.injective
    exact Prod.ext (x.property.trans y.property.symm) he
  · rw [hker₂]
    apply isCyclic_of_injective (r₁.comp r₂.ker.subtype)
    intro x y he
    apply Subtype.ext
    apply d.injective
    exact Prod.ext he (x.property.trans y.property.symm)
end Matrix.SpecialLinearGroup
