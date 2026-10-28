module

public import Theory.Representation.PSL3Two.SmallModules
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.Tactic.FinCases

/-!
# Equal-weight subgroups of the natural binary point radical

The literal point radical consists of the two upper-row translations. Its
cyclic subgroups fix a plane and the full radical fixes a line, so every
subgroup has weight three on the natural module. The three displayed cyclic
root groups generate SL₃(2), and each nonidentity point translation is
conjugate to the first root by an element of the point parabolic.

These are the marked finite-geometry inputs to the actual full-preimage
Baumann family in the natural-point branch of Aschbacher--Smith C.1.37,
printed pp.141--143. The proof uses structural transvection generation and
small checked 3-by-3 matrix identities, without enumerating SL₃(2).
-/

@[expose] public section

open Matrix Subgroup
namespace Matrix.PSL3Two.PointOffenders
open MarkedAutomorphisms
abbrev Vector := Fin 3 → ZMod 2

def row : Multiplicative (ZMod 2 × ZMod 2) →* SL where
  toFun a := ⟨!![1,a.toAdd.1,a.toAdd.2; 0,1,0; 0,0,1], by simp [det_fin_three]⟩
  map_one' := by apply Subtype.ext; decide
  map_mul' a b := by
    apply Subtype.ext
    change !![1,a.toAdd.1+b.toAdd.1,a.toAdd.2+b.toAdd.2; 0,1,0; 0,0,1] =
      !![1,a.toAdd.1,a.toAdd.2; 0,1,0; 0,0,1] *
        !![1,b.toAdd.1,b.toAdd.2; 0,1,0; 0,0,1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem row_injective : Function.Injective row := by
  intro a b h
  exact Prod.ext (congrArg (fun g : SL => g.val 0 1) h)
    (congrArg (fun g : SL => g.val 0 2) h)

theorem row_range : row.range = pointV := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    change (1:ZMod 2)=1 ∧ 0=0 ∧ 0=0 ∧ 1=1 ∧ 0=0 ∧ 0=0 ∧ 1=1
    simp
  · intro g hg
    refine ⟨Multiplicative.ofAdd (g.val 0 1, g.val 0 2), ?_⟩
    apply Subtype.ext
    change pointCorePred g at hg
    rcases hg with ⟨h00,h10,h20,h11,h12,h21,h22⟩
    change !![1,g.val 0 1,g.val 0 2; 0,1,0; 0,0,1] = g.val
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00,h10,h20,h11,h12,h21,h22]

def root : Fin 3 → SL :=
  ![row (Multiplicative.ofAdd (1,0)),
    ⟨!![1,0,0; 0,1,1; 0,0,1], by decide⟩,
    ⟨!![1,0,0; 0,1,0; 1,0,1], by decide⟩]

def cycle : SL := ⟨!![0,0,1; 1,0,0; 0,1,0], by decide⟩

theorem root_conjugate (i : Fin 3) :
    MulAut.conj (cycle ^ i.val) (root 0) = root i := by
  revert i
  decide +kernel

theorem root_square (i : Fin 3) : root i ^ 2 = 1 := by
  revert i
  decide +kernel

theorem root_ne_one (i : Fin 3) : root i ≠ 1 := by
  revert i
  decide +kernel

theorem root_order (i : Fin 3) : orderOf (root i) = 2 :=
  orderOf_eq_prime (root_square i) (root_ne_one i)

private theorem root_transvections : ∀ (i j : Fin 3) (h : i ≠ j),
    SpecialLinearGroup.transvection h (1 : ZMod 2) ∈
      ⨆ k, zpowers (root k) := by
  intro i j h
  let I := ⨆ k, zpowers (root k)
  have hr (k : Fin 3) : root k ∈ I := le_iSup (fun k => zpowers (root k)) k (mem_zpowers _)
  have hc (k l : Fin 3) : root k * root l * (root k)⁻¹ * (root l)⁻¹ ∈ I :=
    I.mul_mem (I.mul_mem (I.mul_mem (hr k) (hr l)) (I.inv_mem (hr k))) (I.inv_mem (hr l))
  fin_cases i <;> fin_cases j
  · exact (h rfl).elim
  · convert hr 0 using 1
    revert h; decide +kernel
  · convert hc 0 1 using 1
    revert h; decide +kernel
  · convert hc 1 2 using 1
    revert h; decide +kernel
  · exact (h rfl).elim
  · convert hr 1 using 1
    revert h; decide +kernel
  · convert hr 2 using 1
    revert h; decide +kernel
  · convert hc 2 0 using 1
    revert h; decide +kernel
  · exact (h rfl).elim

theorem root_generation : (⨆ i, zpowers (root i)) = ⊤ := by
  apply eq_top_iff.mpr
  intro g _
  apply Representation.OneCohomology.SLHigherNatural.transvection_induction
    (fun g => g ∈ ⨆ i, zpowers (root i)) ?_ ?_ g
  · intro i j h c
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simp
    · exact root_transvections i j h
  · exact fun a b ha hb => mul_mem ha hb

def fixed (E : Subgroup SL) := {v : Vector // ∀ g ∈ E, g • v = v}

private theorem fixes_zpowers (g : SL) (v : Vector) :
    (∀ a ∈ zpowers g, a • v = v) ↔ g • v = v := by
  constructor
  · exact fun h => h g (mem_zpowers g)
  · intro h a ha
    exact (zpowers_le.mpr (show g ∈ MulAction.stabilizer SL v from h)) ha

theorem cyclic_fixed_card (a : ZMod 2 × ZMod 2) (ha : a ≠ 0) :
    Nat.card (fixed (zpowers (row (Multiplicative.ofAdd a)))) = 4 := by
  let e : fixed (zpowers (row (Multiplicative.ofAdd a))) ≃
      {v : Vector // row (Multiplicative.ofAdd a) • v = v} :=
    Equiv.subtypeEquivRight (fun v => fixes_zpowers _ v)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  revert ha a
  decide +kernel

theorem point_fixed_card : Nat.card (fixed pointV) = 2 := by
  have h (v : Vector) : (∀ g ∈ pointV, g • v = v) ↔ v 1 = 0 ∧ v 2 = 0 := by
    rw [← row_range]
    constructor
    · intro hv
      have h1 := hv (row (Multiplicative.ofAdd (1,0))) ⟨_, rfl⟩
      have h2 := hv (row (Multiplicative.ofAdd (0,1))) ⟨_, rfl⟩
      have he : ∀ v : Vector,
          row (Multiplicative.ofAdd (1,0)) • v = v →
          row (Multiplicative.ofAdd (0,1)) • v = v → v 1 = 0 ∧ v 2 = 0 := by
        decide +kernel
      exact he v h1 h2
    · rintro ⟨h1,h2⟩ _ ⟨a,rfl⟩
      have he : ∀ (a : ZMod 2 × ZMod 2) (v : Vector),
          v 1 = 0 → v 2 = 0 → row (Multiplicative.ofAdd a) • v = v := by
        decide +kernel
      exact he a.toAdd v h1 h2
  let e : fixed pointV ≃ {v : Vector // v 1 = 0 ∧ v 2 = 0} :=
    Equiv.subtypeEquivRight h
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide


theorem row_order (a : ZMod 2 × ZMod 2) (ha : a ≠ 0) :
    orderOf (row (Multiplicative.ofAdd a)) = 2 := by
  apply orderOf_eq_prime
  · revert a; decide +kernel
  · intro hz
    exact ha (row_injective (hz.trans row.map_one.symm))

theorem subgroup_cases (E : Subgroup SL) (hE : E ≤ pointV) :
    E = ⊥ ∨ (∃ a : ZMod 2 × ZMod 2, a ≠ 0 ∧
      E = zpowers (row (Multiplicative.ofAdd a))) ∨ E = pointV := by
  have hd : Nat.card E ∣ 2 ^ 2 := by
    simpa only [card_pointV, show (2:ℕ)^2=4 from rfl] using card_dvd_of_le hE
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · exact Or.inl (Subgroup.card_eq_one.mp he)
  · have hne : E ≠ ⊥ := by
      intro hz
      rw [hz, card_bot] at he
      norm_num at he
    obtain ⟨g, hg, hg1⟩ : ∃ g ∈ E, g ≠ 1 := by
      by_contra! hzero
      exact hne (eq_bot_iff.mpr hzero)
    obtain ⟨a, rfl⟩ := (show g ∈ row.range from row_range.symm ▸ hE hg)
    have ha : a.toAdd ≠ 0 := by
      intro hz
      have : a = 1 := hz
      exact hg1 (this ▸ row.map_one)
    refine Or.inr (Or.inl ⟨a.toAdd, ha, ?_⟩)
    apply (eq_of_le_of_card_ge (zpowers_le.mpr hg) ?_).symm
    have ho : orderOf (row a) = 2 := row_order a.toAdd ha
    rw [Nat.card_zpowers, ho, he]
    norm_num
  · exact Or.inr (Or.inr (eq_of_le_of_card_ge hE (by rw [card_pointV, he]; norm_num)))

theorem bot_fixed_card : Nat.card (fixed ⊥) = 8 := by
  let e : fixed ⊥ ≃ Vector :=
    { toFun := Subtype.val
      invFun := fun v => ⟨v, by
        intro g hg
        have : g = 1 := hg
        simp [this]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp [Vector]

theorem fixed_card_identity (E : Subgroup SL) (hE : E ≤ pointV) :
    Nat.card (fixed E) * Nat.card E = 8 := by
  rcases subgroup_cases E hE with rfl | ⟨a, ha, rfl⟩ | rfl
  · rw [bot_fixed_card, card_bot]
  · rw [cyclic_fixed_card a ha, Nat.card_zpowers, row_order a ha]
  · rw [point_fixed_card, card_pointV]

def rowConjugator (a : ZMod 2 × ZMod 2) : SL :=
  if a = (1,0) then 1 else if a = (0,1) then
    ⟨!![1,0,0; 0,0,1; 0,1,0], by decide⟩ else root 1

theorem row_conjugate (a : ZMod 2 × ZMod 2) (ha : a ≠ 0) :
    MulAut.conj (rowConjugator a) (root 0) = row (Multiplicative.ofAdd a) := by
  revert ha a
  decide +kernel

theorem rowConjugator_mem (a : ZMod 2 × ZMod 2) : rowConjugator a ∈ pointParabolicSL := by
  revert a
  decide +kernel


/-- Each of the three generating involutions fixes a plane. -/
theorem root_fixed_card (i : Fin 3) : Nat.card (fixed (zpowers (root i))) = 4 := by
  let e : fixed (zpowers (root i)) ≃ {v : Vector // root i • v = v} :=
    Equiv.subtypeEquivRight (fun v => fixes_zpowers _ v)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  revert i
  decide +kernel

/-- The full natural action has no nonzero fixed vector. -/
theorem top_fixed_card : Nat.card (fixed ⊤) = 1 := by
  have h (v : Vector) : (∀ g ∈ (⊤ : Subgroup SL), g • v = v) ↔ v = 0 := by
    constructor
    · intro hv
      have hz : ∀ v : Vector, root 0 • v = v → root 1 • v = v →
          root 2 • v = v → v = 0 := by decide +kernel
      exact hz v (hv _ (mem_top _)) (hv _ (mem_top _)) (hv _ (mem_top _))
    · rintro rfl g _
      exact smul_zero g
  let e : fixed ⊤ ≃ {v : Vector // v = 0} := Equiv.subtypeEquivRight h
  rw [Nat.card_congr e]
  simp

open Representation.BinaryOffender

private def fixedSpaceEquiv (E : Subgroup SL) :
    fixedSpace BinaryLinearThree.W E ≃ fixed E where
  toFun v := ⟨v.val, fun g hg => v.property ⟨g,hg⟩⟩
  invFun v := ⟨v.val, fun g => v.property g g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fixedSpace_card (E : Subgroup SL) :
    Nat.card (fixedSpace BinaryLinearThree.W E) = Nat.card (fixed E) :=
  Nat.card_congr (fixedSpaceEquiv E)

theorem fixed_rank_sum (E : Subgroup SL) (hE : E ≤ pointV) :
    Module.finrank (ZMod 2) (fixedSpace BinaryLinearThree.W E) + Representation.BinaryOffender.rank E = 3 := by
  have hcard : Nat.card E = 2 ^ Representation.BinaryOffender.rank E := by
    rcases subgroup_cases E hE with rfl | ⟨a,ha,rfl⟩ | rfl
    · simp [Representation.BinaryOffender.rank]
    · rw [Representation.BinaryOffender.rank, Nat.card_zpowers, row_order a ha]
      decide
    · rw [Representation.BinaryOffender.rank, card_pointV]
      decide
  have hf := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace BinaryLinearThree.W E)
  rw [Nat.card_zmod, fixedSpace_card] at hf
  have hn := fixed_card_identity E hE
  rw [hf, hcard, ← pow_add] at hn
  have hl := congrArg (Nat.log 2) hn
  simpa only [Nat.log_pow Nat.one_lt_two, show Nat.log 2 8 = 3 from rfl] using hl

theorem fixedCodim_eq_rank (E : Subgroup SL) (hE : E ≤ pointV) :
    fixedCodim BinaryLinearThree.W E = Representation.BinaryOffender.rank E := by
  have hf := fixedCodim_add_finrank BinaryLinearThree.W E
  have hs := fixed_rank_sum E hE
  have hn : Module.finrank (ZMod 2) BinaryLinearThree.Vector = 3 := by
    simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]
  rw [hn] at hf
  omega

theorem weight_eq_three (E : Subgroup SL) (hE : E ≤ pointV) :
    weight BinaryLinearThree.W E = 3 := by
  rw [weight, Nat.add_comm]
  exact fixed_rank_sum E hE

theorem equalWeightLE_of_le {A B : Subgroup SL} (hA : A ≤ pointV) (hBA : B ≤ A) :
    EqualWeightLE BinaryLinearThree.W B A :=
  ⟨hBA, (weight_eq_three B (hBA.trans hA)).trans (weight_eq_three A hA).symm⟩

end Matrix.PSL3Two.PointOffenders
