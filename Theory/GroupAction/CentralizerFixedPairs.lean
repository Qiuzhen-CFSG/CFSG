module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Counting fixed pairs using a centralizer

Suppose a doubly transitive group has an element fixing two distinct points.
If its conjugacy class meets their stabilizer only in that element, its
centralizer is transitive on ordered pairs of distinct fixed points. When
the two-point stabilizer centralizes the element, orbit–stabilizer gives
`|C| = |K| f (f - 1)`, where `f` counts its fixed points.

This is the fixed-pair counting argument used in Suzuki (1965), Section II.
-/

namespace MulAction

/-- Count a centralizer by its orbit on ordered pairs of distinct fixed points. -/
public theorem card_centralizer_eq_twoPoint_mul_fixed_pairs
    {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]
    (htrans : IsMultiplyPretransitive G Ω 2)
    (a b : Ω) (hab : a ≠ b) (j : G) (hja : j • a = a) (hjb : j • b = b)
    (hcomm : ∀ k : stabilizer (stabilizer G a) b,
      Commute j ((k : stabilizer G a) : G))
    (hrigid : ∀ k : stabilizer (stabilizer G a) b,
      IsConj j ((k : stabilizer G a) : G) → ((k : stabilizer G a) : G) = j) :
    Nat.card (Subgroup.centralizer ({j} : Set G)) =
      Nat.card (stabilizer (stabilizer G a) b) *
        (Nat.card {x : Ω // j • x = x} * (Nat.card {x : Ω // j • x = x} - 1)) := by
  classical
  let C := Subgroup.centralizer ({j} : Set G)
  let F := {x : Ω // j • x = x}
  let P := (x : F) × {y : F // y ≠ x}
  have htransport (x y : F) (hxy : x ≠ y) :
      ∃ c : C, (c : G) • a = x ∧ (c : G) • b = y := by
    obtain ⟨g, hga, hgb⟩ := is_two_pretransitive_iff.mp htrans hab
      (show (x : Ω) ≠ y from fun he => hxy (Subtype.ext he))
    have hfix (z : Ω) (hz : j • (g • z) = g • z) :
        (g⁻¹ * j * g) • z = z := by
      rw [mul_smul, mul_smul, hz, inv_smul_smul]
    let k : stabilizer (stabilizer G a) b :=
      ⟨⟨g⁻¹ * j * g, hfix a (by rw [hga]; exact x.property)⟩,
        hfix b (by rw [hgb]; exact y.property)⟩
    have he : g⁻¹ * j * g = j := hrigid k
      (isConj_iff.mpr ⟨g⁻¹, by simp only [inv_inv]; rfl⟩)
    have hgc : g ∈ C := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have he' := congrArg (fun z : G => g * z) he
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he'.symm
    exact ⟨⟨g, hgc⟩, hga, hgb⟩
  let e : orbit C (a, b) ≃ P := Equiv.ofBijective
    (fun z => by
      have hz : j • z.val.1 = z.val.1 ∧ j • z.val.2 = z.val.2 ∧
          z.val.2 ≠ z.val.1 := by
        obtain ⟨c, hc⟩ := z.property
        have hc' : ((c : G) • a, (c : G) • b) = z.val := hc
        have hf (w : Ω) (hw : j • w = w) : j • ((c : G) • w) = (c : G) • w := by
          rw [← mul_smul, (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm,
            mul_smul, hw]
        rw [← hc']
        exact ⟨hf a hja, hf b hjb, fun he => hab ((MulAction.injective (c : G)) he).symm⟩
      exact ⟨⟨z.val.1, hz.1⟩, ⟨⟨z.val.2, hz.2.1⟩,
        fun he => hz.2.2 (congrArg Subtype.val he)⟩⟩)
    (by
      constructor
      · intro x y he
        apply Subtype.ext
        exact Prod.ext (congrArg (fun p : P => p.1.val) he)
          (congrArg (fun p : P => p.2.val.val) he)
      · intro p
        obtain ⟨c, hca, hcb⟩ := htransport p.1 p.2.val p.2.property.symm
        refine ⟨⟨(p.1.val, p.2.val.val), ⟨c, Prod.ext hca hcb⟩⟩, ?_⟩
        rfl)
  let s : stabilizer C (a, b) ≃ stabilizer (stabilizer G a) b := {
    toFun := fun c => ⟨⟨c.val.val, congrArg Prod.fst c.property⟩,
      congrArg Prod.snd c.property⟩
    invFun := fun k => ⟨⟨k.val.val,
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm k).symm.eq⟩,
      Prod.ext k.val.property k.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let : Fintype F := Fintype.ofFinite F
  have hP : Nat.card P = Nat.card F * (Nat.card F - 1) := by
    rw [Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc
    Nat.card C = Nat.card (orbit C (a, b)) * Nat.card (stabilizer C (a, b)) :=
      (Nat.card_congr (orbitProdStabilizerEquivGroup C (a, b))).symm.trans
        (Nat.card_prod _ _)
    _ = Nat.card P * Nat.card (stabilizer (stabilizer G a) b) := by
      rw [Nat.card_congr e, Nat.card_congr s]
    _ = _ := by rw [hP, Nat.mul_comm]

end MulAction
