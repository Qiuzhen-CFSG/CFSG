module
public import Mathlib.Data.List.GetD
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.CosetData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.NormalForms

/-!
# Soundness of the common-factor and Sylow-cover certificates

Three-point checks certify normal-form products and the equations
`factor * w = w * word`. The latter give the required conjugation by
`w`, with no change of coset side. Generator closure and finiteness prove
exhaustiveness of the literal factor list. Right-generator transitions
preserve products of a subgroup member and a representative; induction on
the eight exponents of the actual Sylow normal form proves coverage.

No seed order, factor-list subgroup structure, or witness completeness is
assumed. Source: Parrott (1972), §5, p.683, and the original seed/place JSON.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.SylowCover

private theorem val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl

def field (c offset : Nat) : Fin 2048 :=
  ⟨(c >>> offset) % 2048, Nat.mod_lt _ (by decide)⟩
def productTest (c : Nat) : Bool :=
  sameBase (fastNormalForm (field c 0) * fastNormalForm (field c 11))
    (fastNormalForm (field c 22) * fastNormalForm (field c 33))
theorem product_sound (c : Nat) (h : productTest c = true) :
    atlas1600SylowTwoNormalForm (field c 0) * atlas1600SylowTwoNormalForm (field c 11) =
    atlas1600SylowTwoNormalForm (field c 22) * atlas1600SylowTwoNormalForm (field c 33) := by
  apply (sameBase_iff _ _).mp
  simpa only [productTest, fastNormalForm_eq, val_mul] using h

def conjPlace (c : Nat) : Fin 38 := ⟨c % 64 % 38, Nat.mod_lt _ (by decide)⟩
def conjTest (c : Nat) : Bool :=
  sameBase (fastNormalForm (field c 17) * conjugator (conjPlace c))
    (conjugator (conjPlace c) * fastNormalForm (field c 6))
theorem conj_sound (c : Nat) (h : conjTest c = true) :
    conjugate (conjPlace c) (atlas1600SylowTwoNormalForm (field c 6)) =
      atlas1600SylowTwoNormalForm (field c 17) := by
  have he : atlas1600SylowTwoNormalForm (field c 17) * placeConjugator (conjPlace c) =
      placeConjugator (conjPlace c) * atlas1600SylowTwoNormalForm (field c 6) := by
    apply (sameBase_iff _ _).mp
    simpa only [conjTest, fastNormalForm_eq, conjugator_eq, fastConjugator_eq, val_mul] using h
  unfold conjugate
  rw [← he, mul_inv_cancel_right]

theorem normal_zero : atlas1600SylowTwoNormalForm 0 = 1 := by
  simp [atlas1600SylowTwoNormalForm_eq]

def factorAt (t : Fin 18) (k : Fin 64) : Fin 2048 := (factorIndices t).getD k.val 0
def generatorAt (t : Fin 18) (k : Fin 6) : Fin 2048 := (generatorIndices t).getD k.val 0

def generatorIndex : Fin 8 → Fin 2048 := ![1, 2, 4, 16, 32, 128, 256, 1024]
def generator : Fin 8 → Atlas1600Group :=
  ![atlas1600ParrottAssignment .s1, atlas1600ParrottAssignment .s2,
    atlas1600ParrottAssignment .s3, atlas1600ParrottAssignment .s4,
    atlas1600ParrottAssignment .s5, atlas1600ParrottAssignment .s6,
    atlas1600ParrottAssignment .s7, atlas1600ParrottAssignment .s8]
theorem generator_eq (g : Fin 8) :
    atlas1600SylowTwoNormalForm (generatorIndex g) = generator g := by
  fin_cases g <;> simp [generatorIndex, generator, atlas1600SylowTwoNormalForm_eq]

theorem factor_length (t : Fin 18) : (factorIndices t).length = 64 := by
  revert t
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

theorem generator_length (t : Fin 18) : (generatorIndices t).length ≤ 6 := by
  revert t
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

theorem factorAt_mem (t : Fin 18) (k : Fin 64) : factorAt t k ∈ factorIndices t := by
  unfold factorAt
  rw [List.getD_eq_getElem _ _ (by rw [factor_length]; exact k.isLt)]
  exact List.getElem_mem _

theorem factorAt_surjective (t : Fin 18) (n : Fin 2048) (h : n ∈ factorIndices t) :
    ∃ k : Fin 64, factorAt t k = n := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  refine ⟨⟨k, by rwa [factor_length] at hk⟩, ?_⟩
  exact List.getD_eq_getElem _ _ hk

theorem generatorAt_surjective (t : Fin 18) (n : Fin 2048) (h : n ∈ generatorIndices t) :
    ∃ k : Fin 6, generatorAt t k = n := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  refine ⟨⟨k, lt_of_lt_of_le hk (generator_length t)⟩, ?_⟩
  exact List.getD_eq_getElem _ _ hk

def productRef (r offset : Nat) : Fin 8347 :=
  ⟨(r >>> offset) % 16384 % 8347, Nat.mod_lt _ (by decide)⟩
def closureTest (codes : Fin 8347 → Nat) (t : Fin 18) (r : Nat)
    (g : Fin 6) (k : Fin 64) : Bool :=
  let c := codes (productRef r (14 * (64 * g.val + k.val)))
  (field c 0 == generatorAt t g) && (field c 11 == factorAt t k) &&
    decide (field c 22 ∈ factorIndices t) && (field c 33 == 0)

theorem factor_zero (t : Fin 18) : (0 : Fin 2048) ∈ factorIndices t := by
  revert t
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

theorem closure_sound (codes : Fin 8347 → Nat)
    (hcodes : ∀ i, productTest (codes i) = true) (t : Fin 18) (r : Nat)
    (h : ∀ g k, closureTest codes t r g k = true)
    (q : Atlas1600Group) (hq : q ∈ factorSubgroup t) : q ∈ factors t := by
  have hz := factor_zero t
  have step (g n : Fin 2048) (hg : g ∈ generatorIndices t) (hn : n ∈ factorIndices t) :
      atlas1600SylowTwoNormalForm g * atlas1600SylowTwoNormalForm n ∈ factors t := by
    obtain ⟨a, rfl⟩ := generatorAt_surjective t g hg
    obtain ⟨b, rfl⟩ := factorAt_surjective t n hn
    have hc := h a b
    simp only [closureTest, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    have he := product_sound _ (hcodes (productRef r (14 * (64 * a.val + b.val))))
    rw [hc.1.1.1, hc.1.1.2, hc.2, normal_zero, mul_one] at he
    rw [he]
    exact List.mem_map.mpr ⟨_, hc.1.2, rfl⟩
  have hm : q ∈ Submonoid.closure {x | x ∈ (generatorIndices t).map atlas1600SylowTwoNormalForm} := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hq
  clear hq
  induction hm using Submonoid.closure_induction_left with
  | one => exact normal_zero ▸ List.mem_map.mpr ⟨0, hz, rfl⟩
  | mul_left x hx y _ ih =>
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ih
    exact step g n hg hn

def rowProduct (r : Nat) (a : Fin 32) (g : Fin 8) : Fin 8347 :=
  productRef r (38 * (8 * a.val + g.val))
def rowConj (r : Nat) (a : Fin 32) (g : Fin 8) : Fin 4460 :=
  ⟨(r >>> (38 * (8 * a.val + g.val) + 14)) % 8192 % 4460, Nat.mod_lt _ (by decide)⟩
def rowFactor (r : Nat) (a : Fin 32) (g : Fin 8) : Fin 64 :=
  ⟨(r >>> (38 * (8 * a.val + g.val) + 27)) % 64, Nat.mod_lt _ (by decide)⟩
def rowTarget (r : Nat) (a : Fin 32) (g : Fin 8) : Fin 32 :=
  ⟨(r >>> (38 * (8 * a.val + g.val) + 33)) % 32, Nat.mod_lt _ (by decide)⟩
def rowTest (products : Fin 8347 → Nat) (conjs : Fin 4460 → Nat)
    (t : Fin 18) (j : Fin 38) (r : Nat) (a : Fin 32) (g : Fin 8) : Bool :=
  let p := products (rowProduct r a g)
  let c := conjs (rowConj r a g)
  (field p 0 == sylowRepresentatives t j a) && (field p 11 == generatorIndex g) &&
    (field p 22 == field c 6) && (field p 33 == sylowRepresentatives t j (rowTarget r a g)) &&
    (conjPlace c == j) && (field c 17 == factorAt t (rowFactor r a g))

def Covered (t : Fin 18) (j : Fin 38) (x : Atlas1600Group) : Prop :=
  ∃ q : Atlas1600Group, q ∈ factorSubgroup t ∧ ∃ k : Fin 32,
    x = q * conjugate j (atlas1600SylowTwoNormalForm (sylowRepresentatives t j k))

theorem row_sound (products : Fin 8347 → Nat) (conjs : Fin 4460 → Nat)
    (hp : ∀ i, productTest (products i) = true) (hc : ∀ i, conjTest (conjs i) = true)
    (t : Fin 18) (j : Fin 38) (r : Nat) (a : Fin 32) (g : Fin 8)
    (h : rowTest products conjs t j r a g = true) :
    Covered t j (conjugate j (atlas1600SylowTwoNormalForm (sylowRepresentatives t j a)) *
      conjugate j (generator g)) := by
  simp only [rowTest, Bool.and_eq_true, beq_iff_eq] at h
  have he := product_sound _ (hp (rowProduct r a g))
  rw [h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, generator_eq] at he
  have hj := conj_sound _ (hc (rowConj r a g))
  rw [h.1.2, h.2] at hj
  refine ⟨atlas1600SylowTwoNormalForm (factorAt t (rowFactor r a g)),
    factors_mem_factorSubgroup t _ (List.mem_map.mpr ⟨_, factorAt_mem _ _, rfl⟩),
    rowTarget r a g, ?_⟩
  rw [← conjugate_mul, he, conjugate_mul, hj]

theorem all_covered (t : Fin 18) (j : Fin 38)
    (hz : sylowRepresentatives t j 0 = 0)
    (hs : ∀ (a : Fin 32) (g : Fin 8), Covered t j
      (conjugate j (atlas1600SylowTwoNormalForm (sylowRepresentatives t j a)) *
        conjugate j (generator g))) (n : Fin 2048) :
    Covered t j (conjugate j (atlas1600SylowTwoNormalForm n)) := by
  have h1 : Covered t j (conjugate j 1) := by
    refine ⟨1, (factorSubgroup t).one_mem, 0, ?_⟩
    rw [hz, normal_zero, one_mul]
  have step (x : Atlas1600Group) (hx : Covered t j (conjugate j x)) (g : Fin 8) :
      Covered t j (conjugate j (x * generator g)) := by
    obtain ⟨q, hq, a, he⟩ := hx
    obtain ⟨v, hv, b, hvb⟩ := hs a g
    refine ⟨q * v, (factorSubgroup t).mul_mem hq hv, b, ?_⟩
    rw [conjugate_mul, he, mul_assoc, hvb, ← mul_assoc]
  have power (x : Atlas1600Group) (hx : Covered t j (conjugate j x)) (g : Fin 8) (e : Nat) :
      Covered t j (conjugate j (x * generator g ^ e)) := by
    induction e with
    | zero => simpa only [pow_zero, mul_one] using hx
    | succ e ih => simpa only [pow_succ, ← mul_assoc] using step _ ih g
  rw [atlas1600SylowTwoNormalForm_eq]
  exact power _ (power _ (power _ (power _ (power _ (power _ (power _
    (by simpa [generator] using power 1 h1 0 (n.val % 2)) 1 (n.val / 2 % 2))
    2 (n.val / 4 % 4)) 3 (n.val / 16 % 2)) 4 (n.val / 32 % 4))
    5 (n.val / 128 % 2)) 6 (n.val / 256 % 4)) 7 (n.val / 1024 % 2)

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.SylowCover
