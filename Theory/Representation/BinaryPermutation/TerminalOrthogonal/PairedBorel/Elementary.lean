module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.Model
public import Theory.ElementaryAbelian.Basic

/-!
# The specified elementary eight-subgroup of the paired orthogonal model

The three binary coordinates give the two diagonal Klein generators and the
literal factor interchange. Their faithful homomorphism constructs a genuine
elementary subgroup of order eight inside the swapped permutation actor.
It lies in the extension of the paired A₅ subgroup by the interchange. A
nonzero vector fixed by it is the distinguished diagonal singular point.

Only the four Klein words and eight binary coefficient triples are enumerated;
the semidirect-product laws are handled structurally. This is the standard
marked subgroup in Aschbacher–Smith, G.11.2(12), printed p.364, used in
12.8.13(7), printed p.856 (combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup
namespace BinaryPermutation.TerminalOrthogonal.PairedBorel
open BinaryPermutation.CubicFixedSpace.Five

abbrev BinaryCube := Multiplicative (Fin 3 → ZMod 2)

def elementaryWord (a : BinaryCube) : A5 :=
  first ^ (a.toAdd 0).val * second ^ (a.toAdd 1).val

/-- The diagonal Klein group, together with the literal interchange. -/
def elementaryMap : BinaryCube →* Model where
  toFun a := ⟨((elementaryWord a).val, (elementaryWord a).val),
    Multiplicative.ofAdd (a.toAdd 2)⟩
  map_one' := SemidirectProduct.ext (by decide +kernel) rfl
  map_mul' a b := by
    have hw : ∀ a b : BinaryCube, elementaryWord (a*b) = elementaryWord a * elementaryWord b :=
      by decide +kernel
    have hs : ∀ (c : C2) (d : S5), switch S5 c (d,d) = (d,d) := by
      intro c d
      by_cases hc : c = 1 <;> simp [switch, hc]
    apply SemidirectProduct.ext
    · change ((elementaryWord (a*b)).val, (elementaryWord (a*b)).val) =
        ((elementaryWord a).val, (elementaryWord a).val) *
          switch S5 _ ((elementaryWord b).val, (elementaryWord b).val)
      rw [hs, hw]
      rfl
    · rfl

lemma elementaryMap_injective : Function.Injective elementaryMap := by
  have ht : ∀ a b : BinaryCube, elementaryWord a = elementaryWord b →
      a.toAdd 2 = b.toAdd 2 → a = b := by decide +kernel
  intro a b h
  exact ht a b (Subtype.ext (congrArg (fun g : Model => g.left.1) h))
    (congrArg (fun g : Model => g.right.toAdd) h)

def elementary : Subgroup Model := elementaryMap.range

noncomputable def elementaryEquiv : BinaryCube ≃* elementary :=
  MonoidHom.ofInjective elementaryMap_injective

lemma elementary_card : Nat.card elementary = 8 := by
  rw [← Nat.card_congr elementaryEquiv.toEquiv]
  norm_num [Nat.card_eq_fintype_card]

instance elementary_abelian : IsElementaryAbelian 2 elementary where
  toIsMulCommutative := by
    constructor
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := elementaryEquiv.surjective a
    obtain ⟨b, rfl⟩ := elementaryEquiv.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro a
    obtain ⟨a, rfl⟩ := elementaryEquiv.surjective a
    rw [← map_pow]
    have h : a ^ 2 = 1 := by
      have h : ∀ a : BinaryCube, a ^ 2 = 1 := by decide +kernel
      exact h a
    rw [h, map_one])

lemma elementary_first : pairedInclusion (first, first) ∈ elementary :=
  ⟨Multiplicative.ofAdd ![1,0,0], SemidirectProduct.ext (by decide +kernel) rfl⟩

lemma elementary_second : pairedInclusion (second, second) ∈ elementary :=
  ⟨Multiplicative.ofAdd ![0,1,0], SemidirectProduct.ext (by decide +kernel) rfl⟩

lemma elementary_interchange : (interchange : Model) ∈ elementary :=
  ⟨Multiplicative.ofAdd ![0,0,1], SemidirectProduct.ext (by decide +kernel) rfl⟩

lemma elementary_even (g : elementary) :
    g.val.left.1 ∈ A5 ∧ g.val.left.2 ∈ A5 := by
  obtain ⟨a, ha⟩ := g.property
  rw [← ha]
  exact ⟨(elementaryWord a).property, (elementaryWord a).property⟩

lemma elementary_le_extension :
    elementary ≤ pairedInclusion.range ⊔ Subgroup.zpowers (interchange : Model) := by
  rintro g ⟨a, rfl⟩
  have hbase : base ((elementaryWord a).val, (elementaryWord a).val) ∈
      pairedInclusion.range := ⟨(elementaryWord a, elementaryWord a), rfl⟩
  have ht : SemidirectProduct.inr (Multiplicative.ofAdd (a.toAdd 2)) ∈
      Subgroup.zpowers (interchange : Model) := by
    have h : a.toAdd 2 = 0 ∨ a.toAdd 2 = 1 := by
      have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      exact h _
    rcases h with h | h
    · rw [h]
      exact (Subgroup.zpowers (interchange : Model)).one_mem
    · rw [h]
      exact Subgroup.mem_zpowers _
  change (⟨((elementaryWord a).val, (elementaryWord a).val),
    Multiplicative.ofAdd (a.toAdd 2)⟩ : Model) ∈ _
  rw [SemidirectProduct.mk_eq_inl_mul_inr]
  exact Subgroup.mul_mem_sup hbase ht

lemma elementary_fixed_point (v : PairedFive.Space) (hv : v ≠ 0)
    (hf : ∀ g ∈ elementary, modelAction g v = v) : v = PairedFive.point := by
  apply PairedFive.eq_point_of_fixed v hv
  · simpa only [modelAction_paired] using hf _ elementary_first
  · simpa only [modelAction_paired] using hf _ elementary_second
  · simpa only [modelAction_interchange] using hf _ elementary_interchange

end BinaryPermutation.TerminalOrthogonal.PairedBorel
