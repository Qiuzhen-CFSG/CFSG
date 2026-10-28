module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Models

/-!
# The point-radical/root product in the binary flag stabilizer

In the ordered coordinate frame (e₀,e₁,e₂), the radical at e₀ times the
root group with center e₁ and axis ⟨e₀,e₁⟩ is the upper triangular Sylow
subgroup. The second radical and plane fixer are literal matrix subgroups.
Only eight upper triangular matrices are enumerated: their coverage follows
from the existing order-eight theorem and injectivity of their list.

Source: Aschbacher--Smith, G.2.5(1) and the application in 14.4.7,
printed pp.335,1009. The source frame is (V₁ᵍ,V₁,V₁ˡ).
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace Matrix.PSL3Two.SourceFlag
open MarkedAutomorphisms

/-- Radical with center the second coordinate point. -/
def secondRadical : Subgroup SL :=
  pointV.comap (MulAut.conj (Bruhat.perm 2)).toMonoidHom

/-- Pointwise fixer of the plane spanned by the first two coordinate vectors. -/
def planeFixer : Subgroup SL :=
  MulAction.stabilizer SL (![1, 0, 0] : Fano.Vector) ⊓
    MulAction.stabilizer SL (![0, 1, 0] : Fano.Vector)

theorem mem_planeFixer (x : SL) : x ∈ planeFixer ↔
    x.val.mulVec ![1, 0, 0] = ![1, 0, 0] ∧
    x.val.mulVec ![0, 1, 0] = ![0, 1, 0] := Iff.rfl

instance : DecidablePred (· ∈ secondRadical) := fun x =>
  inferInstanceAs (Decidable ((MulAut.conj (Bruhat.perm 2)) x ∈ pointV))
instance : DecidablePred (· ∈ planeFixer) := fun x =>
  decidable_of_iff _ (mem_planeFixer x).symm

/-- The root group with center e₁ and axis ⟨e₀,e₁⟩. -/
def root : Subgroup SL := secondRadical ⊓ planeFixer
instance : DecidablePred (· ∈ root) := fun x =>
  inferInstanceAs (Decidable (x ∈ secondRadical ∧ x ∈ planeFixer))

set_option maxRecDepth 10000 in
theorem radical_le_borel : pointV ≤ borelSL := by
  intro x hx
  exact (mem_borelSL_iff x).mpr ⟨hx.2.1, hx.2.2.1, hx.2.2.2.2.2.1⟩

set_option maxRecDepth 10000 in
theorem root_le_borel : root ≤ borelSL := by
  intro x hx
  obtain ⟨h₀,h₁⟩ := (mem_planeFixer x).mp hx.2
  have h10 := congrFun h₀ 1
  have h20 := congrFun h₀ 2
  have h21 := congrFun h₁ 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h10 h20 h21
  exact (mem_borelSL_iff x).mpr ⟨h10,h20,h21⟩

set_option maxRecDepth 10000 in
theorem upper_first (i : Fin 4) : Bruhat.upper ⟨i, by omega⟩ ∈ pointV := by
  revert i
  decide +kernel

set_option maxRecDepth 10000 in
theorem upper_last (i : Fin 2) : Bruhat.upper ⟨4 * i, by omega⟩ ∈ root := by
  revert i
  decide +kernel

set_option maxRecDepth 10000 in
theorem borel_factors : ∀ x : SL, x ∈ borelSL →
    ∃ i : Fin 4, ∃ j : Fin 2,
      x = Bruhat.upper ⟨i, by omega⟩ * Bruhat.upper ⟨4 * j, by omega⟩ := by
  intro x hx
  let u : Fin 8 → borelSL := fun i => ⟨Bruhat.upper i, Bruhat.upper_mem i⟩
  have hu : Function.Injective u := by
    have hi : Function.Injective Bruhat.upper := by decide +kernel
    exact fun i j hij => hi (congrArg Subtype.val hij)
  have hcard : Fintype.card (Fin 8) = Fintype.card borelSL := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_borelSL]
  obtain ⟨k,hk⟩ := ((Fintype.bijective_iff_injective_and_card u).mpr ⟨hu,hcard⟩).2 ⟨x,hx⟩
  have he : ∀ k : Fin 8, ∃ i : Fin 4, ∃ j : Fin 2,
      Bruhat.upper k = Bruhat.upper ⟨i, by omega⟩ * Bruhat.upper ⟨4 * j, by omega⟩ := by
    decide +kernel
  have hk' : Bruhat.upper k = x := congrArg Subtype.val hk
  rw [← hk']
  exact he k

theorem borel_product : (borelSL : Set SL) = (pointV : Set SL) * (root : Set SL) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,j,rfl⟩ := borel_factors x hx
    exact Set.mul_mem_mul (upper_first i) (upper_last j)
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact borelSL.mul_mem (radical_le_borel ha) (root_le_borel hb)

noncomputable def flagSylow : Sylow 2 SL := Sylow.ofCard borelSL (by
  rw [card_borelSL, card_SL]
  decide +kernel)

theorem eq_one_iff (x : SL) : x = 1 ↔ ∀ v : Fano.Vector, x.val.mulVec v = v := by
  constructor
  · rintro rfl v
    exact Matrix.one_mulVec v
  · intro h
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have hh := congrFun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply, eq_comm] using hh

theorem planeFixer_iff (x : SL) : x ∈ planeFixer ↔
    ∀ v : Fano.Vector, v 2 = 0 → x.val.mulVec v = v := by
  rw [mem_planeFixer]
  constructor
  · rintro ⟨h₀,h₁⟩ v hv
    have he : v = v 0 • (![1,0,0] : Fano.Vector) + v 1 • ![0,1,0] := by
      ext i
      fin_cases i <;> simp [hv]
    rw [he, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h₀, h₁]
  · intro h
    exact ⟨h _ (by decide), h _ (by decide)⟩

end Matrix.PSL3Two.SourceFlag
