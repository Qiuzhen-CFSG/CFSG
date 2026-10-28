module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.Frattini.PGroup

/-!
# Odd root images detected on the actual Frattini quotient

Coprime faithfulness embeds an odd cyclic root-action image in the
Frattini-quotient automorphism group. If that elementary quotient has odd
binary dimension and the image has order q-1, the Singer-normalizer theorem
makes an involutory normalizer trivial on the quotient. Faithfulness then
makes it centralize the entire root-action image. No assertion that it is
trivial on the original nonabelian root is needed.

Source: Fong--Seitz I (1973), the Suzuki direction of the common-field
argument in (6H)(a), p.51. SuzukiActions applies this on the same source
quotient and discharges all action and cardinality premises.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource.RootAction

/-- The reflection need only be trivial on the Frattini quotient. Coprime
faithfulness then makes it centralize the entire odd root-action image. -/
theorem involution_centralizes_odd_image {E : Type*} [Group E] [Finite E]
    (hE : IsPGroup 2 E) (C : Subgroup (MulAut E)) [IsCyclic C]
    (ho : Nat.Coprime (Nat.card C) 2) {d : ℕ} (hd : Odd d)
    (hC : Nat.card C = 2^d-1) (hV : Nat.card (E ⧸ frattini E) = 2^d)
    (t : MulAut E) (ht : t^2 = 1) (hn : t ∈ normalizer (C : Set (MulAut E))) :
    t ∈ centralizer (C : Set (MulAut E)) := by
  let : Fact (IsPGroup 2 E) := ⟨hE⟩
  let : IsElementaryAbelian 2 (E ⧸ frattini E) := isElementaryAbelian_quotient_frattini
  let q := quotientAut (frattini E)
  let D := C.map q
  have hf := MonoidHom.injective_frattini_action_of_coprime hE C.subtype C.subtype_injective ho
  let f := q.subgroupMap C
  have hfinj : Function.Injective f := by
    intro a b hab
    exact hf (congrArg Subtype.val hab)
  let := isCyclic_of_surjective f (q.subgroupMap_surjective C)
  have hcD : Nat.card D = 2^d-1 := by
    rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfinj,q.subgroupMap_surjective C⟩),hC]
  have hqt2 : (q t)^2 = 1 := by rw [← map_pow,ht,map_one]
  have hqn : q t ∈ normalizer (D : Set _) :=
    C.le_normalizer_map q (mem_map_of_mem q hn)
  have hqt : q t = 1 := involution_eq_one D hd hcD hV _ hqt2 hqn
  rw [mem_centralizer_iff]
  intro c hc
  have hmem := (mem_normalizer_iff.mp hn c).mp hc
  have he : t*c*t⁻¹ = c := by
    apply congrArg Subtype.val (hf (a₁ := ⟨t*c*t⁻¹,hmem⟩) (a₂ := ⟨c,hc⟩) ?_)
    change q (t*c*t⁻¹) = q c
    rw [map_mul,map_mul,map_inv,hqt,one_mul,inv_one,mul_one]
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource.RootAction
