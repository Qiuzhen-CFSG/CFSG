module
public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupAction.CoprimeFixedCardinality
public import Theory.GroupAction.SubgroupConjugation
public import Theory.Representation.BinaryOffender.Defs

/-!
# Coprime fixed points through marked binary sections

A fixed vector in a literal binary conjugation section lifts through its
coordinate kernel to an ambient centralizer element. Restricting the same
coordinate map then gives the fixed-order product formula. These lemmas
supply the Steinberg and natural fixed counts in the companion source
application, without postulating a centralizer-product identity.

Source: Aschbacher–Smith, proof of 14.7.73, printed pp.1076–1077;
the lifting theorem is the coprime quotient theorem in A.1.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting
variable {G D W : Type*} [Group G] [Finite G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Coprime lifting through the literal coordinate homomorphism. -/
theorem fixed_coordinates_lift {H A N B : Subgroup G}
    {q : H →* D} {ρ : Representation (ZMod 2) D W}
    (s : BinaryConjugationSection H A N (ρ.comp q))
    (hBH : B ≤ H) (hsolv : Group.IsSolvable A)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card A))
    (w : fixedSpace ρ ((B.subgroupOf H).map q)) :
    ∃ a : A, (a : G) ∈ centralizer (B : Set G) ∧ s.coordinates a = Multiplicative.ofAdd w.val := by
  let act := conjMulDistribMulActionOfLeNormalizer B A (hBH.trans s.normalized)
  let : MulDistribMulAction B A := act
  have he (b : B) (a : A) : (s.coordinates (b • a)).toAdd =
      ρ (q (inclusion hBH b)) (s.coordinates a).toAdd := s.equivariant (inclusion hBH b) a
  have hInv : IsInvariant B A s.coordinates.ker := by
    constructor
    intro b a
    change s.coordinates a = 1 ↔ s.coordinates (b • a) = 1
    constructor
    · intro ha
      apply Multiplicative.toAdd.injective
      rw [he, ha]
      exact map_zero _
    · intro ha
      have hh := he b⁻¹ (b • a)
      rw [inv_smul_smul, ha] at hh
      change (s.coordinates a).toAdd = ρ (q (inclusion hBH b⁻¹)) 0 at hh
      rw [map_zero] at hh
      exact Multiplicative.toAdd.injective hh
  let : MulDistribMulAction B (A ⧸ s.coordinates.ker) :=
    quotientMulDistribMulAction s.coordinates.ker hInv
  obtain ⟨a, ha⟩ := s.onto (Multiplicative.ofAdd w.val)
  have hfixed : QuotientGroup.mk' s.coordinates.ker a ∈
      FixedPoints.subgroup B (A ⧸ s.coordinates.ker) := by
    intro b
    change QuotientGroup.mk' s.coordinates.ker (b • a) = QuotientGroup.mk' s.coordinates.ker a
    apply QuotientGroup.eq_iff_div_mem.mpr
    change s.coordinates ((b • a) / a) = 1
    rw [map_div, div_eq_one]
    apply Multiplicative.toAdd.injective
    rw [he, ha]
    exact w.property ⟨q (inclusion hBH b), mem_map_of_mem q b.property⟩
  rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hsolv hcop
    s.coordinates.ker hInv] at hfixed
  obtain ⟨a', ha', heq⟩ := hfixed
  refine ⟨a', mem_centralizer_iff.mpr ?_, ?_⟩
  · intro b hb
    have hh := congrArg Subtype.val (ha' ⟨b, hb⟩)
    change b * (a' : G) * b⁻¹ = (a' : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · have hh := QuotientGroup.eq_iff_div_mem.mp heq
    change s.coordinates (a' / a) = 1 at hh
    rw [map_div, div_eq_one] at hh
    exact hh.trans ha

/-- Ambient fixed orders, retaining the original actor and coordinate map. -/
theorem fixed_coordinates_card {H A N B : Subgroup G}
    {q : H →* D} {ρ : Representation (ZMod 2) D W}
    (s : BinaryConjugationSection H A N (ρ.comp q))
    (hBH : B ≤ H) (hsolv : Group.IsSolvable A)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card A)) :
    Nat.card (A ⊓ centralizer (B : Set G) : Subgroup G) =
      Nat.card (fixedSpace ρ ((B.subgroupOf H).map q)) *
        Nat.card (N ⊓ centralizer (B : Set G) : Subgroup G) := by
  let C := A ⊓ centralizer (B : Set G)
  let X := fixedSpace ρ ((B.subgroupOf H).map q)
  let f : C →* Multiplicative X := {
    toFun := fun a => Multiplicative.ofAdd ⟨(s.coordinates ⟨a, a.property.1⟩).toAdd, by
      rintro ⟨_, h, hh, rfl⟩
      have hc : (h : G) * (a : G) * (h : G)⁻¹ = (a : G) :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp a.property.2 h hh)
      have he := s.equivariant h ⟨a, a.property.1⟩
      change _ = ρ (q h) _ at he
      rw [show (⟨(h : G) * (a : G) * (h : G)⁻¹, _⟩ : A) = ⟨a, a.property.1⟩ from
        Subtype.ext hc] at he
      exact he.symm⟩
    map_one' := by apply Multiplicative.toAdd.injective; apply Subtype.ext; exact s.coordinates.map_one
    map_mul' a b := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change (s.coordinates (⟨a, a.property.1⟩ * ⟨b, b.property.1⟩)).toAdd =
        (s.coordinates ⟨a, a.property.1⟩).toAdd + (s.coordinates ⟨b, b.property.1⟩).toAdd
      rw [map_mul]
      rfl }
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨a, ha, hw⟩ := fixed_coordinates_lift s hBH hsolv hcop w.toAdd
    refine ⟨⟨a, a.property, ha⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    exact Subtype.ext (congrArg Multiplicative.toAdd hw)
  let e : f.ker ≃ (N ⊓ centralizer (B : Set G) : Subgroup G) := {
    toFun := fun a => ⟨a.val, (s.coordinates_eq_one_iff _).mp
      (congrArg (fun w : Multiplicative X => Multiplicative.ofAdd w.toAdd.val) a.property), a.val.property.2⟩
    invFun := fun a => ⟨⟨a, s.kernel_le a.property.1, a.property.2⟩, by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact (s.coordinates_eq_one_iff _).mpr a.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    Nat.card_congr e] at hc
  exact hc
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting
