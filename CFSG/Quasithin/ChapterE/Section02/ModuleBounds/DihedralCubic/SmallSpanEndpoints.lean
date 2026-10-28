module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration

/-!
# Cubic small-span endpoints

In the local section action used in E.2.17, a normal nontrivial 3-group and an
involution generate the acting group, the 3-group moves the whole binary
module, and the involution has fixed codimension at most two. The proved
D.2.17 small-support classification then gives only the cyclic order-three,
elementary order-nine, or extraspecial order-twenty-seven endpoints.

The prime-three hypothesis excludes the order-five row, and a module of order
at least sixteen excludes the two-dimensional order-three row. The resulting
endpoints retain the original subgroup and involution, including the models
and inversion statements. A representation consumer checks the complete
local-generation tuple on the unchanged module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
D.2.17 and the cubic small-span step of E.2.17.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.DihedralCubic
open ChapterD.Section02
universe u
variable {G E : Type u} [Group G] [Group E] [Finite G] [Finite E]
  [IsElementaryAbelian 2 E] [MulDistribMulAction G E]

omit [Finite G] [Finite E] in
private theorem cubic_rows (R : Subgroup G) [R.Normal] (t : G)
    (hp : IsPGroup 3 R) (hsize : 16 ≤ Nat.card E)
    (h : CyclicThreeEndpoint (V := E) R t ∨ CyclicFiveEndpoint (V := E) R t ∨
      ElementaryNineEndpoint (V := E) R t ∨ ExtraspecialEndpoint (V := E) R t) :
    (CyclicThreeEndpoint (V := E) R t ∧ Nat.card E = 16) ∨
      ElementaryNineEndpoint (V := E) R t ∨ ExtraspecialEndpoint (V := E) R t := by
  rcases h with h | h | h | h
  · left
    refine ⟨h,?_⟩
    rcases h.dimensions with hlow | hfour
    · omega
    · exact hfour.1
  · have hR : Nat.card R = 5 := by
      obtain ⟨e⟩ := h.kernel_equiv
      simpa using Nat.card_congr e.toEquiv
    have hfive : IsPGroup 5 R := IsPGroup.of_card (n := 1) (by simpa using hR)
    have hbot : R = ⊥ := disjoint_self.mp
      (hp.disjoint_of_coprime hfive (by decide : Nat.Coprime 3 5))
    rw [hbot,card_bot] at hR
    omega
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

omit [Finite G] [Finite E] in
private theorem cardinalities_of_rows (R : Subgroup G) [R.Normal] (t : G)
    (h : (CyclicThreeEndpoint (V := E) R t ∧ Nat.card E = 16) ∨
      ElementaryNineEndpoint (V := E) R t ∨ ExtraspecialEndpoint (V := E) R t) :
    (Nat.card E = 16 ∧ (Nat.card R = 3 ∨ Nat.card R = 9)) ∨
      (Nat.card E = 64 ∧ IsExtraspecial 3 R ∧ Nat.card R = 27) := by
  rcases h with ⟨h,hE⟩ | h | h
  · left
    refine ⟨hE,Or.inl ?_⟩
    obtain ⟨e⟩ := h.kernel_equiv
    simpa using Nat.card_congr e.toEquiv
  · exact Or.inl ⟨h.card_module,Or.inr h.card_kernel⟩
  · exact Or.inr ⟨h.card_module,h.kernel_extraspecial,h.card_kernel⟩

/-- Cubic small-support endpoints, retaining the actual subgroup and involution. -/
theorem small_span_endpoints [FaithfulSMul G E]
    (R : Subgroup G) [R.Normal] (hne : R ≠ ⊥) (hp : IsPGroup 3 R)
    (t : G) (ht : orderOf t = 2)
    (hgen : R ⊔ zpowers t = ⊤) (hc : ⁅R,zpowers t⁆ = R)
    (hm : commutatorAction R E = ⊤)
    (hi : (FixedPoints.subgroup (zpowers t) E).index ≤ 4)
    (hsize : 16 ≤ Nat.card E) :
    (CyclicThreeEndpoint (V := E) R t ∧ Nat.card E = 16) ∨
      ElementaryNineEndpoint (V := E) R t ∨ ExtraspecialEndpoint (V := E) R t := by
  have hodd : Nat.Coprime 2 (Nat.card R) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  have ht' : IsInvolution t :=
    ⟨fun he => by simp [he] at ht, ht ▸ pow_orderOf_eq_one t⟩
  have hf : fixingSubgroup G (Set.univ : Set E) = ⊥ := by
    apply bot_unique
    intro g hg
    apply eq_of_smul_eq_smul (α := E)
    intro e
    simpa only [one_smul] using
      ((mem_fixingSubgroup_iff (M := G)).mp hg e (Set.mem_univ e))
  exact cubic_rows R t hp hsize
    (smallSupportClassification_of_index_le_four R hne 3 hp hodd t ht' hgen hc hm hi hf)

/-- The cubic small span has order sixteen or sixty-four, with its marked kernel. -/
theorem small_span_cardinalities [FaithfulSMul G E]
    (R : Subgroup G) [R.Normal] (hne : R ≠ ⊥) (hp : IsPGroup 3 R)
    (t : G) (ht : orderOf t = 2)
    (hgen : R ⊔ zpowers t = ⊤) (hc : ⁅R,zpowers t⁆ = R)
    (hm : commutatorAction R E = ⊤)
    (hi : (FixedPoints.subgroup (zpowers t) E).index ≤ 4)
    (hsize : 16 ≤ Nat.card E) :
    (Nat.card E = 16 ∧ (Nat.card R = 3 ∨ Nat.card R = 9)) ∨
      (Nat.card E = 64 ∧ IsExtraspecial 3 R ∧ Nat.card R = 27) :=
  cardinalities_of_rows R t (small_span_endpoints R hne hp t ht hgen hc hm hi hsize)

end CFSG.Quasithin.ChapterE.DihedralCubic

namespace CFSG.Quasithin.ChapterE.DihedralCubic
open ChapterD.Section02 ChapterD.CyclicSource Representation.BinaryOffender
universe u
variable {G W : Type u} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) G W}

/-- A cubic local-generation witness gives marked endpoints on the original module. -/
theorem local_generation_cubic_endpoints (d : LocalGeneration ρ)
    (hp : d.prime = 3) (hf : Function.Injective ρ) (hsize : 16 ≤ Nat.card W) :
    letI := BinaryGroupAction.action ρ
    letI : Finite W := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
    letI := d.normal
    (CyclicThreeEndpoint (V := Multiplicative W) d.kernel d.involution ∧ Nat.card W = 16) ∨
      ElementaryNineEndpoint (V := Multiplicative W) d.kernel d.involution ∨
      ExtraspecialEndpoint (V := Multiplicative W) d.kernel d.involution := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let := d.normal
  exact cubic_rows d.kernel d.involution (hp ▸ d.pgroup) hsize (d.endpoints hf)

/-- Numeric cubic rows for a local-generation witness on the original representation. -/
theorem local_generation_cubic_cardinalities (d : LocalGeneration ρ)
    (hp : d.prime = 3) (hf : Function.Injective ρ) (hsize : 16 ≤ Nat.card W) :
    (Nat.card W = 16 ∧ (Nat.card d.kernel = 3 ∨ Nat.card d.kernel = 9)) ∨
      (Nat.card W = 64 ∧ IsExtraspecial 3 d.kernel ∧ Nat.card d.kernel = 27) := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let := d.normal
  exact cardinalities_of_rows (E := Multiplicative W) d.kernel d.involution
    (local_generation_cubic_endpoints d hp hf hsize)

/-- The original cubic source tuple supplies every local-generation field on the
unchanged representation; no ambient model identification is required. -/
theorem small_span_representation_cardinalities
    (R : Subgroup G) [R.Normal] (hne : R ≠ ⊥) (hp : IsPGroup 3 R)
    (t : G) (ht : orderOf t = 2)
    (hgen : R ⊔ zpowers t = ⊤) (hc : ⁅R,zpowers t⁆ = R)
    (hm : subspaceCommutator ρ ⊤ R = ⊤)
    (hi : fixedCodim ρ (zpowers t) ≤ 2)
    (hf : Function.Injective ρ) (hsize : 16 ≤ Nat.card W) :
    (Nat.card W = 16 ∧ (Nat.card R = 3 ∨ Nat.card R = 9)) ∨
      (Nat.card W = 64 ∧ IsExtraspecial 3 R ∧ Nat.card R = 27) := by
  let d : LocalGeneration ρ :=
    { kernel := R
      normal := inferInstance
      prime := 3
      prime_prime := Nat.prime_three
      prime_odd := by decide
      pgroup := hp
      nontrivial := hne
      involution := t
      order_two := ht
      generated := hgen
      commutator := hc
      moved := hm
      codimension := hi }
  exact local_generation_cubic_cardinalities d rfl hf hsize

end CFSG.Quasithin.ChapterE.DihedralCubic
