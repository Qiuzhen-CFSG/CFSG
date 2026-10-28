module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Actions
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Fixed spaces and the strict native cocode flag

The relative normality of A0 = K ∩ L makes its ambient fixed space Q-invariant.
If this space supplemented V6, every A0 displacement would lie in the tetrad
line. An earlier inner involution has displacement rank four, excluding that
supplement. Irreducibility of the top section therefore places V2 inside V6.
The transvection pairing now gives dimensions one and two and identifies W1
with V1; the geometric dimension six gives strictness of the complete flag.

For a hyperplane containing a source involution with five fixed dimensions,
all fixed vectors lie in V6, so its ambient fixed dimension is two. Selecting
such an involution in every hyperplane other than A0, and chiefness of the
four-dimensional middle factor, remain separate conjugation-module deductions.
Source: Aschbacher--Smith H.15.4, printed p.400, using H.14.3--4 and H.15.3.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace MathieuCode.M22Quintet.CocodeTransfer
open DualAction

/-- The source distinguished hyperplane is the intersection with the inner group. -/
abbrev A0 := K ⊓ L

/-- Earlier relative normality, order, and inner-involution fixed dimension. -/
structure InnerInputs : Prop where
  normalizer : Q ≤ Subgroup.normalizer (A0 : Set m22PairStabilizer)
  index : A0.relIndex K = 2
  involution_fixed : ∀ i ∈ A0, orderOf i = 2 →
    Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i)) = 6

theorem card_hyperplane (D : SextetTransvectionInputs)
    (A : Subgroup m22PairStabilizer) (hA : A ≤ K) (hi : A.relIndex K = 2) :
    Nat.card A = 16 := by
  have hc := (A.subgroupOf K).card_mul_index
  have he : Nat.card (A.subgroupOf K) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  rw [he, D.card_kernel] at hc
  change Nat.card A * A.relIndex K = 32 at hc
  rw [hi] at hc
  omega

theorem finrank_middle_fixed_hyperplane (D : SextetTransvectionInputs)
    [IsElementaryAbelian 2 K] (A : Subgroup m22PairStabilizer)
    (hA : A ≤ K) (hi : A.relIndex K = 2) :
    Module.finrank (ZMod 2)
      ((fixedSpace m22OuterCocodeRepresentation A).comap V6.subtype) = 2 := by
  let : IsElementaryAbelian 2 A :=
    { is_comm := ⟨fun a b => Subtype.ext (congrArg (fun k : K => k.val)
        (mul_comm (⟨a.val,hA a.property⟩ : K) ⟨b.val,hA b.property⟩))⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a.val (hA a.property))) }
  have hd := finrank_middle_fixed_add D A hA 4 (by simpa using card_hyperplane D A hA hi)
  omega

def V2Subrepresentation (I : InnerInputs) :
    Subrepresentation (m22OuterCocodeRepresentation.comp Q.subtype) where
  toSubmodule := V2
  apply_mem_toSubmodule g v hv :=
    (fixedSpace_stable_of_normalizes m22OuterCocodeRepresentation I.normalizer g.property v).mpr hv

/-- An irreducible top would force an extra fixed supplement to kill too much displacement. -/
theorem V2_le_V6 (D : SextetTransvectionInputs) (I : InnerInputs)
    [IsElementaryAbelian 2 K]
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation] : V2 ≤ V6 := by
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient
    V6Subrepresentation (V2Subrepresentation I) with h | h
  · exact h
  have hc := card_hyperplane D A0 inf_le_left I.index
  have hn : A0 ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hc
    omega
  obtain ⟨i,hi⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  have hin : i.val ≠ 1 := by exact fun he => hi (Subtype.ext he)
  have ho : orderOf i.val = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian i.val i.property.1) hin
  let f : M22Cocode →ₗ[ZMod 2] M22Cocode := m22OuterCocodeRepresentation i.val - LinearMap.id
  have hr : f.range ≤ W1 := by
    rintro _ ⟨v,rfl⟩
    have hv : v ∈ V6 ⊔ V2 := by rw [show V6 ⊔ V2 = ⊤ from h]; trivial
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
    have hwfix : m22OuterCocodeRepresentation i.val w = w := hw i
    change m22OuterCocodeRepresentation i.val (u+w) - (u+w) ∈ W1
    rw [map_add, hwfix]
    convert displacement_mem_W1 i.val
      (D.displacement i.val.val (D.kernel_le i.property.1)) u hu using 1; abel
  have hb := Submodule.finrank_mono hr
  rw [finrank_W1] at hb
  have hd := fixedCodim_zpowers_eq_displacement_rank m22OuterCocodeRepresentation i.val
  have hf := fixedCodim_add_finrank m22OuterCocodeRepresentation (Subgroup.zpowers i.val)
  rw [I.involution_fixed i.val i.property ho, finrank_m22Cocode, hd] at hf
  change Module.finrank (ZMod 2) f.range + 6 = 10 at hf
  omega

theorem finrank_V2 (D : SextetTransvectionInputs) (I : InnerInputs)
    [IsElementaryAbelian 2 K]
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation] :
    Module.finrank (ZMod 2) V2 = 2 := by
  have hd := finrank_middle_fixed_hyperplane D A0 inf_le_left I.index
  have he := (Submodule.comapSubtypeEquivOfLe (V2_le_V6 D I)).finrank_eq
  exact he.symm.trans hd

theorem W1_eq_V1 (D : SextetTransvectionInputs) (I : InnerInputs)
    [IsElementaryAbelian 2 K]
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation] : W1 = V1 := by
  apply le_antisymm
  · intro v hv k
    exact W1_fixed (kernelInclusion k) v hv
  · intro v hv
    have hv6 := V2_le_V6 D I (V1_le_V2 hv)
    exact (middle_fixed_eq_geometricCenter D).le (show (⟨v,hv6⟩ : V6) ∈
      V1.comap V6.subtype from hv)

theorem finrank_V1 (D : SextetTransvectionInputs) (I : InnerInputs)
    [IsElementaryAbelian 2 K]
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation] :
    Module.finrank (ZMod 2) V1 = 1 := by rw [← W1_eq_V1 D I, finrank_W1]

theorem cocode_flag_strict (D : SextetTransvectionInputs) (I : InnerInputs)
    [IsElementaryAbelian 2 K]
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation] :
    (⊥ : Submodule (ZMod 2) M22Cocode) < V1 ∧ V1 < V2 ∧ V2 < V6 ∧ V6 < ⊤ := by
  have h1 := finrank_V1 D I
  have h2 := finrank_V2 D I
  have h6 := finrank_V6
  refine ⟨lt_of_le_of_ne bot_le ?_, lt_of_le_of_ne V1_le_V2 ?_,
    lt_of_le_of_ne (V2_le_V6 D I) ?_, lt_of_le_of_ne le_top ?_⟩
  all_goals
    intro he
    have hd := congrArg (fun W : Submodule (ZMod 2) M22Cocode => Module.finrank (ZMod 2) W) he
    try simp only [finrank_bot, finrank_top, finrank_m22Cocode] at hd
    omega

/-- A source involution fixing five ambient dimensions has no fixed vector outside V6. -/
theorem involution_fixed_le_V6 (D : SextetTransvectionInputs)
    (i : m22PairStabilizer) (hi : i ∈ K) (ho : orderOf i = 2)
    (hfix : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i)) = 5) :
    fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i) ≤ V6 := by
  let : IsElementaryAbelian 2 (Subgroup.zpowers i) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (orderOf_eq_prime_iff.mp ho).1
  have hd := finrank_middle_fixed_add D (Subgroup.zpowers i)
    (Subgroup.zpowers_le.mpr hi) 1 (by rw [Nat.card_zpowers, ho]; rfl)
  let F := fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i)
  have he : F ⊓ V6 = F := by
    apply Submodule.eq_of_le_of_finrank_eq inf_le_left
    have hdim : Module.finrank (ZMod 2) (F.comap V6.subtype) =
        Module.finrank (ZMod 2) (F ⊓ V6 : Submodule (ZMod 2) M22Cocode) := by
      rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]
    change Module.finrank (ZMod 2) F = 5 at hfix
    rw [hdim] at hd
    omega
  exact he.ge.trans inf_le_right

/-- The outer-hyperplane branch after selecting its source involution.
Existence of that involution is a separate H.14 conjugation-module deduction. -/
theorem finrank_fixed_hyperplane_of_involution (D : SextetTransvectionInputs)
    [IsElementaryAbelian 2 K] (A : Subgroup m22PairStabilizer)
    (hA : A ≤ K) (hi : A.relIndex K = 2)
    (i : m22PairStabilizer) (hia : i ∈ A) (ho : orderOf i = 2)
    (hfix : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i)) = 5) :
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2 := by
  have hle : fixedSpace m22OuterCocodeRepresentation A ≤ V6 := by
    intro v hv
    apply involution_fixed_le_V6 D i (hA hia) ho hfix
    intro j
    exact hv ⟨j.val, (Subgroup.zpowers_le.mpr hia) j.property⟩
  exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.symm.trans
    (finrank_middle_fixed_hyperplane D A hA hi)

end MathieuCode.M22Quintet.CocodeTransfer
