module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Definitions
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Source seed generation for the binary linear-three geometry

The seed is the literal image of V₃ in U_H/V₁, where U_H = ⟨V₃^H⟩.
An invariant subspace containing this seed contains the whole source module.
A two-group acting on its four-element seed fixes a nonzero vector; the
parabolic action transitive on the three nonzero seed vectors then makes
that vector cyclic for H*. Thus a compatible Sylow/parabolic marking gives
all the input conditions of the universally quantified H.6.5 statement.

For both external-component branches the same normal generation argument
proves Ũ_H = [Ũ_H,X*] from Ṽ₃ = [Ṽ₃,X*]. Only normality of X* in H*
is required. The action remains the actual source conjugation action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.6.5
(printed p.388), 13.8.19 and 13.8.21(1) (printed pp.953 and 956–957).
The source seed-action inputs and the compatible marking remain explicit.
These deductions do not construct that marking, classify the external
component, or assert either numbered source theorem.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- A seed element in the literal quotient U_H/V₁. -/
def seedVector (v : V₃) : Additive (Source.Utilde H V₃ V₁) :=
  Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
    ⟨v.val, le_conjugateSpanBy V₃ H v.property⟩)

/-- The source seed Ṽ₃, viewed as a binary subspace. -/
def seedSpace : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) :=
  Submodule.span (ZMod 2) (Set.range (seedVector H V₃ V₁))

/-- Source normal generation becomes linear generation under conjugation. -/
theorem seedSpace_generates (act : SourceAction H V₃ V₁)
    (D : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)))
    (hD : ∀ g v, v ∈ D → act.representation g v ∈ D)
    (hseed : seedSpace H V₃ V₁ ≤ D) : D = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  change Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) ∈ D
  rcases u with ⟨u, hu⟩
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨h, hh, z, hz, rfl⟩
    have hs : seedVector H V₃ V₁ ⟨z,hz⟩ ∈ D :=
      hseed (Submodule.subset_span ⟨⟨z,hz⟩, rfl⟩)
    have hm := hD (QuotientGroup.mk' (pCore 2 H) ⟨h,hh⟩) _ hs
    rw [seedVector, act.conjugation] at hm
    exact hm
  | one => exact D.zero_mem
  | mul x y hx hy ihx ihy =>
    exact D.add_mem ihx ihy
  | inv x hx ih => exact D.neg_mem ih
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
variable {A U : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]
/-- Linear span of the orbit of a vector under the specified subgroup. -/
def orbitSpan (ρ : Representation (ZMod 2) A U) (P : Subgroup A) (m : U) :
    Submodule (ZMod 2) U :=
  Submodule.span (ZMod 2) {v | ∃ p ∈ P, ρ p m = v}

theorem orbitSpan_stable (ρ : Representation (ZMod 2) A U) (P : Subgroup A)
    (m : U) (g : A) (hg : g ∈ P) (v : U) (hv : v ∈ orbitSpan ρ P m) :
    ρ g v ∈ orbitSpan ρ P m := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with ⟨p,hp,rfl⟩
    apply Submodule.subset_span
    exact ⟨g*p, P.mul_mem hg hp, by simp only [map_mul, Module.End.mul_apply]⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using (orbitSpan ρ P m).add_mem ihx ihy
  | smul a v hv ih => simpa only [map_smul] using (orbitSpan ρ P m).smul_mem a ih

theorem orbitSpan_mono (ρ : Representation (ZMod 2) A U) (P Q : Subgroup A)
    (hPQ : P ≤ Q) (m : U) : orbitSpan ρ P m ≤ orbitSpan ρ Q m := by
  apply Submodule.span_mono
  rintro _ ⟨p,hp,rfl⟩
  exact ⟨p,hPQ hp,rfl⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
variable {A U : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

/-- A two-group acting on a four-element binary subspace fixes a nonzero vector. -/
theorem fixed_seed (ρ : Representation (ZMod 2) A U) (T : Subgroup A)
    (hT : IsPGroup 2 T) (D : Submodule (ZMod 2) U) (hcard : Nat.card D = 4)
    (hstable : ∀ t ∈ T, ∀ v ∈ D, ρ t v ∈ D) :
    ∃ m ∈ D, m ≠ 0 ∧ ∀ t ∈ T, ρ t m = m := by
  let : MulAction T D := {
    smul t v := ⟨ρ t.val v.val, hstable t.val t.property v.val v.property⟩
    one_smul v := Subtype.ext (show ρ 1 v.val = v.val by simp)
    mul_smul t s v := Subtype.ext (show ρ (t.val * s.val) v.val = ρ t.val (ρ s.val v.val) by
      simp only [map_mul, Module.End.mul_apply]) }
  have hz : (0 : D) ∈ MulAction.fixedPoints T D := by
    intro t
    apply Subtype.ext
    exact map_zero (ρ t.val)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hne⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point D
    (by rw [hcard]; decide) hz
  refine ⟨m.val, m.property, ?_, ?_⟩
  · intro he
    exact hne (Subtype.ext he.symm)
  · intro t ht
    exact congrArg Subtype.val (hm ⟨t,ht⟩)

omit [Finite U] in
theorem orbitSpan_eq_seed (ρ : Representation (ZMod 2) A U) (P : Subgroup A)
    (D : Submodule (ZMod 2) U)
    (hstable : ∀ p ∈ P, ∀ v ∈ D, ρ p v ∈ D)
    (htrans : ∀ u ∈ D, u ≠ 0 → ∀ v ∈ D, v ≠ 0 → ∃ p ∈ P, ρ p u = v)
    (m : U) (hm : m ∈ D) (hne : m ≠ 0) : orbitSpan ρ P m = D := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    exact hstable p hp m hm
  · intro v hv
    by_cases hzero : v = 0
    · simpa only [hzero] using (orbitSpan ρ P m).zero_mem
    · exact Submodule.subset_span (htrans m hm hne v hv hzero)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
variable {G : Type*} [Group G] [Finite G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Construct a fixed cyclic vector from the source parabolic action on Ṽ₃. -/
theorem cyclic_seed (act : SourceAction H V₃ V₁)
    (T P : Subgroup (Source.Hstar H)) (hTP : T ≤ P) (hT : IsPGroup 2 T)
    (hcard : Nat.card (seedSpace H V₃ V₁) = 4)
    (hstable : ∀ p ∈ P, ∀ v ∈ seedSpace H V₃ V₁,
      act.representation p v ∈ seedSpace H V₃ V₁)
    (htrans : ∀ u ∈ seedSpace H V₃ V₁, u ≠ 0 →
      ∀ v ∈ seedSpace H V₃ V₁, v ≠ 0 → ∃ p ∈ P, act.representation p u = v) :
    ∃ m ∈ seedSpace H V₃ V₁, m ≠ 0 ∧
      (∀ t ∈ T, act.representation t m = m) ∧
      orbitSpan act.representation ⊤ m = ⊤ ∧
      orbitSpan act.representation P m = seedSpace H V₃ V₁ := by
  obtain ⟨m, hm, hne, hfixed⟩ := fixed_seed act.representation T hT
    (seedSpace H V₃ V₁) hcard (fun t ht => hstable t (hTP ht))
  have horbit := orbitSpan_eq_seed act.representation P (seedSpace H V₃ V₁)
    hstable htrans m hm hne
  refine ⟨m, hm, hne, hfixed, ?_, horbit⟩
  apply seedSpace_generates H V₃ V₁ act
  · exact fun g v hv => orbitSpan_stable act.representation ⊤ m g (Subgroup.mem_top g) v hv
  · rw [← horbit]
    exact orbitSpan_mono act.representation P ⊤ le_top m

theorem seed_finrank (hcard : Nat.card (seedSpace H V₃ V₁) = 4) :
    Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2 := by
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := seedSpace H V₃ V₁)
  rw [hcard, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card] at he
  exact Nat.pow_right_injective (by decide : 1 < 2) he.symm
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
variable {A B U : Type*} [Group A] [Group B] [AddCommGroup U] [Module (ZMod 2) U]

theorem orbitSpan_transport (ρ : Representation (ZMod 2) A U) (e : A ≃* B)
    (P : Subgroup A) (m : U) :
    orbitSpan (ρ.comp e.symm.toMonoidHom) (P.map e.toMonoidHom) m = orbitSpan ρ P m := by
  unfold orbitSpan
  congr 1
  ext v
  constructor
  · rintro ⟨p, ⟨q,hq,rfl⟩, hp⟩
    exact ⟨q,hq, by simpa using hp⟩
  · rintro ⟨p,hp,hv⟩
    exact ⟨e p, ⟨p,hp,rfl⟩, by simpa using hv⟩

/-- The universally quantified H.6.5 input, with its fixed Sylow and line
parabolic specified in the same concrete SL₃(2) coordinates as the five modules. -/
def H65Theorem : Prop :=
  ∀ (ρ : Representation (ZMod 2) BinaryLinearThree.Group U),
    Function.Injective ρ → ∀ m : U,
    (∀ t ∈ Matrix.PSL3Two.borelSL, ρ t m = m) →
    orbitSpan ρ ⊤ m = ⊤ →
    Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2 →
    H65Alternatives ρ
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Deduce the five module alternatives from a compatible source marking and
the universal earlier theorem H.6.5, rather than assuming the alternatives. -/
theorem H65_of_marking (act : SourceAction H V₃ V₁)
    (hfaith : Function.Injective act.representation)
    (h65 : H65Theorem (U := Additive (Source.Utilde H V₃ V₁)))
    (T P : Subgroup (Source.Hstar H)) (hTP : T ≤ P) (hT : IsPGroup 2 T)
    (hcard : Nat.card (seedSpace H V₃ V₁) = 4)
    (hstable : ∀ p ∈ P, ∀ v ∈ seedSpace H V₃ V₁,
      act.representation p v ∈ seedSpace H V₃ V₁)
    (htrans : ∀ u ∈ seedSpace H V₃ V₁, u ≠ 0 →
      ∀ v ∈ seedSpace H V₃ V₁, v ≠ 0 → ∃ p ∈ P, act.representation p u = v)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group)
    (hTe : T.map e.toMonoidHom = Matrix.PSL3Two.borelSL)
    (hPe : P.map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL) :
    H65Alternatives (act.representation.comp e.symm.toMonoidHom) := by
  obtain ⟨m, _, _, hfixed, hgen, horbit⟩ :=
    cyclic_seed H V₃ V₁ act T P hTP hT hcard hstable htrans
  apply h65 _ (fun a b h => e.symm.injective (hfaith h)) m
  · intro t ht
    rw [← hTe] at ht
    obtain ⟨s,hs,rfl⟩ := ht
    simpa using hfixed s hs
  · have he := orbitSpan_transport act.representation e ⊤ m
    rw [Subgroup.map_top_of_surjective _ e.surjective] at he
    exact he.trans hgen
  · rw [← hPe, orbitSpan_transport, horbit]
    exact seed_finrank H V₃ V₁ hcard

omit [Finite G] in
/-- The normality needed here is only normality of X* in H*. No normality
of X in the ambient group, or even in H, is imposed. -/
theorem normal_seed_generation (act : SourceAction H V₃ V₁) (X : Subgroup G)
    (hX : (Source.starImage H X).Normal)
    (hseed : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H X) = seedSpace H V₃ V₁) :
    subspaceCommutator act.representation ⊤ (Source.starImage H X) = ⊤ := by
  apply seedSpace_generates H V₃ V₁ act
  · have htop : (⊤ : Subgroup (Source.Hstar H)) ≤
        subspaceStabilizer act.representation ⊤ := by
      apply le_subspaceStabilizer
      intro a ha v hv
      exact Submodule.mem_top
    have hnorm : (⊤ : Subgroup (Source.Hstar H)) ≤
        normalizer (Source.starImage H X : Set (Source.Hstar H)) := by
      let := hX
      rw [Subgroup.normalizer_eq_top]
    have hs := subspaceCommutator_invariant_normalizer act.representation htop hnorm
    exact fun g v hv => (hs (Subgroup.mem_top g) v).2 hv
  · rw [← hseed]
    exact subspaceCommutator_mono_left act.representation le_top (Source.starImage H X)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Actual subgroup normalization gives invariance of the source seed image. -/
theorem seedSpace_invariant (act : SourceAction H V₃ V₁) (P : Subgroup G)
    (hP : P ≤ normalizer (V₃ : Set G)) :
    ∀ p ∈ Source.starImage H P, ∀ v ∈ seedSpace H V₃ V₁,
      act.representation p v ∈ seedSpace H V₃ V₁ := by
  rintro _ ⟨p,hp,rfl⟩ v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with ⟨z,rfl⟩
    rw [seedVector, act.conjugation]
    apply Submodule.subset_span
    refine ⟨⟨p.val * z.val * p.val⁻¹, ?_⟩, rfl⟩
    exact (mem_normalizer_iff.mp (hP hp) z.val).mp z.property
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (seedSpace H V₃ V₁).add_mem ihx ihy
  | smul a v hv ih =>
    simpa only [map_smul] using (seedSpace H V₃ V₁).smul_mem a ih
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
