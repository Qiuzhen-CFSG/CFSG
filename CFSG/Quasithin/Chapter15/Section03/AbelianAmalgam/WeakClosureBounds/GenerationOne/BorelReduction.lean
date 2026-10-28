module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.Quotients
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.Residual
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.RankOneTori
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.ModelTori
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.LinearModels
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.LinearCases

/-!
# Borel torus transfer in the generation-one argument

The group-theoretic transfer is complete: component generation gives the
residual orbit; a concrete torus in a specified model Borel gives an injection
into the actual image of `M ∩ O²(H)` in `H/O₂(H)`; and the no-three hypothesis
forces the field exponent to be odd. The source quotient `H/J` is retained
throughout. No splitting of its central kernel is assumed.

The final theorem reduces all six genuine E.2.2 alternatives under n(H)>1,
constructs the torus in every surviving model, and proves that its field
exponent f=n(H)>1 is odd. It retains every surviving source clause, including
the relative C-component, quasisimplicity of K/O₂(K), the diagram action,
the exchanged-component product, the SQTK quotient, and the central kernel.
The linear comparisons identify the actual SL₂ and, after oddness, SL₃
Borels. Sp₄ retains the source's derived-group convention.

This conditional part of 15.3.65 takes the preceding minimal-parabolic
conclusion, the full E.2.2 conclusion, and 15.3.49(4)'s no-three assertion as
explicit inputs. The parent must establish these from its source hypotheses;
no torus, divisibility, field parity, or reduced alternative is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
E.2.2, printed pp.215–216, and 15.3.65, printed p.1152.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
open Subgroup ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- Transport through a genuine component model and its Borel identification.
The component's inclusion in the residual is derived from its generation
clause. The resulting map has the codomain required by `Setup`. -/
theorem component_model_torus
    {F X : Type*} [Field F] [Finite F] [Group X]
    {H M K T : Subgroup G} (B : Subgroup X)
    (hgen : H = K ⊔ T) (hT : IsPGroup 2 T)
    (hK : (K.subgroupOf H).IsCComponent)
    (hcore : pCore 2 H ≤ sourceKernel H M)
    (e : sourceImage H M K ≃* X)
    (hB : ((sourceImage H M (M ⊓ K)).subgroupOf (sourceImage H M K)).map
      e.toMonoidHom = B)
    (i : Fˣ →* B) (hi : Function.Injective i) :
    ∃ j : Fˣ →* borelImage H M, Function.Injective j := by
  have hKR : K ≤ residual H := by
    rw [residual_eq_conjugateSpanBy_of_component hgen hT hK]
    exact le_conjugateSpanBy K T
  exact lift_component_borel_torus B hcore hKR (componentBorelEquiv B e hB) i hi

/-- The field restriction from a concrete Borel torus and 15.3.49(4).
The torus divisor is proved in the actual overlap. -/
theorem odd_of_component_model_borel
    {F X : Type*} [Field F] [Finite F] [Group X]
    {H M K T : Subgroup G} {f : ℕ} (B : Subgroup X)
    (hgen : H = K ⊔ T) (hT : IsPGroup 2 T)
    (hK : (K.subgroupOf H).IsCComponent)
    (hcore : pCore 2 H ≤ sourceKernel H M)
    (e : sourceImage H M K ≃* X)
    (hB : ((sourceImage H M (M ⊓ K)).subgroupOf (sourceImage H M K)).map
      e.toMonoidHom = B)
    (hF : Nat.card F = 2 ^ f)
    (i : Fˣ →* B) (hi : Function.Injective i)
    (hthree : ¬ 3 ∣ Nat.card (M ⊓ H : Subgroup G)) : Odd f := by
  obtain ⟨j, hj⟩ := component_model_torus B hgen hT hK hcore e hB i hi
  exact odd_field_exponent_of_borel_torus hF j hj hthree

/-- A concrete linear case, with no supplied torus or divisor. Recognition
and the equality of the named Borel with the transported overlap remain the
explicit source inputs. -/
theorem psl2_component_model_torus
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {H M K T : Subgroup G}
    (hgen : H = K ⊔ T) (hT : IsPGroup 2 T)
    (hK : (K.subgroupOf H).IsCComponent)
    (hcore : pCore 2 H ≤ sourceKernel H M)
    (e : sourceImage H M K ≃* BenderSuzuki.Converse.PSL2 F)
    (hB : ((sourceImage H M (M ⊓ K)).subgroupOf (sourceImage H M K)).map
      e.toMonoidHom = BenderSuzuki.Converse.PBorel F) :
    ∃ j : Fˣ →* borelImage H M, Function.Injective j :=
  component_model_torus _ hgen hT hK hcore e hB psl2Torus psl2Torus_injective

omit [Finite G] in
/-- The constructed torus supplies the source order divisor. -/
theorem HasBorelTorus.dvd_intersection {H M : Subgroup G} {f : ℕ}
    (h : HasBorelTorus H M f) : 2 ^ f - 1 ∣ Nat.card (M ⊓ H : Subgroup G) := by
  obtain ⟨F, hF, hfin, hcard, j, hj⟩ := h
  exact torus_dvd_intersection hcard j hj

omit [Finite G] in
/-- Field parity follows from the constructed injection and the actual overlap. -/
theorem HasBorelTorus.odd {H M : Subgroup G} {f : ℕ}
    (h : HasBorelTorus H M f)
    (hthree : ¬ 3 ∣ Nat.card (M ⊓ H : Subgroup G)) : Odd f := by
  obtain ⟨F, hF, hfin, hcard, j, hj⟩ := h
  exact odd_field_exponent_of_borel_torus hcard j hj hthree

/-- Output of the Borel step, retaining all the source model and kernel clauses.
The homomorphism is into the literal residual overlap in H/O₂(H). -/
structure OddReduction (𝒦 : GroupClass) (H M K T : Subgroup G) (f : ℕ) : Prop
    extends SourceCases.Reduction 𝒦 H M K T f where
  torus : HasBorelTorus H M f
  exponent_odd : Odd f
  linear_cases : SourceCases.LinearCases H M K T f

/-- Assemble the first paragraph on p.1152 from the full E.2.2 output.
The parent discharges `hP` (the preceding minimal-parabolic result), `hsource`
(E.2.2 after proving SQTK and nonsolvability), and `hthree` (15.3.49(4)).
The strict generation bound selects the cases; it does not supply parity. -/
theorem reduce_of_full_e22_and_no_three
    {𝒦 : GroupClass} {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hn : 1 < generationParameter H)
    (hsource : SourceCases.FullE22Conclusion 𝒦 H M (T : Subgroup G))
    (hthree : ¬ 3 ∣ Nat.card (M ⊓ H : Subgroup G)) :
    ∃ (K : Subgroup G) (f : ℕ), OddReduction 𝒦 H M K (T : Subgroup G) f := by
  obtain ⟨K, f, h⟩ := SourceCases.reduce_of_full_e22 hH hP hn hsource
  have ht := h.borel_torus
  have hf := ht.odd hthree
  exact ⟨K, f, h, ht, hf, h.cases.linear hf⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
