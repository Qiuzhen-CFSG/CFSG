module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.ExceptionalCorank.OddExtension
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.ExceptionalCorank.PrimeField
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements

/-!
# The exceptional corank conclusion from the preceding source geometry

For H₁ in the literal H(L₁T,M), the hypothesis O²(H₁) ≤ K forces L₁ < K.
The full 11.1.2 alternatives, together with the triangle exclusion in
11.4.1(2), then leave exactly the two q=4 models. In the prime PSL₂ case
R₁ acts trivially on K/O₂(K). In the odd-extension case the preceding
11.4.1(3) radical calculation bounds every elementary action image by one.
The actual action kernel lies in O₂(H₁), which transfers this bound to
m(A/(A ∩ O₂(H₁))). No action bound or kernel containment is an input.

The full refinement and local quotient marking are preceding-source inputs
owned by qt-d-1222-natural-relative-components. Triangle exclusion and the
strict-component radical calculation are owned by qt-d-1222-shadow-components
(through qt-d-1222-shadow-component-triangle and
qt-d-1141-surviving-radical-bounds). In particular the latter must supply
both R₁ ≤ O∞(KT) and |O∞(KT):O₂,F(KT)| ≤ 2. The parent
qt-d-1222-natural-closure-cartan retains their discharge. These theorems
complete the corank deduction conditionally on that earlier geometry;
they do not assert that the partial ClassicalRefinementCase is exhaustive.

The odd-extension quotient is the literal iterated TwoOddQuotient K. No
splitting, restriction on the odd kernel, or ambient normality of K is used.
Source: Aschbacher--Smith, 11.1.2, printed p.761; 11.4.1, pp.775--776;
11.5.6(6), pp.780--781 (PDF pp.797--798).
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open LocalGeometry.Components

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The outside condition and the two-residual premise remove equality from
the full source alternatives. The preceding triangle exclusion leaves exactly
11.1.2(1--2), with q=4 and their original quotient and prime conditions. -/
theorem exceptional_models_of_residual_le (H : Subgroup G)
    (hH : H ∈ Chapter1.HOutside G ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G)
      (E.M : Set G))
    (hr : (pResidual 2 H).map H.subtype ≤ E.K)
    (href : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : E.input.field.degree = 2 →
      ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X) :
    E.input.field.degree = 2 ∧
      ((∃ p : ℕ, (p = 5 ∨ (p.Prime ∧ 11 ≤ p)) ∧
        Source.IsSL (Source.TwoOddQuotient E.K) 2 p) ∨
       (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧
        ClassicalGroup.IsPSL (E.K ⧸ pCore 2 E.K) 2 p ∧
        ¬ Source.IsSL (L ⧸ pCore 2 L) 3 4)) := by
  have hstrict := E.local_lt_closure_of_residual_le H hH hr
  cases href with
  | equal he => exact (hstrict.ne (by simpa using he)).elim
  | sl2 _ hn p hp hm => exact ⟨hn, Or.inl ⟨p, hp, hm⟩⟩
  | psl2 _ hn p hp hlarge hm hL => exact ⟨hn, Or.inr ⟨p, hp, hlarge, hm, hL⟩⟩
  | triangle _ hn ht => exact (htriangle hn ht).elim

/-- The actual R₁ action has elementary image rank at most one in both
surviving cases. The strict-component radical premise is precisely the
intermediate calculation in the proof of 11.4.1(3). -/
theorem radical_action_rank_of_source_geometry (H : Subgroup G)
    (hH : H ∈ Chapter1.HOutside G ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G)
      (E.M : Set G)) (hHG : H ≤ E.G₁)
    (hr : (pResidual 2 H).map H.subtype ≤ E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (href : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : E.input.field.degree = 2 →
      ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X)
    (hstructure : E.L₁ < E.K →
      E.R₁ ≤ (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)).map
        (E.K ⊔ (T : Subgroup G) : Subgroup G).subtype ∧
      (twoFittingCore (E.K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : A ≤ E.R₁) :
    Group.rank ((A.subgroupOf E.R₁).map
      (E.radicalCoreAction ((le_sup_right.trans hH.1.2).trans hHG))) ≤ 1 := by
  have hT : (T : Subgroup G) ≤ E.G₁ := (le_sup_right.trans hH.1.2).trans hHG
  obtain ⟨hn, hodd | hprime⟩ := E.exceptional_models_of_residual_le H hH hr href htriangle
  · obtain ⟨hR, hi⟩ := hstructure (E.local_lt_closure_of_residual_le H hH hr)
    exact E.radical_action_rank_of_preceding_radical_structure hT hR hi A hA
  · obtain ⟨p, hp, hlarge, hm, _⟩ := hprime
    have hlocal' : E.L₁ ≠ E.L₁.pCoreIn 2 :=
      E.local_ne_core_of_projective_quotient (by rw [hn]; norm_num) hlocal
    have hC := E.radical_centralizes_of_prime_projective_quotient hT hlocal'
      hp (by omega) hm
    have hk : (E.radicalCoreAction hT).ker = ⊤ := by
      apply top_unique
      intro r _
      have hrk : (r : G) ∈ (E.radicalCoreAction hT).ker.map E.R₁.subtype := by
        rw [E.radicalCoreAction_kernel_map hT]
        exact ⟨r.property, hC r.property⟩
      obtain ⟨s, hs, he⟩ := hrk
      exact (Subtype.ext he : s = r) ▸ hs
    have hz : (A.subgroupOf E.R₁).map (E.radicalCoreAction hT) = ⊥ := by
      apply bot_unique
      rintro _ ⟨r, _, rfl⟩
      exact MonoidHom.mem_ker.mp (hk ▸ mem_top r)
    rw [hz, Group.rank_eq_zero]
    exact Nat.zero_le _

/-- Source 11.5.6(6), conditional only on the displayed preceding 11.1--11.4
geometry. H is in the actual outside family inside G₁, the premise is O²(H)≤K,
and the conclusion uses the original A and O₂(H). Earlier-source discharge
remains with the parent closure assembly. -/
theorem elementary_corank_le_one_of_source_geometry (H : Subgroup G)
    (hH : H ∈ Chapter1.HOutside G ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G)
      (E.M : Set G)) (hHG : H ≤ E.G₁)
    (hr : (pResidual 2 H).map H.subtype ≤ E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (href : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : E.input.field.degree = 2 →
      ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X)
    (hstructure : E.L₁ < E.K →
      E.R₁ ≤ (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)).map
        (E.K ⊔ (T : Subgroup G) : Subgroup G).subtype ∧
      (twoFittingCore (E.K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : A ≤ E.R₁) :
    ChapterE.subgroupCorank A (A ⊓ H.pCoreIn 2) ≤ 1 := by
  exact E.elementary_corank_le_one_of_action_rank
    ((le_sup_right.trans hH.1.2).trans hHG) H hH.1.2 hHG hr A hA
    (E.radical_action_rank_of_source_geometry H hH hHG hr hlocal href htriangle hstructure A hA)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
