module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.EvenThirtyTwo
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.Sporadic
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentModels
/-!
# The complete Theorem C catalogue for a wreathed Sylow of order thirty-two

Exponent at most eight excludes odd rank one, and noncommutativity excludes
binary rank one. The even and sporadic order sieves eliminate their other
constructors, with the actual binary G₂ derived group becoming PSU₃(3).
Thus precisely prime-field PSL₃ and PSU₃ models remain.

The component consumer applies genuine A/C through the original SQTK cover
and transports the actual central projection. Its exact component Sylow
order is the earlier source comparison supplied by the degree-three branch;
no field model or classification conclusion is an input.
Source: Aschbacher–Smith F.6.18(10), printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
variable {G : Type*} [Group G] [Finite G]
theorem theoremC_degree_three_of_sylow32
    (P : Sylow 2 G) (hP : Nat.card P = 32)
    (hexp : ∀ x : P, x ^ 8 = 1) (hnc : ¬ IsMulCommutative P)
    (hm : ChapterA.Section02.IsTheoremCModel G) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p) := by
  cases hm with
  | alternating n hn hm => exact (no_alternating_le_eight_of_sylow32 P hP hn hm).elim
  | odd hm =>
    cases hm with
    | linear_three p hp ho hm => exact ⟨p,hp,ho,.inl hm⟩
    | unitary_three p hp ho hm => exact ⟨p,hp,ho,.inr hm⟩
    | linear_two p f hp ho _ hm =>
      have hf : 0 < f := by
        obtain ⟨F,_,_,hc,_⟩ := hm
        have hh : 1 < Nat.card F := Finite.one_lt_card
        by_contra hhf
        have he : f=0 := by omega
        simp only [he,pow_zero] at hc
        omega
      exact (not_odd_psl2_of_large_sylow_exponent_eight P hP.ge hexp
        ⟨p,f,hp,ho,hf,rfl⟩ hm).elim
  | bender hm => exact (no_bender_of_noncommutative_sylow32 P hP hnc hm).elim
  | rank_two f hm => exact ⟨3,by decide,by decide,.inr (unitary_three_of_rankTwo_sylow32 P hP hm)⟩
  | linear_binary n hn hm => exact (no_binary_four_or_five_of_sylow32 P hP hn hm).elim
  | sporadic hm => exact (no_sporadic_of_sylow_thirty_two P hP hm).elim
end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt

namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
  {κ : GroupClass.{u}} {K : Subgroup G}
theorem component_quotient_degree_three_of_wreathed32
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (T : Sylow 2 G) (eT : T ≃* WreathedThirtyTwo)
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card P = 32) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (K ⧸ center K) 3 p ∨ ClassicalGroup.IsPSU (K ⧸ center K) 3 p) := by
  obtain ⟨hexp,hnc⟩ := wreathedThirtyTwo_section_invariants T eT K
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _) P hP
  have hm := component_central_quotient_model hA hC hH
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK
  exact ComponentSieve.LargeGoldschmidt.theoremC_degree_three_of_sylow32 P hP hexp hnc hm
end CFSG.Quasithin.ChapterF.SourceAssembly
