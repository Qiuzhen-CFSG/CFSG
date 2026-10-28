module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentModels
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.SupercriticalAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.DihedralEight.Models
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.DihedralEight.ElementaryEight
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.Covers

/-!
# The actual component catalogue with dihedral Sylow subgroup of order eight

Theorems A and C apply to the central quotient of the original component
through the SQTK covering group. The original ambient dihedral Sylow gives
the order bound and excludes the elementary-eight models. The surviving
central quotients are odd PSL2 of source degree at most two, A6 and A7.
The odd-center covering theorems then identify the component itself with
an odd PSL2, the hexacode triple cover of A6, A7, or its actual triple cover.

Source: Aschbacher--Smith F.6.18, printed p.310, dihedral-eight branch.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open ComponentSieve
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {K : Subgroup G}

theorem component_quotient_models_of_dihedral_eight
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (T : Sylow 2 G) (eT : T ≃* DihedralGroup 4) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
      ClassicalGroup.IsPSL (K ⧸ center K) 2 (p ^ f)) ∨
    Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 7)) := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  let P : Sylow 2 (K ⧸ center K) := default
  have hT : Nat.card T = 8 := by rw [Nat.card_congr eT.toEquiv, DihedralGroup.nat_card]
  have hP : Nat.card P ≤ 8 := (central_quotient_sylow_card_le T K P).trans hT.le
  have hm := component_central_quotient_model hA hC hH
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK
  rcases theoremC_model_of_sylow_le_eight P hP (Group.IsPerfect.not_isSolvable _) hm with
    hm | hm | hm | hm | hj
  · exact .inl hm
  · exact .inr (.inl hm)
  · exact .inr (.inr hm)
  · exact (not_pslTwoEight_central_quotient T eT K hm).elim
  · exact (not_jankoOne_central_quotient T eT K (Classical.choice hj)).elim

/-- Actual component models, with only the original earlier A/C source
results explicit and all cover alternatives constructed. -/
theorem component_models_of_dihedral_eight
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (T : Sylow 2 G) (eT : T ≃* DihedralGroup 4) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
      ClassicalGroup.IsPSL K 2 (p ^ f)) ∨
    Nonempty (K ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
    Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (K ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) := by
  let : IsQuasisimple K := hK.2
  have hcore := Noncyclic.twoCore_eq_bot_of_primeToThreeCore_eq_bot
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e)
  have hodd := GLS3.Chapter5.OddCentralCovers.component_center_odd hcore K hK
  rcases component_quotient_models_of_dihedral_eight hA hC hH e hK T eT with
    hm | hj | hj
  · obtain ⟨p, f, hp, ho, hf, hf2, hm⟩ := hm
    rcases quasisimple_odd_psl2_of_odd_center hodd ho.pow hm with hm | ⟨_, hm⟩
    · exact .inl ⟨p, f, hp, ho, hf, hf2, hm⟩
    · exact .inr (.inl hm)
  · obtain ⟨j⟩ := hj
    rcases quasisimple_alternating_six_of_odd_center hodd j with ha | hm
    · obtain ⟨a⟩ := ha
      let b := Atlas.Comparisons.Exceptional.psl2NineEquivAlt6
      refine .inl ⟨3, 2, by decide, by decide, by decide, by decide,
        GaloisField 3 2, inferInstance, inferInstance, ?_, ⟨a.trans b.symm⟩⟩
      rw [GaloisField.card 3 2 (by decide)]
    · exact .inr (.inl hm)
  · obtain ⟨j⟩ := hj
    rcases quasisimple_alternating_seven_of_odd_center hodd j with hm | hm
    · exact .inr (.inr (.inl hm))
    · exact .inr (.inr (.inr hm))

end CFSG.Quasithin.ChapterF.SourceAssembly
