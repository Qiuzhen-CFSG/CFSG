module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SplitSixteen.Assembly
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SplitSixteen.PSL2Eight
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.SourceComponent

/-!
# Actual component models in the split-sixteen branch

The complete Theorem C sieve leaves odd PSL2, A6, or A7 as the literal
central quotient. Its binary-eight endpoint is excluded using the full
universal cover and odd outer group. The original SQTK quotient supplies
an odd component center, so the actual universal covering calculations
identify the component itself with odd PSL2 or the concrete triple covers.

Source: Aschbacher--Smith F.6.18(8)--(9), printed p.310. Only earlier A/C
and the actual normal two-group extension hypotheses remain explicit.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open ComponentSieve
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {K : Subgroup G} [K.Normal]

theorem component_quotient_models_of_split_sixteen
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (hFstar : generalizedFitting G = K)
    (hquot : IsPGroup 2 (G ⧸ K)) (T : Sylow 2 G)
    (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
      ClassicalGroup.IsPSL (K ⧸ center K) 2 (p ^ f)) ∨
    Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 7)) := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  have hcore := Noncyclic.twoCore_eq_bot_of_cover e
  have hodd := GLS3.Chapter5.OddCentralCovers.component_center_odd hcore K hK
  have hm := component_central_quotient_model hA hC hH
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK
  rcases SplitSixteen.theoremC_component_models_of_split_sixteen T eT K hFstar hK hodd hm with
    hm | hm | hm | hm
  · exact .inl hm
  · exact .inr (.inl hm)
  · exact .inr (.inr hm)
  · exact (SplitSixteen.not_psl_two_eight_component T eT K hFstar hK hquot hm).elim

/-- Actual component models, with only the original earlier A/C source
results explicit and all cover alternatives constructed. -/
theorem component_models_of_split_sixteen
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (hFstar : generalizedFitting G = K)
    (hquot : IsPGroup 2 (G ⧸ K)) (T : Sylow 2 G)
    (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
      ClassicalGroup.IsPSL K 2 (p ^ f)) ∨
    Nonempty (K ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
    Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (K ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) := by
  let : IsQuasisimple K := hK.2
  have hcore := Noncyclic.twoCore_eq_bot_of_primeToThreeCore_eq_bot
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e)
  have hodd := GLS3.Chapter5.OddCentralCovers.component_center_odd hcore K hK
  rcases component_quotient_models_of_split_sixteen hA hC hH e hK hFstar hquot T eT with
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
