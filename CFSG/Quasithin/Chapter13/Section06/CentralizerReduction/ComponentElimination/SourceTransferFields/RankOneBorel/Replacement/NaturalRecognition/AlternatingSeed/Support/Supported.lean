module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.Minimal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.QuotientSolvable
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.SolvableQuotientSelection

/-!
# The supported transposition in the original13.6.15 Sylow subgroup

The literal action has a solvable quotient by its normal A₅ component.
Selecting a moving minimal best offender through B.1.9 supplies a transposition
fixing the component's whole fixed complement. It can be conjugated into any
specified Sylow subgroup. All action coordinates are the original coordinates;
the permutation map may be chosen beforehand and is retained in the conclusion.

The source application supplies the quotient solvability from the actual
cubic residual and all classifier, faithfulness and offender premises from
W_K. No decomposition, offender choice or supported factor is assumed.
Source: Aschbacher–Smith13.6.15, printed p.930 (PDF p.947).
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
open ChapterB.QuasisimpleSource ChapterB.SourceInduction ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

omit [Finite D] in
private theorem not_fixed_of_not_centralizing [C.Normal]
    (hf : Function.Injective ρ) (U : Subrepresentation ρ)
    (hcompl : IsCompl U.toSubmodule (fixedSpace ρ C)) {A : Subgroup D}
    (hA : ¬ A ≤ centralizer (C : Set D)) : ¬ U.toSubmodule ≤ fixedSpace ρ A := by
  intro hfix
  apply hA
  intro a ha c hc
  apply hf
  apply LinearMap.ext
  intro w
  have hw : w ∈ U.toSubmodule ⊔ fixedSpace ρ C := hcompl.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  have hauc : ρ a (ρ c u) = ρ c u := hfix (U.apply_mem_toSubmodule c hu) ⟨a, ha⟩
  have hau : ρ a u = u := hfix hu ⟨a, ha⟩
  have hcz : ρ c z = z := hz ⟨c, hc⟩
  have hcz' : ρ c (ρ a z) = ρ a z :=
    ((fixedSpace_stable_of_normal ρ C (mem_top a) z).2 hz) ⟨c, hc⟩
  simp only [map_mul, Module.End.mul_apply, map_add, hau, hauc, hcz, hcz']

/-- The supplied permutation homomorphism and the original constituent's
coordinates are retained. All offender selection and support are proved. -/
theorem exists_supported_transposition {𝒦 : GroupClass.{u}}
    (h : ClassifierApplicability 𝒦 ρ C) (hc : IsQuasisimple C)
    [C.Normal] [Group.IsSolvable (D ⧸ C)]
    (I : Subrepresentation (ρ.comp C.subtype))
    (e : ActionEquiv I.toRepresentation (alternatingNatural 5))
    (hm : I.toSubmodule = moved ρ C)
    (hcompl : IsCompl I.toSubmodule (fixedSpace ρ C))
    (r : D →* Equiv.Perm (Fin 5))
    (hr : ∀ g (w : I.toSubmodule), ρ g (w : V) =
      (e.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 5)
        (r g) (e.linearEquiv w)) : V)) (P : Sylow 2 D) :
    ∃ a ∈ P, (r a).IsSwap ∧ a ^ 2 = 1 ∧
      ∀ w ∈ fixedSpace ρ C, ρ a w = w := by
  let := h.finite_module
  obtain ⟨A, hA, hAC⟩ := exists_minimalBestOffender_not_centralizing_of_le_offenders
    ChapterB.FittingStructure.earlierB19 ρ h.faithful h.twoCore C hc h.le_offenders h.quotient
  let s := MovedSection.ofNormal ρ C
  have hs : s.space.toSubmodule = I.toSubmodule := s.space_eq.trans hm.symm
  let f := LinearEquiv.ofEq s.space.toSubmodule I.toSubmodule hs
  let a : ActionEquiv (s.space.toRepresentation.comp C.subtype) (alternatingNatural 5) :=
    { groupEquiv := e.groupEquiv
      linearEquiv := f.trans e.linearEquiv
      intertwines g w := e.intertwines g (f w) }
  have hcompl' : IsCompl s.space.toSubmodule (fixedSpace ρ C) := hs ▸ hcompl
  have hr' (g : D) (w : s.space.toSubmodule) :
      a.linearEquiv (s.space.toRepresentation g w) =
        BinaryPermutation.naturalRepresentation (Fin 5) (r g) (a.linearEquiv w) := by
    have he := hr g (f w)
    have hsub : f (s.space.toRepresentation g w) =
        e.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 5)
          (r g) (e.linearEquiv (f w))) := Subtype.ext he
    exact (congrArg e.linearEquiv hsub).trans (e.linearEquiv.apply_symm_apply _)
  obtain ⟨b, _, hb, h2, hf⟩ := minimal_supported_transposition s.space a hcompl' r hr'
    hA (not_fixed_of_not_centralizing h.faithful s.space hcompl' hAC)
  exact supported_transposition_in_sylow r b hb h2 hf P

variable {G : Type u} [Group G] [Finite G]

/-- The supported transposition in any actual plus Sylow subgroup, from the
original local hypotheses of13.6.15 and the original constituent and marking. -/
theorem wk_supported_transposition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    ∀ (I : Subrepresentation (componentRepresentation K L T z v hL hz))
      (e : ActionEquiv I.toRepresentation (alternatingNatural 5))
      (r : Gplus K L T z v hL hz →* Equiv.Perm (Fin 5)),
      (∀ g (w : I.toSubmodule), wkRepresentation K L T z v hL hz g
        (w : Additive (WK K L T z v)) =
        (e.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 5)
          (r g) (e.linearEquiv w)) : Additive (WK K L T z v))) →
      ∀ P : Sylow 2 (Gplus K L T z v hL hz),
        ∃ a ∈ P, (r a).IsSwap ∧ a ^ 2 = 1 ∧
          ∀ w ∈ fixedSpace (wkRepresentation K L T z v hL hz)
            (plusImage K L T z v hL hz K), wkRepresentation K L T z v hL hz a w = w := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  dsimp only
  intro I e r hr P
  let := plusImage_K_normal K L T z v hL hz hK hn
  let := plus_quotient_isSolvable K L T z v hL hz hSylow hK hn hc
  have ha := classifierApplicability_of_local hG K L T z v hv hL hz hSylow hzOmega hf hK hn
  have hq := plusImage_K_quasisimple K L T z v hL hz hK ha.twoCore
  obtain ⟨hm, hcompl⟩ := wk_moved_and_isCompl hG K L T z v hv hL hz hSylow hzOmega hf hK hn I e
  exact exists_supported_transposition ha hq I e hm hcompl r hr P

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
