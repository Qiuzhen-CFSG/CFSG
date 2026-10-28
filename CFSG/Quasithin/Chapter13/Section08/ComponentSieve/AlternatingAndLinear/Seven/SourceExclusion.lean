module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.SourceExclusion.Inputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.SourceExclusion.Sections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeQuadratic
public import Mathlib.Order.Atoms.Finite

/-!
# Conditional exclusion of K/O₂(K) ≅ A₇

Construct the faithful seven-point action from the actual component quotient.
A first-case transvection, for either corrected critical actor, selects the
whole natural module by 13.8.5 and contradicts the even partition two-core.
In the remaining case choose a maximal proper subrepresentation of U_H/V₁;
its existence follows from the nonzero rank-two generating seed and finiteness.
The solvable-overgroup and theta arguments give both relative partitions.

For 4+3, the local residual/seed arguments derive surjectivity and select the
natural maximal quotient from the genuine 4,6,4+dual alternatives. Quadraticity
passes to this quotient and to the conjugated critical actor in the literal
Klein-four two-core, forcing rank(Vγ*)=1. The earlier 13.8.18 argument and
inverse endpoint transport construct a reciprocal transvection surviving V₁;
the first-case parity obstruction then gives the contradiction.

For 2³+1, the branch proves local three-rank one, the A₆ quotient and the
natural maximal quotient. The universal 13.7.6(3) implication forces K to act
nontrivially on W. Both 13.8.22 alternatives and the strong-FF exclusion give
rank(Uγ*)=1 and natural submodules on both faithful sections. The literal
pointwise-centralizer identities contradict 13.8.23(4).

The earlier facts listed in `Earlier` are explicit, authorized conditional
inputs. Every additional premise of the partition helpers is discharged here.
`not_alternatingSeven_original` applies 13.8.16 to K(L₁T), retaining the
original intrinsic quotient of K and descending relative component normality.
This completes the conditional 13.8.24 argument; its chapter consumer still
supplies the preceding source facts and universal appendix implications.

The β correction uses g_b⁻¹γ₁, not g_b⁻¹γ. No core is replaced by a residual;
the incompatible printed O₂ equality with a three-cycle group is not used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959/PDF pp.975–976 (1 March 2004 manuscript).
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.SourceExclusion
open CriticalGeometry PairsBranch PairsBranch.ModuleSelection
open FourThreeBranch.NaturalSelection
universe u
variable {G : Type u} [Group G] [Finite G]
  {L T H V : Subgroup G} (c : CriticalPair L T H V)
  (K L₁ L₀ X G₁ M V₃ V₁ : Subgroup G)
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [IsElementaryAbelian 2 (Source.VH H V)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))

variable {c K L₁ L₀ X G₁ M V₃ V₁ ρ}
  (d : Earlier c K L₁ L₀ X G₁ M V₃ V₁ ρ)

omit [IsElementaryAbelian 2 (Source.VH H V)] in
include d in
private theorem exists_maximal : ∃ W : Subrepresentation ρ, IsCoatom W := by
  have hp : 0 < Module.finrank (ZMod 2) (sourceImage H V₃ V₁ V₃) := by rw [d.seed_rank]; decide
  let : Nontrivial (sourceImage H V₃ V₁ V₃) := Module.nontrivial_of_finrank_pos hp
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁)) :=
    Function.Injective.nontrivial (sourceImage H V₃ V₁ V₃).subtype_injective
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, by
    intro h
    have h' := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h'⟩⟩
  exact IsCoatomic.exists_coatom (Subrepresentation ρ)

omit [Finite G] in
private theorem quadratic_quotient (W : Subrepresentation ρ)
    (A : Subgroup (Source.Hstar H)) (hq : IsQuadratic ρ A) :
    IsQuadratic W.quotientRepresentation A := by
  intro a ha b hb q
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    change W.toSubmodule.mkQ (ρ a (ρ b v - v)) = W.toSubmodule.mkQ (ρ b v - v)
    rw [hq a ha b hb v]

include d in
private theorem second_case (φ : Source.Hstar H →* S7) (hi : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range) :
    LocalGeometry.SecondCase H L₁ T (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma
      (c.Aone V₁) V₁ ρ := by
  let := d.base_solvable
  let : IsElementaryAbelian 2 (CriticalReciprocity.Vbeta c) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  obtain ⟨S, hS⟩ := d.sylow
  rcases d.alternatives with hb | hg | hs
  · exfalso
    apply LocalGeometry.exclude_first_case_actor H L L₁ T G₁ M
      (CriticalReciprocity.Vbeta c) (CriticalReciprocity.Vbeta c)
      d.member.1.2 d.member.2.1 d.theta d.solvable_overgroups S hS ρ φ hi hAlt
      d.transvection_models d.covered_nine
      (CriticalReciprocity.Vbeta_le_H c L₁ d.edge d.terminal_core)
      le_rfl _ hb
    refine ⟨1, ?_⟩
    change (CriticalReciprocity.Vbeta c).conjBy 1 ≤ _
    rw [conjBy_one]
    exact CriticalReciprocity.Vbeta_le_twoCore c L₁ d.edge d.terminal_core
  · exact (LocalGeometry.exclude_first_case_actor H L L₁ T G₁ M c.Vgamma c.Vgamma
      d.member.1.2 d.member.2.1 d.theta d.solvable_overgroups S hS ρ φ hi hAlt
      d.transvection_models d.covered_nine d.Vgamma_le le_rfl d.Vgamma_placement hg).elim
  · exact hs

include d in
private theorem four_three_impossible
    (φ : Source.Hstar H →* S7) (hi : Function.Injective φ)
    (hK : (Source.starImage H K).map φ = alternatingGroup (Fin 7))
    (hP : Source.starImage H (L₁ ⊔ T) = fourThreeStabilizer.comap φ)
    (hs : LocalGeometry.SecondCase H L₁ T (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma
      (c.Aone V₁) V₁ ρ) (W : Subrepresentation ρ) (hW : IsCoatom W) : False := by
  obtain ⟨_, _, _, _, _, hfull, _, hnatural, _, _⟩ :=
    source_natural_quotient H K L L₁ L₀ X T G₁ M V₃ V₁ ρ d.source_action
      d.member.1.2 d.member.2.1 d.theta d.solvable_overgroups φ hi hK hP
      d.local_models d.six_local_card d.covered_residuals d.component_le d.generated
      d.monolith W hW d.seed_normalized d.seed_irreducible d.seed_rank d.seed_centralized
      (Source.starImage H (c.Ugamma V₃)) hs.2.2.2.2.1 hs.2.2.2.2.2.1
      hs.2.2.2.2.2.2.1 (d.small_modules φ hi hK)
  have hUV : c.Ugamma V₃ ≤ c.Vgamma :=
    map_mono (conjugateSpanBy_mono d.flag le_rfl)
  have hAV : IsElementaryTwo (Source.starImage H c.Vgamma) := by
    refine ⟨?_, ?_⟩
    · intro hz
      exact hs.2.2.2.2.1.1 (eq_bot_iff.mpr
        (hz ▸ LocalGeometry.starImage_mono H hUV))
    · let : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
      let : IsElementaryAbelian 2 (c.Vgamma.subgroupOf H) :=
        IsElementaryAbelian.subgroupOf d.Vgamma_le
      exact IsElementaryAbelian.map _
  obtain ⟨y, hy⟩ := hs.2.2.2.2.2.2.2
  have hr := FourThreeQuadratic.rank_eq_one_of_conjugate W.quotientRepresentation φ hi
    (Source.starImage H (L₁ ⊔ T)) (Source.starImage H c.Vgamma)
    (QuotientGroup.mk' (pCore 2 H) y) hfull
    (LocalGeometry.star_conjugate_le_twoCore H (L₁ ⊔ T) c.Vgamma
      d.member.1.2 d.Vgamma_le y hy)
    hAV hnatural (quadratic_quotient W _ d.Vgamma_quadratic)
  let := d.base_solvable
  obtain ⟨S, hS⟩ := d.sylow
  have hAlt : alternatingGroup (Fin 7) ≤ φ.range := by
    rw [← hK]
    exact map_le_range φ _
  exact CriticalReciprocity.exclude_of_rank_one c L₁ K V₃ V₁ G₁ M
    (d.reciprocal_inputs hs) ρ d.source_action hr d.member.2.1 d.theta
    d.solvable_overgroups S hS φ hi hAlt d.transvection_models d.covered_nine

include d in
/-- Conditional 13.8.24 from the genuine earlier local and appendix inputs. -/
theorem not_alternatingSeven : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨eK⟩
  let := d.base_solvable
  obtain ⟨φ, hi, hK, _⟩ := LocalGeometry.source_action_exists H K T d.component_le
    (le_sup_right.trans d.member.1.2) d.component d.component_normal d.two_group
    d.supplement eK
  have hAlt : alternatingGroup (Fin 7) ≤ φ.range := by
    rw [← hK]
    exact map_le_range φ _
  have hs := second_case d φ hi hAlt
  obtain ⟨S, hS⟩ := d.sylow
  obtain ⟨σ, hp, _, _, _⟩ := LocalGeometry.source_partition_dichotomy H L₁ T G₁ M
    d.member.1.2 d.member.2.1 d.theta d.solvable_overgroups φ hi hAlt S hS
  let ψ := (MulAut.conj σ).toMonoidHom.comp φ
  have hiψ : Function.Injective ψ := (MulAut.conj σ).injective.comp hi
  have hKψ := LocalGeometry.alternating_image_conjugate φ (Source.starImage H K) hK σ
  obtain ⟨W, hW⟩ := exists_maximal d
  rcases hp with hp | hp
  · exact four_three_impossible d ψ hiψ hKψ hp hs W hW
  · let a : LocalRank.CompatibleAction H K := ⟨d.component_le, ψ, hiψ, hKψ⟩
    exact exclude_pair_partition H V₃ V₁ L L₁ T G₁ M K (c.Ugamma V₃) (c.Aone V₁)
      a hp d.theta d.seed_nontrivial d.seed_commutator d.local_models d.covered_local_rank
      ρ d.source_action d.member d.line_le d.component d.local_le_component d.generated
      d.monolith d.seed_normalized d.seed_irreducible d.seed_rank W hW
      hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1
      (source_critical_line c L₁ K (d.reciprocal_inputs hs) ρ d.source_action)
      ((source_codimension_le _ (commutatorPreimage_le _ _ _)).trans hs.2.2.2.1)
      (d.small_modules ψ hiψ hKψ)
      d.alternating_natural d.no_strong d.recognition (d.strict_centralizer W hW)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.SourceExclusion

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.SourceExclusion
open CriticalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The actual critical pair and binary conjugation representation together
with precisely the earlier inputs used by the conditional exclusion. -/
structure LocalData (L T H V K L₁ L₀ X G₁ M V₃ V₁ : Subgroup G) where
  elementary_U : IsElementaryAbelian 2 (Source.UH H V₃)
  elementary_V : IsElementaryAbelian 2 (Source.VH H V)
  denominator_normal : (V₁.subgroupOf (Source.UH H V₃)).Normal
  pair : CriticalPair L T H V
  representation : letI := elementary_U; letI := denominator_normal
    Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))
  earlier : letI := elementary_U; letI := denominator_normal
    Earlier pair K L₁ L₀ X G₁ M V₃ V₁ representation

/-- A bundle of actual earlier local data discharges the conditional theorem. -/
theorem LocalData.not_alternatingSeven
    {L T H V K L₁ L₀ X G₁ M V₃ V₁ : Subgroup G}
    (d : LocalData L T H V K L₁ L₀ X G₁ M V₃ V₁) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) := by
  let := d.elementary_U
  let := d.elementary_V
  let := d.denominator_normal
  exact SourceExclusion.not_alternatingSeven d.earlier

/-- Conditional 13.8.24 for an original member of Hz. The source's
13.8.16(1) reduction supplies J=K(L₁T); component membership and normality
are transported to that J. Only earlier local data for reduced members are
requested. The intrinsic quotient of K is the original one throughout. -/
theorem not_alternatingSeven_original
    (L T H V K L₁ L₀ X G₁ M V₃ V₁ : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (h16 : K ⊔ (L₁ ⊔ T) ∈ Source.Hz L₁ T G₁ M)
    (earlier : ∀ J : Subgroup G, J ∈ Source.Hz L₁ T G₁ M → K ≤ J →
      (K.subgroupOf J).IsCComponent → (K.subgroupOf J).Normal →
      J = K ⊔ (L₁ ⊔ T) → Nonempty (LocalData L T J V K L₁ L₀ X G₁ M V₃ V₁)) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  apply LocalGeometry.exclude_original_of_reduced L₁ T G₁ M H K hH hKH hK hKn h16 e
  intro J hJ hKJ hc hn he hA7
  obtain ⟨d⟩ := earlier J hJ hKJ hc hn he
  exact d.not_alternatingSeven hA7

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.SourceExclusion
