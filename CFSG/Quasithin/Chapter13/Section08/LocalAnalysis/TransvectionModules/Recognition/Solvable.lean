module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Centralizing
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.FaithfulClosure
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.Factors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.Preimage
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.SeedGeneration

/-!
# The solvable normal closure in the transvection argument

For the literal H/O₂(H)-action on U_H/V₁, the source centralizer bound
supplies faithfulness. The transvection and all its conjugates generate best
offenders in their normal closure. Its two-core is trivial. We can therefore
apply the universal earlier B.1.8 factor theorem, with every applicability
condition established, obtaining actual S₃ factors with natural moved spaces.
The three-rank bound gives one or two factors. In the one-factor case the
existing centralizing contradiction now needs only pointwise commutation;
its concrete natural-module witness is constructed here.

The marked A₆ or triple-cover geometry excludes two factors and derives
the exhaustive one-factor residual alternatives. The actual preimage and
its two-residual are retained. The covered L₀ alternative contradicts
13.2.2(9); the L₁ and L₁,+ alternatives give the literal moved-space
equality and then contradict 13.5.5. Full seed generation follows from
the marked flag and 13.7.3(6), so the commuting alternative closes with
the existing centralizing theorem.

`source_normalClosure_not_solvable` completes this implication under the
genuine standing setup. Its only additional inputs are universal earlier
results, specified in `EarlierLocalInputs`, and universal B.1.8. No
factorization, residual alternative, moved-space equality, or conclusion
of a later source theorem is assumed for this normal closure.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.8.5, printed pp.947–948 (PDF pp.964–965). B.1.8 is the universal
earlier input on printed p.70; its factor theorem is owned by Chapter B.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable
open ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- B.1.8 applies to the actual transvection normal closure, and its factor
count is one or two. The earlier theorem is universal in the acting group
and representation; no decomposition of this particular closure is assumed. -/
theorem source_normalClosure_factors
    (hB18 : ∀ (B : Type u) [Group B] [Finite B] [Group.IsSolvable B]
      (σ : Representation (ZMod 2) B (Additive (Source.Utilde H V₃ V₁))),
      pCore 2 B = ⊥ → Function.Injective σ → IsFFModule σ → Nonempty (SolvableFFFactors σ))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (hrank : primeRank 3 H ≤ 2) (t : Source.Hstar H) (ht : IsTransvection ρ t)
    (hsolv : Group.IsSolvable (normalClosure ({t} : Set (Source.Hstar H)))) :
    ∃ d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype),
      (1 ≤ d.count ∧ d.count ≤ 2) ∧
      offenderSubgroup (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype) = ⊤ := by
  have hf := faithful_of_centralizer_le_core ρ hρ hcentralizer
  obtain ⟨d⟩ := normalClosure_factors_of_universal hB18 hf
    (pCore_quotient_pCore_eq_bot 2) ht hsolv
  exact ⟨d, factor_count_le_two H ρ _ d hrank, normalClosure_offenderSubgroup_eq_top ht hf⟩

omit [Finite G] in
/-- The one-factor commuting branch closes with the natural model constructed
from B.1.8, using the already established seed, spanning and faithfulness argument. -/
theorem centralizing_one_factor_impossible
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (L₁ : Subgroup G) (hL : L₁ ≤ H) (hgen : V₃ = ⁅V₃, L₁⁆)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (t : Source.Hstar H) (ht : IsTransvection ρ t)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype) = ⊤)
    (hc : d.count = 1)
    (hcomm : ∀ l ∈ Source.starImage H L₁,
      ∀ k ∈ normalClosure ({t} : Set (Source.Hstar H)), Commute l k) : False :=
  centralizing_transvection_impossible ρ hρ L₁ hL hgen hcentralizer t ht
    (naturalTwo_of_count_one _ d hJ hc) hcomm

open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction

/-- The complete solvable-normal-closure exclusion in the proof of 13.8.5.
The earlier results are universal in the standing setup (or, for B.1.8,
in the acting group), and every applicability condition is established
here. The final recognition and its component branch remain separate. -/
theorem source_normalClosure_not_solvable
    (T : Sylow 2 G) {L V V₂ M G₁ : Subgroup G}
    (s : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierLocalInputs (G := G))
    (hB18 : ∀ (B : Type u) [Group B] [Finite B] [Group.IsSolvable B]
      (σ : Representation (ZMod 2) B (Additive (Source.Utilde H V₃ V₁))),
      pCore 2 B = ⊥ → Function.Injective σ → IsFFModule σ → Nonempty (SolvableFFFactors σ))
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (t : Source.Hstar H) (ht : IsTransvection ρ t) :
    ¬ Group.IsSolvable (normalClosure ({t} : Set (Source.Hstar H))) := by
  intro hsolv
  have hcentralizer := (earlier.centralizer T L V V₁ V₂ V₃ M G₁ s H hH).le
  have hrank := TwoFactors.source_threeRank_le_two s hH
  obtain ⟨d, hcount, hJ⟩ := source_normalClosure_factors hB18 ρ hρ hcentralizer hrank t ht hsolv
  have hc : d.count = 1 := by
    by_contra hne
    have htwo : d.count = 2 := by omega
    exact TwoFactors.source_two_factors_impossible T s earlier.point_models hH ρ hρ t ht d hJ htwo
  have hmodels := earlier.natural_models T L V V₁ V₂ V₃ M G₁ s
  have hfactor := earlier.covered_factorization L (T : Subgroup G) V
  rcases OneFactor.source_one_factor_alternatives T G₁ M hH hmodels hfactor
      hrank s.line_card s.seed_card ρ hρ t ht d hJ hc with
    hcomm | ⟨hres, hcover⟩ | ⟨_, hmoved⟩
  · have hgen := seed_generation_of_core_displacement s hH hmodels hfactor
      (earlier.core_displacement T L V V₁ V₂ V₃ M G₁ s H hH)
    exact centralizing_one_factor_impossible ρ hρ (sourceOne L T V₁)
      (le_sup_left.trans hH.1.2) hgen hcentralizer t ht d hJ hc hcomm
  · exact hH.2.2 (le_M_of_preimageResidual_eq H M (zero L) _ hres
      (earlier.covered_normalizer T L V V₁ V₂ V₃ M G₁ s hcover))
  · exact hH.2.2 (le_M_of_movedSpace_eq ρ hρ
      (s.line_le_plane.trans s.plane_le_seed) M
      (s.first_normalizer ▸ hH.2.1)
      ((earlier.flag_normalizers T L V V₁ V₂ V₃ M G₁ s).trans inf_le_left) _ hmoved)

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable

end
