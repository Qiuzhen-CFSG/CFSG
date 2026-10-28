module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Seed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling.Consumers

/-!
# Source generation applications of the proved seed automizer bound

The literal H-star Hall actor, once faithful by the exact odd-kernel
normalizer contract, gives n(H) ≤ n whenever H ∩ M normalizes V. The
proved preceding normalization supplies this for Sp₄ and G₂. Thus those
rows of 11.2.1 need no additional automizer or doubled-module premise.

For the full alternative and its actual 11.3.6--7 consumers, only the
V_M doubled automizer bound remains from the automizer calculation. The
weak-closure source owner retains that bound and final assembly. The shared
odd-kernel contract remains with qt-d-1222-natural-odd-kernel-normalizer;
none of these conditional applications discharges it.

Source: Aschbacher--Smith 11.2.1, 11.3.6--7, printed pp.766--767,772--773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The source first branch when the actual intersection preserves V. -/
theorem parameter_le_degree_of_intersection_normalizes
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hN : H ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G)) :
    generationParameter H ≤ S.field.degree := by
  by_contra hlarge
  have hlarge' : 1 < generationParameter H := S.nonbinary.trans (Nat.lt_of_not_ge hlarge)
  obtain ⟨hP,f,_,hf,d,hm,_⟩ := hall_data D S hH hlarge'
  have hfaith := hall_faithful D S hcontrol hH hlarge' hP d hm
  have hBM : d.witness.abelianGroup.map H.subtype ≤ normalizer (L : Set G) :=
    map_le_iff_le_comap.mpr (d.hall_le.trans hm.le)
  exact hlarge ((parameter_le_automizer hH.1.1.2 hP d hf hfaith
    (normalizer (L : Set G) ⊓ normalizer (V : Set G)) V
    (le_inf D.sylow_normalizes_component S.sylow_normalizes)
    (le_inf hBM ((le_inf (map_subtype_le _) hBM).trans hN)) inf_le_right le_rfl).trans
      (seed_nPrime_le D S))

/-- The symplectic and G₂ H-star bounds, conditional only on odd-kernel control. -/
theorem other_rows_parameter_le_degree
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hrows :
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))) :
    generationParameter H ≤ S.field.degree :=
  parameter_le_degree_of_intersection_normalizes D S hcontrol hH
    ((Preliminary.intersection_normalizes D S hrows H hH).trans inf_le_right)

/-- Only the doubled V_M bound remains in the automizer premise. -/
theorem automizer_bounds_of_doubled_bound
    (hfull : DoubledNatural D S →
      nPrime (inducedAutomizer
        (Source.conjugateSpan (normalizer (L : Set G)) V)
        (normalizer (L : Set G))) ≤ 2 * S.field.degree) : AutomizerBounds D S :=
  ⟨seed_nPrime_le D S, hfull⟩

/-- The literal 11.2.1 conclusion after discharging the seed bound. -/
theorem conclusion_of_doubled_bound
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hfull : DoubledNatural D S →
      nPrime (inducedAutomizer
        (Source.conjugateSpan (normalizer (L : Set G)) V)
        (normalizer (L : Set G))) ≤ 2 * S.field.degree)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Conclusion D S H :=
  Doubling.conclusion_of_automizer_bounds D S hcontrol
    (automizer_bounds_of_doubled_bound D S hfull) hH

open ShadowReduction
variable {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Apply the reduced generation assembly to the actual 11.3.6 exclusion. -/
theorem shadow_parameter_upper_of_doubled_bound
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hfull : DoubledNatural D S →
      nPrime (inducedAutomizer
        (Source.conjugateSpan (normalizer (L : Set G)) V)
        (normalizer (L : Set G))) ≤ 2 * S.field.degree)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H) :
    ChapterE.generationParameter H ≤ S.field.degree :=
  Doubling.shadow_parameter_upper D S hcontrol
    (automizer_bounds_of_doubled_bound D S hfull) h p hc f hpoint r

/-- Apply it to the actual residual-component conclusion of 11.3.7. -/
theorem shadow_parameter_component_of_doubled_bound
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hfull : DoubledNatural D S →
      nPrime (inducedAutomizer
        (Source.conjugateSpan (normalizer (L : Set G)) V)
        (normalizer (L : Set G))) ≤ 2 * S.field.degree)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : ParameterComponent.RankOneReduction S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ParameterComponent.Conclusion S H :=
  Doubling.shadow_parameter_component D S hcontrol
    (automizer_bounds_of_doubled_bound D S hfull) h p hc f hpoint r hs

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
