module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupMovement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityOddQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityTerminal

/-!
# Fundamental-module geometry in the original parity application

The original chosen-module hypotheses construct the Fundamental Setup used
in 5.1.17. Once its natural action is identified, the Sylow line has order
2ⁿ, is TI under N_G(L), and the actual Cartan moves the whole module.
The final application assembles the parity seed from the remaining natural,
global TI and F.8 hypotheses, discharging its cardinality, central-image,
movement and quotient-rank fields. These remaining geometric hypotheses
are owned by qt-d-1222-linear-field-parity, as is the displacement proof.

Source: Aschbacher–Smith 5.1.17, printed pp.640–641, used in 12.2.2,
printed p.795 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The newly selected FSU exists under the original chosen-module hypotheses. -/
theorem rankOne_parity_fundamental_exists
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L) :=
  fundamental_exists (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)

/-- The actual selected point and Cartan satisfy the local geometry clauses. -/
theorem rankOne_odd_fundamental_point_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : Chapter6.Source.IsNaturalModule L F.moduleSubgroup n) :
    Nat.card (setup T L F.moduleSubgroup H A).V₁ = 2 ^ n ∧
    (∀ g ∈ normalizer (L : Set G),
      (setup T L F.moduleSubgroup H A).V₁ ⊓
          (setup T L F.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L F.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom =
          (setup T L F.moduleSubgroup H A).V₁) ∧
      F.moduleSubgroup = ⁅F.moduleSubgroup,A⁆ := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact ⟨fundamental_point_card F hi.sylow_normalizes hpsl hodd hnat,
    fun _ hg => fundamental_point_ti_under_normalizer F hi.sylow_normalizes hpsl hodd hnat hg,
    fundamental_cartan_commutator F hi.sylow_normalizes hpsl hn c hnat⟩

/-- The remaining source geometry suffices; no numerical or movement callback remains. -/
theorem rankOne_odd_seed_of_fundamental_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : Chapter6.Source.IsNaturalModule L F.moduleSubgroup n)
    (hf : (setup T L F.moduleSubgroup H A).Hypothesis)
    (hti : ∀ g : G,
      (setup T L F.moduleSubgroup H A).V₁ ⊓
          (setup T L F.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L F.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom =
          (setup T L F.moduleSubgroup H A).V₁) :
    Nonempty (Seed T L H A n) := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hm,hf'⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact seed_of_fundamental_geometry hi hH c hodd hm hf' hlinear F hnat hf hti

/-- Parity with the derived seed fields removed from the remaining source obligations. -/
theorem rankOne_even_exponent_of_fundamental_geometry_and_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgeometry : ∀ A B : Subgroup G, CartanPair T L H A B → Odd n →
      ∃ F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L,
        Chapter6.Source.IsNaturalModule L F.moduleSubgroup n ∧
        (setup T L F.moduleSubgroup H A).Hypothesis ∧
        ∀ g : G,
          (setup T L F.moduleSubgroup H A).V₁ ⊓
              (setup T L F.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            (setup T L F.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom =
              (setup T L F.moduleSubgroup H A).V₁)
    (hlower : DisplacementSource T L H n) : Even n := by
  apply D.rankOne_even_exponent_of_seed_and_displacement h hn hpsl hH hgen ?_ hlower
  intro A B c hodd
  obtain ⟨F,hnat,hf,hti⟩ := hgeometry A B c hodd
  exact D.rankOne_odd_seed_of_fundamental_geometry h hmany hn hpsl hH hlinear c hodd
    F hnat hf hti

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
