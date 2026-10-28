module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldParity
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Original Hermitian Cartan parity and the escaping plus torus

In the actual Chapter 12 chosen-module setup, a Hermitian model on the
original omega-span forces the original field degree to be divisible by
four whenever the Cartan fails to normalize O²(H). The original Cartan
splits into its norm-one and complementary factors. Universal local control
makes the first normalize the same residual and forces the second's join
with H to have zero two-core.

This discharges the parity and torus premises of the higher-field source
branch. Selection of the model, the numerical bound from 3.1.6, zero-core
recognition and final normalization remain separate proof obligations.
Source: Aschbacher--Smith 5.1.6(4), 5.2.2 and 12.2.2, printed
pp.632--633,647,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
open Representation.OrthogonalFourMinus
variable {G : Type*} [Group G] [Finite G]
local instance (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))

/-- The original comparison retains its Hall Cartans, field degree and
residual while deriving parity and the literal zero-core plus join. -/
theorem rankOne_cartan_hermitian_torus_of_escape
    {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 2 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (Representation.SL2.BinarySmall.hermitian s)) :
    4 ∣ n ∧ ∃ Dminus Dplus : Subgroup G,
      Dminus ⊔ Dplus = A ∧ Nat.card Dminus = 2^(n/2)+1 ∧
      Nat.card Dplus = 2^(n/2)-1 ∧
      Dminus ⊔ H ≤ omegaCentralizer T ∧
      (Dminus ⊔ H).pCoreIn 2 ≠ ⊥ ∧
      Dminus ≤ normalizer (residual H : Set G) ∧
      (Dplus ⊔ H).pCoreIn 2 = ⊥ := by
  let hi := C.rankOne_generic_input_of_many h hmany (by omega : 1 < n) hpsl
  exact hi.hermitian_torus_of_escape hH c hn hcontrol hescape s hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
