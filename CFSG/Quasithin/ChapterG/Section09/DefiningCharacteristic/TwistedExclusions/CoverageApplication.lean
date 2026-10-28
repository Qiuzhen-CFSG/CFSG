module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.ComponentRank

/-!
# Applying triality automorphism coverage to the G.9 component

The actual component and its model isomorphism supply simplicity and
perfectness, as proved in `ComponentRank`. The completed inner–coefficient
decomposition discharges the automorphism-coverage premise of its coarse-rank
exclusion for n ≥ 3, on the original component and its model witness.

The original conditional root-geometric application is retained. The final
theorem needs only the independently owned intrinsic bound m₂(³D₄(2ⁿ)) ≤ 5n.
That bound and the cases n = 1,2 remain with their respective owners.

Source: Aschbacher--Smith G.9, printed p.356 (`refs/quasithin.pdf`), and
GLS3 §2.5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.OuterOdd Triality.Standard.OuterOdd.Coverage

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : CFSG.Quasithin.GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The original G.9 model witness consumes the three root-geometric premises
through the proved coverage reduction. Intrinsic rank is an independent input. -/
theorem not_triality_of_coarse_rank_and_root_geometry
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 3 ≤ n)
    (model : IsTrialityGroupAt (2 ^ n) L)
    (hrank : primeRank 2 (BinaryCarrier n (by omega)) ≤ 5 * n)
    (hgen : Subgroup.closure (rootGenerators (binaryParameters n (by omega)) rfl) = ⊤)
    (halign : ∀ a : MulAut (BinaryCarrier n (by omega)),
      (unipotent (binaryParameters n (by omega))).map a.toMonoidHom =
        unipotent (binaryParameters n (by omega)) →
      ∃ u : BinaryCarrier n (by omega), u ∈ unipotent (binaryParameters n (by omega)) ∧
        PreservesRootFrame (binaryParameters n (by omega)) rfl (MulAut.conj u * a))
    (hparameters : ∀ a : MulAut (BinaryCarrier n (by omega)),
      PreservesRootFrame (binaryParameters n (by omega)) rfl a →
      ∃ t : BinaryCarrier n (by omega), t ∈ torus (binaryParameters n (by omega)) ∧
        ∃ e : CoefficientAut (binaryParameters n (by omega)),
          ∀ (s : Bool) (i : Node) (r : RootField (binaryParameters n (by omega)) i),
            a (rootElement (binaryParameters n (by omega)) rfl s i r) =
            t * rootElement (binaryParameters n (by omega)) rfl s i
              (coefficientRootField (binaryParameters n (by omega)) e i r) * t⁻¹) :
    False := by
  apply not_triality_of_coarse_model_estimates h hn model hrank
  intro _ _
  exact inner_coefficient_of_root_geometry _ rfl hgen halign hparameters

/-- The actual G.9 component supplies the inherited simple/perfect instances;
proved coverage leaves only the independent intrinsic two-rank bound. -/
theorem not_triality_of_coarse_rank
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 3 ≤ n)
    (model : IsTrialityGroupAt (2 ^ n) L)
    (hrank : primeRank 2 (BinaryCarrier n (by omega)) ≤ 5 * n) : False := by
  apply not_triality_of_coarse_model_estimates h hn model hrank
  intro hsimple hperfect
  exact @binary_inner_coefficient n _ hsimple hperfect

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
