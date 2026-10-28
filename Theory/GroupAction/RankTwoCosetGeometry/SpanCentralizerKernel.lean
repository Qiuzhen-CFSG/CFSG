module
public import Theory.GroupAction.RankTwoCosetGeometry.SecondBallKernel
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The second ball kernel as an orbit-span centralizer

Relative normality propagates centralization of a seed to its whole orbit
span. Apply this to the second kernel at one endpoint, which fixes the
first ball at the other endpoint. Conversely, a normal span centralizer
contained in both first kernels fixes the second ball by the normal-core
formula. No finite or connected graph hypothesis is required.

Source application: Aschbacher--Smith F.3.2--4 and 15.2.8, printed pp.270
and 1110, to the literal graph of the two source parabolics.
-/

public section
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Fixing a seed at one endpoint makes the neighboring second kernel
fix its entire vertex-group orbit span. -/
theorem second_kernel_le_span_centralizer (V : Subgroup G)
    (hc : ballKernel F (base F false) 1 ≤ centralizer (V : Set G)) :
    ballKernel F (base F true) 2 ≤
      F true ⊓ centralizer (conjugateSpanBy V (F true) : Set G) := by
  have hle : ballKernel F (base F true) 2 ≤ F true := by
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using
      ballKernel_le_stabilizer F (base F true) 2
  have hn : F true ≤ normalizer (ballKernel F (base F true) 2 : Set G) := by
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using
      stabilizer_le_normalizer_ballKernel F (base F true) 2
  have ha : (graph F).Adj (base F true) (base F false) :=
    ⟨by change true ≠ false; decide,incident_base F true false⟩
  exact le_inf hle (le_centralizer_conjugateSpanBy_of_normalizes _ V _ hn
    ((ballKernel_succ_le F ha 1).trans hc))

/-- If the first kernel is the seed centralizer, the neighboring second
kernel is exactly the span centralizer whenever that centralizer fixes
the neighboring first ball. -/
theorem second_kernel_eq_span_centralizer (V : Subgroup G)
    (hfirst : ballKernel F (base F false) 1 = F false ⊓ centralizer (V : Set G))
    (hwhole : F true ⊓ centralizer (conjugateSpanBy V (F true) : Set G) ≤
      ballKernel F (base F true) 1) :
    ballKernel F (base F true) 2 =
      F true ⊓ centralizer (conjugateSpanBy V (F true) : Set G) := by
  apply le_antisymm (second_kernel_le_span_centralizer F V (hfirst.le.trans inf_le_right))
  let C := F true ⊓ centralizer (conjugateSpanBy V (F true) : Set G)
  have hn : F true ≤ normalizer (C : Set G) :=
    (le_inf (F true).le_normalizer
      ((le_normalizer_conjugateSpanBy V (F true)).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let : (C.subgroupOf (F true)).Normal := normal_subgroupOf_of_le_normalizer hn
  have hCF : C ≤ F false := by
    have ha : (graph F).Adj (base F true) (base F false) :=
      ⟨by change true ≠ false; decide,incident_base F true false⟩
    have hh := hwhole.trans ((ballKernel_one_le_edge F ha).trans inf_le_right)
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using hh
  have hCfirst : C ≤ ballKernel F (base F false) 1 := by
    rw [hfirst]
    exact le_inf hCF (inf_le_right.trans (centralizer_le (le_conjugateSpanBy V (F true))))
  have hCcore : C.subgroupOf (F true) ≤
      ((ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1).subgroupOf
        (F true)).normalCore :=
    normal_le_normalCore.mpr (fun _ hx => ⟨hCfirst hx,hwhole hx⟩)
  rw [←base_ballKernel_two F true] at hCcore
  intro x hx
  exact hCcore (show (⟨x,hx.1⟩ : F true) ∈ C.subgroupOf (F true) from hx)
end Subgroup.CosetGeometry.RankTwo
