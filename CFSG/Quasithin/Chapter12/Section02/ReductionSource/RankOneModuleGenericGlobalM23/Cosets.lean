module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.FieldExtension
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Cosets

/-!
# The original exceptional-local coset action at Chapter 12

Apply source 5.2.19 to the literal whole reduced-module input. The constructed
local marking identifies the original J-orbit in G/(L ∨ H) with all pairs
of the native heptad, preserving the two-core and H under the same map.
Source: Aschbacher–Smith 5.2.19(1–2), printed p.656 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Source 5.2.19(1–2), with the actual original cosets and local action. -/
theorem rankOne_global_linear_exceptional_coset_orbit
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    : ∃ (ζ : J ≃* heptadStabilizer)
        (e : MulAction.orbit J ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ≃
          {p : Finset (Fin 23) // p.card = 2 ∧ p ⊆ omega}),
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ∀ j : J, (e ⟨j • ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)),
        MulAction.mem_orbit _ j⟩).val = ζ j • x.val := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_exceptional_coset_orbit hi hH hp E hm hE he hJ hKJ
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
