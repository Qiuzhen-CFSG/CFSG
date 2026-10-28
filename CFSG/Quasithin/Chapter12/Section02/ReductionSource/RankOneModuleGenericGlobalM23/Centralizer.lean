module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Centralizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.Local

/-!
# The original central involution and TI core at the Chapter 12 consumer

Nonmaximality of the prepared whole-residual linear row supplies its actual
exceptional overcomponent J. The source 5.2.12 argument identifies Z(T), puts
the full ambient involution centralizer in J, identifies its exact two-core
and PSL₃(2) quotient, and proves that core is TI in G. It also places N_G(T)
in this centralizer, as required later in source 5.2.21.

The selected field and both whole-overlap maps are retained. These are steps
toward ambient M₂₃ recognition, not a proof of GlobalExit.
Source: Aschbacher–Smith 5.2.12 and 5.2.21, pp.654,657 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Ambient centralizer control and the TI core of the original nonmaximal
linear branch, with the same Sylow subgroup and exceptional overcomponent. -/
theorem rankOne_global_linear_nonmaximal_centralizer_geometry
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
      Nat.card (center T) = 2 ∧
        (∀ x y : G, x ∈ J.pCoreIn 2 → y ∈ J.pCoreIn 2 → x ≠ 1 → y ≠ 1 →
          ∃ a : J, (a : G)*x*(a : G)⁻¹ = y) ∧
        ∃ z : G, z ∈ J.pCoreIn 2 ∧ orderOf z = 2 ∧
          (center T).map (T : Subgroup G).subtype = zpowers z ∧
          centralizer ({z} : Set G) ≤ J ∧
          (centralizer ({z} : Set G)).pCoreIn 2 = J.pCoreIn 2 ∧
          Nonempty ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∧
          ChapterI.Section06To08.IsTISubgroup (J.pCoreIn 2) ∧
          normalizer ((T : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional hi hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,hblock⟩ := hc.resolve_left hnonmax
  exact ⟨J,hJ,hKJ,d.linear_exceptional_centralizer_geometry hi hH hp F hm hF he hJ hKJ⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
