module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.WeakClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Weak closure of the original linear root planes

Natural-module offender theory puts every maximum elementary subgroup of the
ambient Sylow T in S. The two source cores exhaust that family, generate J(T),
and are weakly closed in T under G-conjugacy. These are the actual original
Chapter12 groups and residual, with both orientations and q=4 retained.

This supplies §5.3.6(1) and the preceding Thompson calculation. The orbit count
in §5.3.6(2), full-normalizer realization, centralizer control and ambient
recognition remain separate obligations of the linear-row owner.
Source: Aschbacher–Smith 5.3.5–7, printed pp.660–661, using B.4.2(1), p.86,
and applied in Chapter12 on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (he : Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F).reverse))
  (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include D h hmany hn hpsl hH d hp hm hF he hmax

/-- The maximum elementary family, Thompson subgroup, and weak closure in
the original Chapter12 Sylow, with no geometric premise remaining. -/
theorem rankOne_global_linear_weak_closure :
    elementaryAbelianMaxSubgroups (T : Subgroup G) =
      {L.pCoreIn 2,(residual H).pCoreIn 2} ∧
    Global.sourceS L H = elementaryAbelianMaxJ (T : Subgroup G) ∧
    ∀ E ∈ ({L.pCoreIn 2,(residual H).pCoreIn 2} : Set (Subgroup G)), ∀ g : G,
      E.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      E.map (MulAut.conj g).toMonoidHom = E := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.linear_maxElementary_pair hi hH hp F hm hF he hmax,
    d.linear_sourceS_eq_thompson hi hH hp F hm hF he hmax,
    d.linear_root_planes_weakly_closed hi hH hp F hm hF he hmax⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
