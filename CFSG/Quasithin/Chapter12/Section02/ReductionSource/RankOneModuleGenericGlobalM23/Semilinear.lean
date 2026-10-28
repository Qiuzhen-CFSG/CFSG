module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CubicLocal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.Local

/-!
# The original semilinear local and its scalar cubic at Chapter 12

The chosen module supplies the generic input on its whole reduced subgroup.
The nonmaximal linear source theorem identifies the actual quotient of
M = N_G(L) with ΓL₂(4), preserving L and the entire two-core action.
It also constructs a Sylow three-subgroup of the literal preimage of
C_{M/O₂(M)}(L/O₂(L)). Its normalizer inside M is a complement to O₂(M)
and maps isomorphically onto that same semilinear quotient.

Source: Aschbacher–Smith 5.2.11(3) and the local-normalizer step of 5.2.15,
printed pp.653–655 (`refs/quasithin.pdf`). Full ambient cubic-normalizer
recognition, completion, ambient generation and GlobalExit remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.SL2FourNatural.SemilinearNormalizer
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual maximal-local quotient, with its original layer and full core action. -/
theorem rankOne_global_linear_nonmaximal_semilinear_quotient
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
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ e : ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G))) ≃* Gamma,
      (L.subgroupOf (normalizer (L : Set G))).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))) = special.range ∧
      ∃ b : Multiplicative Representation.SL2FourNatural.V ≃* pCore 2 (normalizer (L : Set G)),
        ∀ (x : normalizer (L : Set G)) (v : Multiplicative Representation.SL2FourNatural.V),
          (b (Multiplicative.ofAdd (natural (e (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))) x)) v.toAdd)) : normalizer (L : Set G)) =
            x * (b v : normalizer (L : Set G)) * x⁻¹ := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_nonmaximal_semilinear_quotient hi hH hp E hm hE he hnonmax

/-- The original scalar cubic is Sylow in the actual quotient-action centralizer;
its normalizer inside M is a marked ΓL₂(4) complement. -/
theorem rankOne_global_linear_nonmaximal_scalar_cubic_local_normalizer
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
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    let M := normalizer (L : Set G)
    let π := QuotientGroup.mk' (pCore 2 M)
    let Lbar := (L.subgroupOf M).map π
    ∃ e : (M ⧸ pCore 2 M) ≃* Gamma,
      (L.subgroupOf M).map (e.toMonoidHom.comp π) = special.range ∧
      ∃ C : Subgroup M, C.map (e.toMonoidHom.comp π) = scalar.range ∧ Nat.card C = 3 ∧
        (∃ P : Sylow 3 ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π),
          (P : Subgroup ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π)).map
            ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π).subtype = C) ∧
        (pCore 2 M).IsComplement' (Subgroup.normalizer (C : Set M)) ∧
        ∃ eN : Subgroup.normalizer (C : Set M) ≃* Gamma,
          ∀ x : Subgroup.normalizer (C : Set M), eN x = e (π x) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_nonmaximal_scalar_cubic_local_normalizer hi hH hp E hm hE he hnonmax

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
