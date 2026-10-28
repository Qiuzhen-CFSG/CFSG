module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticCompletion

/-!
# Ambient symplectic local inputs for the original Chapter 12 pair

The source core-center normalizers, root-involution centralizers, odd middle
index and ambient two-perfectness apply to W = wholeReduced T L. The whole
residual of H and the same compatible pure amalgam comparison are retained,
in either orientation and including exponent two.

The extended application also proves characteristic two for every
involution centralizer in the actual Z(S), and both root TI conclusions.
Thus all ambient clauses (a)–(e) of F.4.31 and the symplectic F.4.34
conclusions hold for this prepared pair. The full-normalizer extension,
ambient fusion, outer transfer, third centralizer containment and ambient
order comparison remain necessary before applying the symplectic extension
completion theorem without extra inputs.

Source: Aschbacher–Smith 5.3.1–3, printed pp.658–659; F.4.31–34, p.291;
and the original Chapter 12 application, p.795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply the proved ambient local inputs to the original chosen module,
without a supplied symplectic extension or ambient order bound. -/
theorem rankOne_global_symplectic_source_local_inputs
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
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
    (∀ i : Fin 2,
      let P := ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i
      P.pCoreIn 2 = (![L,residual H] i).pCoreIn 2 ∧
      normalizer ((center (P.pCoreIn 2)).map (P.pCoreIn 2).subtype : Set G) =
        normalizer (![L,residual H] i : Set G)) ∧
    (∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G)) ∧
    Odd (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G).index ∧
    IsPPerfect 2 G :=
  d.symplectic_source_local_inputs (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he

/-- Apply all F.4.31 ambient clauses and both root TI conclusions to the original chosen module,
without a supplied symplectic extension or ambient order bound. -/
theorem rankOne_global_symplectic_source_ambient_inputs
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
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
    (∀ i : Fin 2,
      let P := ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i
      P.pCoreIn 2 = (![L,residual H] i).pCoreIn 2 ∧
      normalizer ((center (P.pCoreIn 2)).map (P.pCoreIn 2).subtype : Set G) =
        normalizer (![L,residual H] i : Set G)) ∧
    (∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G)) ∧
    (∀ z ∈ (center (Global.sourceS L H)).map (Global.sourceS L H).subtype, orderOf z = 2 →
      generalizedFitting (centralizer ({z} : Set G)) =
        pCore 2 (centralizer ({z} : Set G))) ∧
    Odd (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G).index ∧
    IsPPerfect 2 G ∧
    (∀ i : Fin 2,
      IsElementaryAbelian 2 ((center (![L,residual H] i)).map (![L,residual H] i).subtype) ∧
      ChapterI.Section06To08.IsTISubgroup
        ((center (![L,residual H] i)).map (![L,residual H] i).subtype) ∧
      normalizer ((center (![L,residual H] i)).map (![L,residual H] i).subtype : Set G) =
        normalizer (![L,residual H] i : Set G)) :=
  d.symplectic_source_ambient_inputs (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
