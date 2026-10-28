module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2OuterInvolution

/-!
# Centralizer decomposition for the original Chapter 12 outer involution

The same pulled-back Hall torus and right-quotient field marking now give
C_T(t) = C_S(t) N_T(D), with exact order |C_S(t)| [T:S] and [T:S] dividing n.
The field coefficient's fixed field has square-root order. The displayed six-root action also gives |C_S(t)| ≤ q³ and
|C_T(t)| < q⁴. Constructing that action identity and proving ambient
centralizer Sylow placement remain required.

Source: Aschbacher–Smith F.4.37–38, printed pp.293–294, and 5.3.3, p.659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original torus complement centralizes the selected actor and supplies its exact extension factor. -/
theorem rankOne_global_g2_outer_torus_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} {Y : Subgroup G}
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : Y ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ Atlas.G2.splitTorus)
    (t : T) (ht : t.val ∈ normalizer (Y : Set G)) :
    let U := (T : Subgroup G) ⊓ normalizer (Y : Set G)
    U ≤ centralizer ({t.val} : Set G) ∧
      ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Set G) =
        ((Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) : Set G) * (U : Set G) ∧
      Nat.card U = (Global.sourceS L H).relIndex (T : Subgroup G) ∧
      Nat.card U ∣ n ∧ Nat.card U < Nat.card F ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
        Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) *
          (Global.sourceS L H).relIndex (T : Subgroup G) :=
  d.g2_outer_torus_centralizer (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp F e hD hmark t ht

/-- The original outer involution has a square-root fixed field and the computed centralizer extension factor. -/
theorem rankOne_global_g2_exists_outer_involution_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G}
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hne : Global.sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H)
    ∃ Y : Subgroup G, Y ≤ C ∧ IsHallSubgroup oddPrimes (Y.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ Atlas.G2.splitTorus) ∧
      ∃ eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F,
      ∃ t : T, orderOf t=2 ∧ t.val ∉ Global.sourceS L H ∧
        t.val ∈ normalizer (Y : Set G) ∧ orderOf (Global.residualSylowFieldAction hH.1.1.2 eR t)=2 ∧
        Nat.card (FixedBy.subfield F (Global.residualSylowFieldAction hH.1.1.2 eR t))^2=Nat.card F ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
          Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) *
            (Global.sourceS L H).relIndex (T : Subgroup G) ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤
          Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) * n :=
  d.g2_exists_outer_involution_centralizer (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp F e hne

/-- The displayed original root action gives the strict centralizer order
bound. This retains the root-action premise and does not assert ambient Sylow placement. -/
theorem rankOne_global_g2_outer_involution_centralizer_lt_of_root_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B Y : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : Y ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2) (htS : t.val ∉ Global.sourceS L H)
    (htD : t.val ∈ normalizer (Y : Set G))
    (ρ : Fin 6 → F ≃+ F)
    (hroot : ∀ v : Fin 6 → F,
      t.val * (e.right.symm ⟨unipotentProduct v,
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem v))⟩).val * t.val⁻¹ =
      (e.right.symm ⟨unipotentProduct (fun i => ρ i (v i)),
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩).val) :
    Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ Nat.card F^3 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < Nat.card F^4 :=
  d.g2_outer_involution_centralizer_lt_of_root_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e hD hmark t ht2 htS htD ρ hroot

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
