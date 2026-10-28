module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2OuterRootAction

/-!
# The original outer involution's centralizer normalizer

The actual root action puts the nontrivial characteristic central-derived
subgroup of E = C_T(t) in the right factor's highest-root center. Its TI
geometry forces N_G(E) into N_G(O²(H)). Together with the ambient q⁴ lower
bound and |E| < q⁴, the normalizer condition now produces a strict local
two-group enlargement of E. This is a concrete consequence of the original
chosen-module hypotheses, with the same torus and quotient field marking.
Excluding that enlargement, hence proving S=T, still requires the local
centralizer Sylow argument. Original uniqueness and exhaustive comparison
remain with the generic-global assembly.

Source: Aschbacher–Smith F.4.37–38, pp.293–294, and 5.3.3, p.659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The source characteristic central-derived subgroup is nontrivial and
forces the full normalizer of C_T(t) into the original right normalizer. -/
theorem rankOne_global_g2_outer_centralizer_normalizer
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
    (t : T) (ht2 : orderOf t=2)
    (htD : t.val ∈ normalizer (Y : Set G)) :
    let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
    let Z := (center E ⊓ commutator E).map E.subtype
    Z ≠ ⊥ ∧ Z ≤ (center (residual H)).map (residual H).subtype ∧
      normalizer (E : Set G) ≤ normalizer (residual H : Set G) :=
  d.g2_outer_centralizer_normalizer
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e hD hmark t ht2 htD

/-- A proper original core supplies the same actual outer involution, torus
marking, order-two quotient field action strict centralizer bound, and a strict local centralizer enlargement. -/
theorem rankOne_global_g2_exists_outer_involution_local_enlargement
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
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
        t.val ∈ normalizer (Y : Set G) ∧
        orderOf (Global.residualSylowFieldAction hH.1.1.2 eR t)=2 ∧
        Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ Nat.card F^3 ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < Nat.card F^4 ∧
        ∃ R : Subgroup G, IsPGroup 2 R ∧
          (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) < R ∧
          R ≤ normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G) ∧
          R ≤ normalizer ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Set G) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨Y,hY,hHall,hmark,eR,t,ht,htS,htY,hσ,hS,hT⟩ :=
    d.g2_exists_outer_involution_small_centralizer hi hH hp F e hne
  exact ⟨Y,hY,hHall,hmark,eR,t,ht,htS,htY,hσ,hS,hT,
    d.g2_outer_involution_local_enlargement hi hH hp F e hY hmark t ht htS htY⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
