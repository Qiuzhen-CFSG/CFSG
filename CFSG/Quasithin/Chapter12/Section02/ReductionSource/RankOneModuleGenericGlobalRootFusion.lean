module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRootFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityCentralizers

/-!
# Root TI and conjugate-pair control for the original rank-one setup

The actual G₂ and triality comparisons identify a nontrivial central
involution in K = O²(H). The right parabolic orbit and ambient centralizer
bound prove that Z(K) is elementary abelian and TI, with full normalizer
N_G(K). I.6.2 then turns point centralization by two conjugate centers
into centralization of the whole third conjugate, the input used in F.4.35.

All groups are those of the literal Chapter12 application. Original
uniqueness in Preparation and the compatible comparison remain explicit;
exhaustive comparison, involution nonfusion and completion recognition are
still required for GlobalExit. The source S and whole overlap are retained.
Source: Aschbacher–Smith F.4.34–35, printed pp.291–292, 5.3.3, p.659,
and the Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original G₂ pair satisfies the TI and conjugate-root centralization
steps of F.4.34–35, with no additional fusion hypothesis. -/
theorem rankOne_global_g2_root_fusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse)) :
    let Z := (center (residual H)).map (residual H).subtype
    IsElementaryAbelian 2 Z ∧ IsTISubgroup Z ∧
    normalizer (Z : Set G) = normalizer (residual H : Set G) ∧
    ∀ g r s a : G, a ∈ Z.map (MulAut.conj g).toMonoidHom → a ≠ 1 →
      Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom ≤
        centralizer ({a} : Set G) →
      Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom ≤
        centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hf := d.g2_right_center_fusion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he
  let := hf.1
  refine ⟨hf.1,hf.2.1,hf.2.2,?_⟩
  intro g r s a ha ha1 hpair
  exact Global.center_conjugate_pair hf.2.1 g r s a ha ha1
    (le_sup_left.trans hpair) (le_sup_right.trans hpair)

/-- The same source fusion steps for the genuine graph-field triality pair,
including the exact original center and both possible comparison orientations. -/
theorem rankOne_global_triality_root_fusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    let Z := (center (residual H)).map (residual H).subtype
    IsElementaryAbelian 2 Z ∧ IsTISubgroup Z ∧
    normalizer (Z : Set G) = normalizer (residual H : Set G) ∧
    ∀ g r s a : G, a ∈ Z.map (MulAut.conj g).toMonoidHom → a ≠ 1 →
      Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom ≤
        centralizer ({a} : Set G) →
      Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom ≤
        centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hf := d.triality_right_center_fusion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he
  let := hf.1
  refine ⟨hf.1,hf.2.1,hf.2.2,?_⟩
  intro g r s a ha ha1 hpair
  exact Global.center_conjugate_pair hf.2.1 g r s a ha ha1
    (le_sup_left.trans hpair) (le_sup_right.trans hpair)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
