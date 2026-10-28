module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2RootPair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSpecialIntersection

/-!
# The G₂ root pair in the original chosen-module setup

The compatible G₂ comparison constructs a short-root involution in the
actual right core Q = O₂(O²(H)), retaining its literal C-root marking
under the compatible parabolic map. Two ambient conjugates of Z(O²(H)) lie
in Q and centralize that involution, and the Frattini subgroup of their
join is precisely Z(O²(H)). A literal element of the original S moves
the involution modulo Z. The established TI theorem makes the entire
join centralize every conjugate root containing the selected involution.

This discharges the G₂ root-pair and nonfixed-image calculations used
in F.4.35; neither is a new premise. The existing counts and saturation
then contradict fusion once both Sylow placements hold. The centralizer
conjugations giving those placements, transport of the selected short-root
representative through them, the triality pair, and final nonfusion still
remain. Original uniqueness in Preparation and the compatible comparison
remain inputs; exhaustive comparison and ambient recognition are unproved.
Source: Aschbacher–Smith F.4.35, printed p.292, 5.3.3, p.659, and the
Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original G₂ core supplies the centralizing root pair, its exact
Frattini subgroup, the nonfixed short-root image, and the TI consequence. -/
theorem rankOne_global_g2_special_core_root_pair
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
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse,
      ∃ v ∈ Q,
      (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val = v ∧ (e.right w).val = Atlas.G2.rootC (1:F)) ∧
      v ∉ Z ∧ orderOf v = 2 ∧
      (∃ x ∈ Global.sourceS L H, ⁅x,v⁆ ∉ Z) ∧ ∃ r s : G,
      let U := Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom
      U ≤ Q ∧ U ≤ centralizer ({v} : Set G) ∧ (frattini U).map U.subtype = Z ∧
      (∀ g : G, v ∈ Z.map (MulAut.conj g).toMonoidHom →
        U ≤ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      (∀ g : G, v ∈ Z.map (MulAut.conj g).toMonoidHom →
        Z ≤ Q.map (MulAut.conj g).toMonoidHom →
        ¬ Q.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Z : Set G) ≤ Global.sourceS L H) := by
  exact d.g2_special_core_root_pair
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
