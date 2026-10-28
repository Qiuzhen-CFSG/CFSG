module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootPair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSpecialIntersection

/-!
# The triality root pair in the original chosen-module setup

The genuine compatible triality comparison supplies a highest short-root
involution in Q = O₂(O²(H)), marked by the same right parabolic map.
Two actual ambient conjugates of Z(O²(H)) lie in Q and centralize it;
their join has Frattini subgroup Z(O²(H)). The coordinate fixed-space
calculation supplies a mover in the original S = O₂(N_G(L) ∩ H).
TI then makes the pair centralize every conjugate root containing the
marked involution. The intersection counts and saturation give a contradiction
if both source placements hold. These are constructions, with no added pair
or mover premise. Both parabolic maps and their agreement on the whole overlap
are retained.

The two Sylow placements and preservation of the short-root information
through those conjugations remain to be proved. Original uniqueness in
Preparation and the compatible comparison remain explicit; exhaustive
comparison and ambient completion recognition are still required.
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

/-- The original triality core supplies the centralizing root pair, its exact
Frattini subgroup, the nonfixed short-root image, and the TI consequence. -/
theorem rankOne_global_triality_special_core_root_pair
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse,
      ∃ v ∈ Q,
      (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val = v ∧ (e.right w).val = _root_.Triality.Standard.RadicalCoordinates.LeviCommutators.short
          (_root_.Triality.Standard.binaryParameters m hm) rfl 2 1) ∧
      v ∉ Z ∧ orderOf v = 2 ∧
      (∃ x ∈ Global.sourceS L H, ⁅x,v⁆ ∉ Z) ∧ ∃ r s : G,
      let U := Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom
      U ≤ Q ∧ U ≤ centralizer ({v} : Set G) ∧ (frattini U).map U.subtype = Z ∧
      (∀ g : G, v ∈ Z.map (MulAut.conj g).toMonoidHom →
        U ≤ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      (∀ g : G, v ∈ Z.map (MulAut.conj g).toMonoidHom →
        Z ≤ Q.map (MulAut.conj g).toMonoidHom →
        ¬ Q.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Z : Set G) ≤ Global.sourceS L H) := by
  exact d.triality_special_core_root_pair
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
