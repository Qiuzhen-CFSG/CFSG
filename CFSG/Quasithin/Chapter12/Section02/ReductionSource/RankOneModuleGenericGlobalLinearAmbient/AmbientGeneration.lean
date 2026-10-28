module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.AmbientGeneration
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.FullNormalizer

/-!
# All-degree linear ambient generation for the original chosen module

The unchanged Chapter12 hypotheses now prove S=T and generation of G by
both original pairs, including q=4. The same full-normalizer realization
therefore gives a faithful completion in original G with its whole overlap.
The centralizer core and central-line disjointness also hold at every degree.

The final GlobalExit application still explicitly requires the source
endpoint cubic witness. The Hall-torus argument producing that witness
remains with the ambient-row owner; this module does not assert unconditional
linear recognition.
Source: Aschbacher–Smith F.4.37–38,45–46, pp.293–294,297, using 5.3.7,
pp.660–661, applied to 12.2, p.795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
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


/-- Both original pairs generate G, and the source Sylow is the original T,
including field four and both orientations. -/
theorem rankOne_global_linear_ambient_generation :
    Global.sourceS L H = (T : Subgroup G) ∧
    normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
    L ⊔ residual H = ⊤ := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.linear_sourceS_eq_sylow hi hH hp F hm hF he hmax,
    d.linear_ambient_generation hi hH hp F hm hF he hmax⟩

/-- The exact centralizer core and Sylow normalizer are the original groups. -/
theorem rankOne_global_linear_involution_centralizer_core
    (z : G) (hz : orderOf z=2) (hzS : z ∈ centerIn (Global.sourceS L H)) :
    (centralizer ({z} : Set G)).pCoreIn 2 = (T : Subgroup G) ∧
    normalizer (T : Set G) = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨(d.linear_centralizer_core_eq_sourceS hi hH hp F hm hF he hmax z hz hzS).trans
    (d.linear_sourceS_eq_sylow hi hH hp F hm hF he hmax),
    d.linear_sylow_normalizer_eq_inter hi hH hp F hm hF he hmax⟩

/-- Distinct ambient conjugates of the original central line are disjoint. -/
theorem rankOne_global_linear_center_TI (g : G) :
    (centerIn (Global.sourceS L H)).map (MulAut.conj g).toMonoidHom =
      centerIn (Global.sourceS L H) ∨
    Disjoint (centerIn (Global.sourceS L H))
      ((centerIn (Global.sourceS L H)).map (MulAut.conj g).toMonoidHom) :=
  d.linear_center_TI (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax g

/-- A faithful completion in original G with the whole full-normalizer overlap;
no ambient-generation premise remains. -/
theorem rankOne_global_linear_ambient_completion :
    let a := d.linearNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp F hm hF he hmax
    ∃ c : ChapterF.SourceCompletion.LinearThreeEven.Completion a.extension G,
      c.middle.range = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      c.left.range ⊓ c.right.range = c.middle.range :=
  d.linear_ambient_completion (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax

/-- The actual source endpoint cube witness is the sole remaining extra input
for the prepared maximal linear GlobalExit. Its construction remains owed. -/
theorem rankOne_globalExit_of_linear_cube
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (residual H : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    RankOneModule.GlobalExit G := by
  obtain ⟨_,_,hpslG,_⟩ := d.linear_ambient_recognition_of_cube
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hmax
    s t hs ht hsout htout hs2 ht2 hcube
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.linear (by omega) hpslG⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
