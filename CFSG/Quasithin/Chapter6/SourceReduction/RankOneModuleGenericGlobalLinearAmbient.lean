module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.HallCosets

/-!
# Complete ambient recognition for the prepared maximal linear row

The source centralizer argument, including its exceptional field-four branch,
forces the original source Sylow to be the ambient Sylow and the original
parabolics to generate G. The native torus gives one full odd Hall complement.
Suzuki's invariant-line and coset argument places the cube of the same two
endpoint involutions in that Hall subgroup, hence in the entire original
full-normalizer overlap. The completed marked recognizer now identifies
original G with PSL₃(F), retaining the exact original exponent n>1.

No centralizer, generation, order, smallness, cubic or recognition callback
remains. Both whole-residual comparison orientations and q=4 are included;
maximality of the residual is the original classification-branch premise.
Source: Aschbacher–Smith 5.3.2–7, printed pp.659–661, and F.4.31 specialized
through F.4.45–49 and F.4.8, pp.297–299 and 278–279, `refs/quasithin.pdf`.
The nonmaximal exceptional/M₂₃ row and exhaustive comparison are separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
open Subgroup.OddHall CFSG.Quasithin.Chapter5.Section03LinearSource
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax



/-- The original prepared maximal linear row supplies the cubic witness
on its two actual full normalizers, with escape from their whole overlap. -/
theorem Preparation.linear_hall_cubic_witness :
    ∃ s t : G,
      s∈normalizer (L : Set G) ∧ t∈normalizer (residual H : Set G) ∧
      s∉normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      t∉normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      s^2=1 ∧ t^2=1 ∧ (s*t)^3∈normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  obtain ⟨c,i,hleft,hright,hmid⟩ := d.linear_native_ambient_completion h hH hp F hm hF he hmax
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let N := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  have hf := d.hypothesisF11 h hH.1.1.2
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hPN (j : Fin 2) : P j ⊓ N=C := by
    dsimp only [N]
    rw [←d.linear_common_normalizer_eq h hH hp F hm hF he hmax]
    simpa only [inf_eq_left.mpr (hs j)] using (hf.commonBorel_eq_normalizer j).symm
  have hP₀ : P 0≤normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show L≤P 0 from le_sup_left.trans le_sup_left)).mp
      (hf.local_normal_in_parabolic 0)
  have hP₁ : P 1≤normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show residual H≤P 1 from le_sup_left.trans le_sup_left)).mp
      (hf.local_normal_in_parabolic 1)
  have hsm : c.weyl i∈P 0 := hleft.le (c.weyl_mem i)
  have htm : c.weyl (!i)∈P 1 := hright.le (c.weyl_mem (!i))
  have hout (j : Bool) (k : Fin 2) (hj : c.weyl j∈P k) : c.weyl j∉N := by
    intro hh
    exact c.weyl_not_mem_middle j (hmid.symm ▸ ((hPN k).le ⟨hj,hh⟩))
  refine ⟨c.weyl i,c.weyl (!i),hP₀ hsm,hP₁ htm,hout i 0 hsm,hout (!i) 1 htm,
    c.weyl_sq i,c.weyl_sq (!i),?_⟩
  have hc := (d.linear_native_weyl_cube_mem_hall h hH hp F hm hF he hmax c i hleft hright hmid).1
  rwa [d.linear_sylow_normalizer_eq_inter h hH hp F hm hF he hmax] at hc

/-- Complete prepared maximal-linear ambient recognition. All source centralizer,
Sylow, generation, Hall-coset and cubic premises are discharged internally. -/
theorem Preparation.linear_ambient_recognition_full :
    m=n ∧ 1<m ∧ ClassicalGroup.IsPSL G 3 (2^n) ∧ Nonempty (G ≃* PSL(3,F)) := by
  obtain ⟨s,t,hs,ht,hsout,htout,hs2,ht2,hcube⟩ :=
    d.linear_hall_cubic_witness h hH hp F hm hF he hmax
  exact d.linear_ambient_recognition_of_cube h hH hp F hm hF he hmax
    s t hs ht hsout htout hs2 ht2 hcube

/-- The exact original exponent and an isomorphism of original G with PSL₃(F),
including field four and both whole-residual comparison orientations. -/
theorem Preparation.linear_ambient_recognition :
    m=n ∧ Nonempty (G ≃* PSL(3,F)) := by
  obtain ⟨hmn,_,_,heq⟩ := d.linear_ambient_recognition_full h hH hp F hm hF he hmax
  exact ⟨hmn,heq⟩

/-- The concrete classical-group witness at the unchanged original exponent. -/
theorem Preparation.linear_ambient_isPSL : ClassicalGroup.IsPSL G 3 (2^n) :=
  (d.linear_ambient_recognition_full h hH hp F hm hF he hmax).2.2.1

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
