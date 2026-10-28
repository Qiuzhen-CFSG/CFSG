module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CentralFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialTransfer

/-!
# Involution fusion at every degree in the prepared linear row

The actual action of T on the right factor quotient has cyclic field image
and kernel the original S. Generalized Thompson transfer in the original
simple group therefore fuses every ambient involution into S. The two
affine root planes then fuse it to a nonzero element of Z(S). This proves
one ambient involution class without an odd-degree assumption, including
field four and both orientations. The same field action gives [T:S] ∣ n.

No equality S=T or ambient recognition is asserted here. Individual
involution-centralizer containment and the exceptional marked Sylow
argument remain obligations of the prepared ambient recognition theorem.
Source: Aschbacher–Smith A.1.37(2), F.4.38, F.4.46(1), and §5.3.7,
printed pp.31,294,297,660 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
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

omit hmax in
/-- The actual source Sylow index divides the original exponent, in either orientation. -/
theorem Preparation.linear_source_sylow_index_dvd :
    (sourceS L H).relIndex (T : Subgroup G) ∣ n := by
  obtain ⟨_,_,_,_,_,_,hpsl,_⟩ :=
    (d.linear_amalgam_blocks h hH.1.1.2 hp F hm hF he).2.2
  exact d.residual_sylow_index_dvd h hH.1.1.2
    (d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he) hpsl

omit hmax in
/-- Cyclic field-action transfer fuses every ambient involution into the original S. -/
theorem Preparation.linear_involution_fused_into_sourceS
    (x : G) (hx : orderOf x = 2) :
    ∃ y ∈ sourceS L H, IsConj x y := by
  obtain ⟨_,_,_,_,_,_,hpsl,_⟩ :=
    (d.linear_amalgam_blocks h hH.1.1.2 hp F hm hF he).2.2
  exact d.residual_involution_fused_into_sourceS h hH.1.1.2
    (d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he) hpsl x hx

/-- Every ambient involution is conjugate to the same nonzero central-line element,
including even field degrees and field four. -/
theorem Preparation.linear_involution_isConj_central
    (z : G) (hz : z ∈ centerIn (sourceS L H)) (hz1 : z ≠ 1)
    (x : G) (hx : orderOf x = 2) : IsConj z x := by
  obtain ⟨y,hy,hxy⟩ := d.linear_involution_fused_into_sourceS h hH hp F hm hF he x hx
  have hy2 : orderOf y = 2 := by
    obtain ⟨a,ha⟩ := isConj_iff.mp hxy
    rw [←ha]
    exact ((MulAut.conj a).orderOf_eq x).trans hx
  obtain ⟨g,_,hg⟩ := d.linear_sourceS_involution_fused h hH hp F hm hF he hmax z hz hz1 y hy hy2
  exact (isConj_iff.mpr ⟨g,hg⟩).trans hxy.symm

/-- The prepared maximal linear ambient group has one involution class at every degree. -/
theorem Preparation.linear_involutions_isConj
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨z,hz,hz2,_⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz2
  exact (d.linear_involution_isConj_central h hH hp F hm hF he hmax z hz hz1 x hx).symm.trans
    (d.linear_involution_isConj_central h hH hp F hm hF he hmax z hz hz1 y hy)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
