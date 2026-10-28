module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Fusion
public import Theory.SpecificGroups.ReeF4.SourceCompletion.InvolutionReduction

/-!
# Reduced native coordinates on the original Ree marking

An involution in the full common normalizer maps into the inner subgroup of
its same marked extension, whose outer degree is odd. Both endpoint tests
put the native element in the Borel, hence in its normal positive Sylow.
The Suzuki-Levi square calculation therefore applies to this very element:
its first main coordinate is zero, and it is the central first-root curve
times an element of the literal Suzuki radical.

Every ambient involution has such a representative in the original T. The
construction retains both comparison orientations, both full endpoints and
the whole overlap. It adds no class, conjugacy, or coordinate hypothesis.
Classifying the remaining radical factor into the two root classes is still
required for F.4.27 and the converse fusion application; this reduction does
not assert exhaustion or ambient recognition.
Source: Aschbacher–Smith 5.3.1–3 and F.4.27,35, printed pp.658–659,288,291–292
(`refs/quasithin.pdf`); GLS3 Table 2.4 and 2.4.5(d).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ReeF4.NormalizedRootCentralizers.CenterExponent
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
include d h hp

/-- The native element of every full-overlap involution is already positive
and has central first Suzuki-Levi factor, under the literal same marking. -/
theorem Preparation.ree_middle_involution_normal_form
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    (hy : orderOf y.val = 2) :
    ∃ (t : ReeF4.Model m) (p : PositiveParameters m)
      (r : ReeF4.Parabolics.radical m .suzuki),
      orderOf t = 2 ∧ t ∈ ReeF4.Parabolics.unipotent m ∧
      D.middleToCarrier y = D.extension.baseHom t ∧
      p.main 0 = 0 ∧ ReeF4.toSplitGroup m t = positiveWord m p ∧
      t = ReeF4.ElementaryTwoBound.centralElement m 0 (p.central 0) * r.val := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  have hi : Function.Injective D.middleToCarrier :=
    (inclusion_injective (inf_le_left.trans D.extension.left_le)).comp D.full.middle.injective
  have hyE : orderOf (D.middleToCarrier y) = 2 :=
    (orderOf_injective _ hi y).trans ((Subgroup.orderOf_coe y).symm.trans hy)
  obtain ⟨t,ht,hyt⟩ := GeneralReeFour.extension_involution_native D.extension hm _ hyE
  have hc : MulAut.conj t = (D.full.middle y).val := congrArg Subtype.val hyt
  have hleft : t ∈ ReeF4.Parabolics.parabolic m .linear := by
    apply (D.extension.conj_mem_left_iff (ReeF4.SmallCompletion.conj_injective m hm) t).mp
    rw [hc]
    exact (D.full.middle y).property.1
  have hright : t ∈ ReeF4.Parabolics.parabolic m .suzuki := by
    apply (D.extension.conj_mem_right_iff (ReeF4.SmallCompletion.conj_injective m hm) t).mp
    rw [hc]
    exact (D.full.middle y).property.2
  have hb : t ∈ ReeF4.Parabolics.borel m :=
    (ReeFour.overlap m).le ⟨hright,hleft⟩
  have hu := ReeF4.SourceCompletion.involution_mem_unipotent_of_mem_borel m t hb ht
  obtain ⟨p,r,hp,h0,hr⟩ := ReeF4.SourceCompletion.positive_involution_suzuki_factor m
    ⟨t,hu⟩ (orderOf_eq_prime_iff.mp ht).1
  exact ⟨t,p,r,ht,hu,hyt.symm,h0,hp,hr⟩

variable
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include hH he

/-- The original Sylow representative has the reduced native word under the
same full common-normalizer marking, with no extra conjugator or premise. -/
theorem Preparation.ree_involution_suzuki_representative
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (x : G) (hx : orderOf x = 2) :
    ∃ (y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
      (t : ReeF4.Model m) (p : PositiveParameters m)
      (r : ReeF4.Parabolics.radical m .suzuki),
      y.val ∈ (T : Subgroup G) ∧ IsConj x y.val ∧
      orderOf t = 2 ∧ t ∈ ReeF4.Parabolics.unipotent m ∧
      D.middleToCarrier y = D.extension.baseHom t ∧
      p.main 0 = 0 ∧ ReeF4.toSplitGroup m t = positiveWord m p ∧
      t = ReeF4.ElementaryTwoBound.centralElement m 0 (p.central 0) * r.val := by
  obtain ⟨y,_,hy,_,hxy,_⟩ := d.ree_involution_native_representative h hH hp m he D x hx
  have hy2 : orderOf y.val = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hxy
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  obtain ⟨t,p,r,ht,hu,hmark,h0,hword,hfactor⟩ :=
    d.ree_middle_involution_normal_form h hp m D y hy2
  exact ⟨y,t,p,r,hy,hxy,ht,hu,hmark,h0,hword,hfactor⟩

/-- Both original orientations yield one full extension whose original Sylow
representatives satisfy the native Suzuki-Levi coordinate reduction. -/
theorem Preparation.ree_full_extension_involution_normal_forms :
    2*m+1 = n ∧ 0 < m ∧
    ∃ D : ReeNormalizerMarking L (residual H) (sourceS L H) m,
      ∀ x : G, orderOf x = 2 →
        ∃ (y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
          (t : ReeF4.Model m) (p : PositiveParameters m)
          (r : ReeF4.Parabolics.radical m .suzuki),
          y.val ∈ (T : Subgroup G) ∧ IsConj x y.val ∧
          orderOf t = 2 ∧ t ∈ ReeF4.Parabolics.unipotent m ∧
          D.middleToCarrier y = D.extension.baseHom t ∧
          p.main 0 = 0 ∧ ReeF4.toSplitGroup m t = positiveWord m p ∧
          t = ReeF4.ElementaryTwoBound.centralElement m 0 (p.central 0) * r.val := by
  obtain ⟨hn,hm,⟨D⟩⟩ := d.ree_full_normalizer_marking h hH hp m he
  exact ⟨hn,hm,D,fun x hx => d.ree_involution_suzuki_representative h hp m hH he D x hx⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
