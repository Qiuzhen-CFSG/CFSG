module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtensionOrder
public import Theory.SpecificGroups.Triality.SylowFixerThreeRank
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.LocalKernel

/-!
# Full marked long-root centralizers in the triality extension

An automorphism centralizing a native long-root inner involution fixes the
root element, since the native group is centerless. Its native centralizer
is the arms local factor, so the automorphism preserves that factor and its
normalizer, the arms parabolic. The whole-middle factorization of the same
source extension then places the automorphism in its left endpoint.

Consequently the original ambient long-root centralizer comparison is onto
the full centralizer in that extension. The isomorphism retains the original
full-normalizer map pointwise and sends the distinguished involution to the
pinned native root. The Chapter 12 application selects the constructed marking
from the original comparison. This supplies the long-root centralizer datum
for Thompson's order comparison, without an additional ambient premise.

The short-root model extremality, full ambient short-root containment, and
same-carrier order comparison remain separate obligations.
Source: Aschbacher--Smith F.4.27 and F.4.43, printed pp.288--289 and296,
and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates.Centers
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary
open ChapterF.SourceCompletion

private theorem left_preserves_native
    {X : Type*} [Group X] {P Q : Subgroup X}
    (E : UnitaryNonbinary.SourceExtension P Q)
    (hi : Function.Injective (MulAut.conj : X →* MulAut X))
    (f : MulAut X) (hf : f ∈ E.left) : P.map f.toMonoidHom = P := by
  have hp (a : MulAut X) (ha : a ∈ E.left) (x : X) (hx : x ∈ P) : a x ∈ P := by
    apply (E.conj_mem_left_iff hi _).mp
    have he : MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
      ext y
      simp
    rw [he]
    exact E.left.mul_mem (E.left.mul_mem ha ((E.conj_mem_left_iff hi x).mpr hx))
      (E.left.inv_mem ha)
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hp f hf x hx
  · intro x hx
    exact ⟨f.symm x,hp f⁻¹ (E.left.inv_mem hf) x hx,f.apply_symm_apply x⟩

private theorem left_of_native_stabilizer
    {X : Type*} [Group X] {P Q : Subgroup X}
    (E : UnitaryNonbinary.SourceExtension P Q)
    (hi : Function.Injective (MulAut.conj : X →* MulAut X))
    (hP : normalizer (P : Set X) = P)
    (f : MulAut X) (hf : f ∈ E.carrier) (hs : P.map f.toMonoidHom = P) :
    f ∈ E.left := by
  obtain ⟨g,b,hb,he⟩ := E.factor f hf
  have hg : g ∈ P := by
    rw [←hP,mem_normalizer_iff_map_conj_eq]
    calc
      P.map (MulAut.conj g).toMonoidHom =
          (P.map b.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
            rw [left_preserves_native E hi b hb.1]
      _ = P.map f.toMonoidHom := by rw [map_map,he]; rfl
      _ = P := hs
  rw [he]
  exact E.left.mul_mem ((E.conj_mem_left_iff hi g).mpr hg) hb.1

private theorem automorphism_preserves_centralizer
    {X : Type*} [Group X] (a : MulAut X) (z : X) (hz : a z = z) :
    (centralizer ({z} : Set X)).map a.toMonoidHom = centralizer ({z} : Set X) := by
  have hp (b : MulAut X) (hb : b z = z) (x : X)
      (hx : x ∈ centralizer ({z} : Set X)) : b x ∈ centralizer ({z} : Set X) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg b (mem_centralizer_singleton_iff.mp hx)
    simpa only [map_mul,hb] using hh
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hp a hz x hx
  · intro x hx
    have hi : a.symm z = z := by
      apply a.injective
      rw [a.apply_symm_apply,hz]
    exact ⟨a.symm x,hp a⁻¹ hi x hx,a.apply_symm_apply x⟩

/-- In any genuine triality source extension, the full centralizer of a
nonidentity native highest-root element lies in the marked arms endpoint. -/
theorem triality_extension_highestRoot_centralizer_le_left
    (m : ℕ) (hm : 0 < m) (E : SourceExtension m hm)
    (z : BinaryCarrier m hm) (hz : z ∈ highestRoot (binaryParameters m hm)) (hne : z ≠ 1) :
    centralizer ({E.baseHom z} : Set E.carrier) ≤ E.left.subgroupOf E.carrier := by
  intro a ha
  have hfix : a.val z = z := by
    apply conj_injective m hm
    have he : MulAut.conj (a.val z) = a.val * MulAut.conj z * a.val⁻¹ := by
      ext y
      simp
    rw [he]
    have hh := congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
    change a.val * MulAut.conj z = MulAut.conj z * a.val at hh
    rw [hh,mul_inv_cancel_right]
  have hc := automorphism_preserves_centralizer a.val z hfix
  rw [highestRoot_centralizer_eq_localFactor m hm z hz hne] at hc
  have hP : (parabolic (binaryParameters m hm) .arms).map a.val.toMonoidHom =
      parabolic (binaryParameters m hm) .arms := by
    have hn := map_normalizer_eq_of_bijective
      (localFactor (binaryParameters m hm) .arms) (f := a.val.toMonoidHom) a.val.bijective
    rw [hc,ParabolicOuterTwo.normalizer_localFactor (binaryParameters m hm) rfl .arms] at hn
    exact hn
  exact left_of_native_stabilizer E (conj_injective m hm)
    (normalizer_parabolic_binary _ rfl .arms) a.val a.property hP

variable {G : Type*} [Group G] [Finite G]

/-- Full ambient-to-model long-root centralizer comparison for the same
extension and original endpoint map, including the distinguished involution. -/
theorem Preparation.triality_long_centralizer_full_marked
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e) :
    let P := binaryParameters m hm
    let z := (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val
    ∃ hz : centralizer ({z} : Set G) ≤ normalizer (residual H : Set G),
      ∃ k : centralizer ({z} : Set G) ≃* centralizer
          ({a.extension.baseHom (TrialityCompletionFusion.longElement P rfl).val} :
            Set a.extension.carrier),
        (∀ x, (k x).val = inclusion a.extension.left_le
          (a.comparison.right (inclusion hz x))) ∧
        k ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩ =
          ⟨a.extension.baseHom (TrialityCompletionFusion.longElement P rfl).val,
            mem_centralizer_singleton_iff.mpr rfl⟩ := by
  let P := binaryParameters m hm
  have hroot : (TrialityCompletionFusion.longElement P rfl).val ∈ highestRoot P := by
    change highestHom P rfl (Multiplicative.ofAdd 1) ∈ highestRoot P
    rw [←highestHom_range P rfl]
    exact ⟨_,rfl⟩
  have hne : (TrialityCompletionFusion.longElement P rfl).val ≠ 1 := by
    change highestHom P rfl (Multiplicative.ofAdd 1) ≠ 1
    intro he
    have hh := (highestHom_injective P rfl) (he.trans (map_one (highestHom P rfl)).symm)
    have hz : (1 : fixedField P) = 0 := congrArg Multiplicative.toAdd hh
    exact one_ne_zero hz
  have hc := triality_extension_highestRoot_centralizer_le_left m hm a.extension _ hroot hne
  obtain ⟨hz,k,hk⟩ := d.triality_long_centralizer_marked h hH hp m hm e a
  let f := k.trans (MulEquiv.subgroupCongr (inf_eq_right.mpr hc))
  have hf (x) : (f x).val = inclusion a.extension.left_le
      (a.comparison.right (inclusion hz x)) := hk x
  refine ⟨hz,f,hf,?_⟩
  apply Subtype.ext
  rw [hf]
  apply Subtype.ext
  change (a.comparison.right (inclusion hz _)).val =
    MulAut.conj (TrialityCompletionFusion.longElement P rfl).val
  have hi : inclusion hz ⟨(e.right.symm (TrialityCompletionFusion.longElement P rfl)).val,
      mem_centralizer_singleton_iff.mpr rfl⟩ =
      inclusion a.right_le (e.right.symm (TrialityCompletionFusion.longElement P rfl)) :=
    Subtype.ext rfl
  rw [hi,a.right_marked,e.right.apply_symm_apply]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
