module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtension.FullNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityAmbientSylow
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Inner
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootPair
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCompletionFusion

/-!
# Odd degree and marked centralizers of the constructed triality extension

The original whole-middle marking identifies the native overlap with the
source common Borel. Since the proved S=T lies in that Borel, its index in
the whole common normalizer is odd. The extension therefore has odd outer
degree, and its native positive subgroup is a Sylow two-subgroup. Every
involution lies in the native inner group and is conjugate to one of the
two pinned root representatives.

For the long root, the source centralizer containment and the exact right
endpoint equation give an isomorphism from the full ambient centralizer
onto the endpoint centralizer inside this same extension carrier. The
isomorphism retains its literal restriction of the original normalizer map.
The Chapter 12 companion instantiates the published constructed marking;
no alternative carrier or ambient recognition hypothesis is introduced.

These are inputs to F.4.43. Short-root model extremality, full short-root
ambient containment and the final same-carrier order comparison remain.
The two-root covering theorem does not assert that the two model classes
are distinct.

Source: Aschbacher--Smith F.4.38 and F.4.40--43, printed pp.294--296,
and 5.3.3, p.659 (`refs/quasithin.pdf`). Internal imports reuse the original
root-center identification without changing its public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary
open ChapterF.SourceCompletion
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The full outer degree is the original common-Borel index in the whole middle. -/
theorem TrialityNormalizerMarking.outer_index_eq_source {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse}
    (a : TrialityNormalizerMarking L K S m hm e) :
    a.extension.nativeOverlap.index =
      (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1).relIndex
        (normalizer (L : Set G) ⊓ normalizer (K : Set G)) := by
  have he : a.extension.nativeOverlap.comap a.comparison.middle.toMonoidHom =
      (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1).subgroupOf
        (normalizer (L : Set G) ⊓ normalizer (K : Set G)) := by
    ext x
    change (a.comparison.middle x).val ∈ UnitaryNonbinary.inner (BinaryCarrier m hm) ↔ _
    rw [a.middle_marked]
    exact a.inner_preimage x
  rw [← a.extension.nativeOverlap.index_comap_of_surjective
    (f := a.comparison.middle.toMonoidHom) a.comparison.middle.surjective,he]
  rfl


omit [Finite G] in
/-- The carrier order retains exactly the source whole-middle extension factor. -/
theorem TrialityNormalizerMarking.card_eq_source
    {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse}
    (a : TrialityNormalizerMarking L K S m hm e) :
    Nat.card a.extension.carrier = Nat.card (BinaryCarrier m hm) *
      (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1).relIndex
        (normalizer (L : Set G) ⊓ normalizer (K : Set G)) := by
  rw [a.extension.carrier_card_eq_base_mul_outer (conj_injective m hm),
    a.outer_index_eq_source]

/-- F.4.38 for the same marked carrier: the original S=T forces odd outer degree. -/
theorem Preparation.triality_extension_outer_odd
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e) :
    ¬ 2 ∣ a.extension.nativeOverlap.index := by
  let C := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
    ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hTC : (T : Subgroup G) ≤ C := by
    rw [← d.triality_sourceS_eq_sylow h hH hp m hm (Or.inr ⟨e⟩)]
    exact le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hCD : C ≤ D := le_inf (inf_le_left.trans a.left_le) (inf_le_right.trans a.right_le)
  have hTD : (T : Subgroup G) ≤ D := hTC.trans hCD
  have hrel : ¬ 2 ∣ (C.subgroupOf D).index := by
    intro hbad
    exact (T.subtype hTD).not_dvd_index
      (hbad.trans (index_dvd_of_le (show (T.subtype hTD : Subgroup D) ≤ C.subgroupOf D from
        fun x hx => hTC hx)))
  rw [TrialityNormalizerMarking.outer_index_eq_source a]
  exact hrel

/-- The native positive subgroup remains Sylow in the full marked extension. -/
theorem Preparation.triality_extension_native_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e) :
    ∃ Q : Sylow 2 a.extension.carrier,
      (Q : Subgroup _) = (unipotent (binaryParameters m hm)).map a.extension.baseHom := by
  let U := unipotent (binaryParameters m hm)
  have hu : IsPGroup 2 U := (unipotentSylow (binaryParameters m hm) rfl).isPGroup'
  have hi : ¬ 2 ∣ (U.map a.extension.baseHom).index := by
    rw [index_map_of_injective _ (a.extension.baseHom_injective (conj_injective m hm)),
      ← a.extension.nativeOverlap_index_eq]
    exact Nat.prime_two.not_dvd_mul (unipotentSylow (binaryParameters m hm) rfl).not_dvd_index
      (d.triality_extension_outer_odd h hH hp m hm e a)
  exact ⟨(hu.map a.extension.baseHom).toSylow hi,rfl⟩

private theorem extension_base_range_normal {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm) :
    E.baseHom.range.Normal := by
  have he : E.baseHom.range =
      (MulAut.innerSubgroup (BinaryCarrier m hm)).subgroupOf E.carrier := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  rw [he]
  infer_instance

/-- Every extension involution has a literal native preimage of order two. -/
theorem Preparation.triality_extension_involution_lift
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e)
    (x : a.extension.carrier) (hx : orderOf x = 2) :
    ∃ v : BinaryCarrier m hm, orderOf v = 2 ∧ a.extension.baseHom v = x := by
  let E := a.extension
  let N := E.baseHom.range
  let : N.Normal := extension_base_range_normal E
  let q := QuotientGroup.mk' N
  have hodd : ¬ 2 ∣ Nat.card (E.carrier ⧸ N) := by
    change ¬ 2 ∣ N.index
    rw [← E.nativeOverlap_index_eq]
    exact d.triality_extension_outer_odd h hH hp m hm e a
  have hd : orderOf (q x) ∣ 2 := by
    rw [← hx]
    exact orderOf_map_dvd q x
  have hqx : q x = 1 := by
    apply orderOf_eq_one_iff.mp
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact h1
    · exact (hodd (h2 ▸ orderOf_dvd_natCard (q x))).elim
  have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp hqx
  obtain ⟨v,hv⟩ := hxN
  refine ⟨v,?_,hv⟩
  rw [← orderOf_injective E.baseHom (E.baseHom_injective (conj_injective m hm)),hv,hx]

/-- The two pinned native roots cover the involutions of the same full extension. -/
theorem Preparation.triality_extension_involution_classes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e)
    (x : a.extension.carrier) (hx : orderOf x = 2) :
    let P := binaryParameters m hm
    IsConj (a.extension.baseHom (TrialityCompletionFusion.longElement P rfl).val) x ∨
      IsConj (a.extension.baseHom (TrialityCompletionFusion.shortElement P rfl).val) x := by
  let P := binaryParameters m hm
  obtain ⟨v,hv2,rfl⟩ := d.triality_extension_involution_lift h hH hp m hm e a x hx
  obtain ⟨u,hu2,hvu⟩ := Triality.Standard.EvenInvolutionGeometry.involution_isConj_unipotent
    m hm (unipotentSylow P rfl) rfl v hv2
  let w : parabolic P .arms := ⟨u.val,(unipotent_le_borel P).trans (borel_le_parabolic P .arms) u.property⟩
  have hw2 : orderOf w = 2 := (Subgroup.orderOf_coe w).symm.trans hu2
  have hc := TrialityCompletionFusion.compatible_involution_classes m hm
    (parabolic P .arms).subtype (parabolic P .central).subtype (fun _ _ _ _ => rfl)
    w u.property hw2
  rcases hc with hz | ht
  · exact Or.inl (a.extension.baseHom.map_isConj (hz.trans hvu.symm))
  · exact Or.inr (a.extension.baseHom.map_isConj (ht.trans hvu.symm))

private theorem marked_centralizer_equiv
    {X Y : Type*} [Group X] [Group Y]
    (N : Subgroup X) (J : Subgroup Y) (f : N ≃* J) (z : N)
    (hc : centralizer ({z.val} : Set X) ≤ N) :
    ∃ k : centralizer ({z.val} : Set X) ≃*
        (J ⊓ centralizer ({(f z).val} : Set Y) : Subgroup Y),
      ∀ x, (k x).val = (f (inclusion hc x)).val := by
  let F : centralizer ({z.val} : Set X) →* Y :=
    J.subtype.comp (f.toMonoidHom.comp (inclusion hc))
  have hF : Function.Injective F :=
    J.subtype_injective.comp (f.injective.comp (inclusion_injective hc))
  let R := J ⊓ centralizer ({(f z).val} : Set Y)
  have hFR (x : centralizer ({z.val} : Set X)) : F x ∈ R := by
    refine ⟨(f (inclusion hc x)).property,mem_centralizer_singleton_iff.mpr ?_⟩
    have hh : inclusion hc x * z = z * inclusion hc x :=
      Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
    exact congrArg Subtype.val (by simpa only [map_mul] using congrArg f hh)
  let k : centralizer ({z.val} : Set X) →* R := F.codRestrict R hFR
  have hks : Function.Surjective k := by
    intro y
    let u : N := f.symm ⟨y.val,y.property.1⟩
    have hfu : f u = ⟨y.val,y.property.1⟩ := f.apply_symm_apply _
    have huc : u.val ∈ centralizer ({z.val} : Set X) := by
      apply mem_centralizer_singleton_iff.mpr
      change (u*z).val = (z*u).val
      apply congrArg (fun v : N => v.val)
      apply f.injective
      rw [map_mul,map_mul,hfu]
      exact Subtype.ext (mem_centralizer_singleton_iff.mp y.property.2)
    refine ⟨⟨u.val,huc⟩,?_⟩
    apply Subtype.ext
    change (f ⟨u.val,hc huc⟩).val = y.val
    exact congrArg (fun v : J => v.val) hfu
  exact ⟨MulEquiv.ofBijective k ⟨fun _ _ hh => hF
    (congrArg (fun v : R => v.val) hh),hks⟩,
    fun _ => rfl⟩

/-- The full ambient long centralizer is the marked endpoint centralizer inside
the very same extension carrier, with its map retained pointwise. -/
theorem Preparation.triality_long_centralizer_marked
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
      ∃ k : centralizer ({z} : Set G) ≃*
        (a.extension.left.subgroupOf a.extension.carrier ⊓ centralizer
          ({a.extension.baseHom (TrialityCompletionFusion.longElement P rfl).val} :
            Set a.extension.carrier) : Subgroup _),
        ∀ x, (k x).val = inclusion a.extension.left_le
          (a.comparison.right (inclusion hz x)) := by
  let P := binaryParameters m hm
  let w := e.right.symm (TrialityCompletionFusion.longElement P rfl)
  let z : G := w.val
  have hzK : z ∈ (center (residual H)).map (residual H).subtype := by
    have hZ := (triality_comparison_images d h hH.1.1.2 hp P rfl e).1
    rw [← hZ]
    refine ⟨Multiplicative.ofAdd (1 : fixedField P),?_⟩
    change (e.right.symm (TrialityRootPair.longHom P rfl 2 (Multiplicative.ofAdd 1))).val = z
    exact congrArg (fun x => (e.right.symm x).val)
      (Subtype.ext (TrialityRootPair.long_two_eq P rfl 1))
  have hz2 : orderOf z = 2 := by
    rw [show z = (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val from rfl,
      Subgroup.orderOf_coe,e.right.symm.orderOf_eq]
    exact triality_longElement_order P rfl
  have hc : centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) :=
    d.triality_central_involution_centralizers h hH hp m hm (Or.inr ⟨e⟩) 1 z hzK hz2
  let zN := inclusion a.right_le w
  let J := a.extension.left.subgroupOf a.extension.carrier
  let f : normalizer (residual H : Set G) ≃* J :=
    a.comparison.right.trans (subgroupOfEquivOfLe a.extension.left_le).symm
  have he : (f zN).val =
      a.extension.baseHom (TrialityCompletionFusion.longElement P rfl).val := by
    apply Subtype.ext
    change (a.comparison.right zN).val =
      MulAut.conj (TrialityCompletionFusion.longElement P rfl).val
    rw [a.right_marked,e.right.apply_symm_apply]
  refine ⟨hc,?_⟩
  change ∃ k : centralizer ({zN.val} : Set G) ≃*
      (J ⊓ centralizer ({a.extension.baseHom (TrialityCompletionFusion.longElement P rfl).val} :
        Set a.extension.carrier) : Subgroup _),
    ∀ x, (k x).val = (f (inclusion hc x)).val
  rw [←he]
  exact marked_centralizer_equiv (normalizer (residual H : Set G)) J f zN hc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
