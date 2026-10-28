module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionIntersection
public import Theory.SpecificGroups.Triality.ArmsFixedQuotient

/-!
# The original core's Sylow-fixed elements have long-root images

The whole-overlap square lifts the model unipotent group to the original
Sylow. Compatibility of the core equivalence with the first endpoint then
transports the explicit coordinate calculation on Q/Z. A nonidentity core
element fixed modulo its center has genuine long-root image. In the mutual
core-incidence case the preceding extraspecial counting theorem therefore
produces such an image after conjugation inside the original Mc.

The earlier marked realization remains explicit. This is the fixed-space
step of Aschbacher--Smith F.4.35, printed p.292, in the original 14.2.18--19
setup, printed p.987. Excluding the resulting Mc-orbit intersection and
recognizing the ambient group remain with qt-e-14315-eight-borel-exclusion.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.RadicalCoordinates.Centers
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
open _root_.Triality.Standard.EvenInvolutionGeometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

omit [Finite G] in
/-- The core equivalence uses the literal first endpoint inclusion. -/
theorem firstCoreEquiv_val (r : MarkedTriality T M Mc H) (q : H.pCoreIn 2) :
    (firstCoreEquiv r q : Carrier (binaryParameters 1 Nat.zero_lt_one)) =
      (r.left ⟨q,pCoreIn_le 2 H q.property⟩ : Carrier (binaryParameters 1 Nat.zero_lt_one)) := by
  let f := (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have he : H.subtype (f.symm q : H)=(q:G) := by
    have hh := congrArg Subtype.val (f.apply_symm_apply q)
    exact (coe_equivMapOfInjective_apply _ _ _ _).symm.trans hh
  have hq : (f.symm q : H)=⟨q,pCoreIn_le 2 H q.property⟩ := Subtype.ext he
  change (r.left (f.symm q : H) : Carrier (binaryParameters 1 Nat.zero_lt_one)) = _
  rw [hq]

private theorem inclusion_amalgam_lift {L R : Type*} [Group L] [Group R]
    (A B C : Subgroup L) (hA : B ≤ A) (hC : B ≤ C)
    (A' B' C' : Subgroup R) (hA' : B' ≤ A') (hC' : B' ≤ C')
    (r : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups A B C hA hC)
      (RankTwoAmalgam.ofSubgroups A' B' C' hA' hC'))
    (S : Subgroup L) (u : R)
    (hu : u∈((S.subgroupOf B).map r.middle.toMonoidHom).map B'.subtype) :
    ∃ x : A, (x:L)∈S ∧ (r.left x : R)=u := by
  obtain ⟨b,⟨y,hy,hb⟩,hbu⟩ := hu
  refine ⟨(RankTwoAmalgam.ofSubgroups A B C hA hC).left y,hy,?_⟩
  have he := congrArg A'.subtype (r.left_commutes y)
  exact he.trans ((congrArg B'.subtype hb).trans hbu)

/-- The whole-overlap square lifts every native unipotent element into the
original chosen Sylow, with its literal first endpoint value. -/
theorem marked_sylow_lift (r : MarkedTriality T M Mc H)
    (hTH : (T:Subgroup G)≤H) (u : Carrier (binaryParameters 1 Nat.zero_lt_one))
    (hu : u∈unipotent (binaryParameters 1 Nat.zero_lt_one)) :
    ∃ x : H, (x:G)∈(T:Subgroup G) ∧ (r.left x).val=u := by
  exact inclusion_amalgam_lift H (H ⊓ secondParabolic T M Mc H)
    (secondParabolic T M Mc H) inf_le_left inf_le_right
    _ _ _ (borel_le_parabolic _ .arms) (borel_le_parabolic _ .central)
    r (T:Subgroup G) u ((middle_sylow_map r hTH).ge hu)

omit [Finite G] in
/-- The mapped core center is the literal highest-root group. -/
theorem marked_core_center_mem (r : MarkedTriality T M Mc H)
    (x : H) (hx : (x:G)∈firstCoreCenter H) :
    (r.left x).val∈highestRoot (binaryParameters 1 Nat.zero_lt_one) := by
  obtain ⟨q,hq,hqx⟩ := hx
  have hc := (centerCongr (firstCoreEquiv r) ⟨q,hq⟩).property
  have hm := mem_map_of_mem (radical (binaryParameters 1 Nat.zero_lt_one) .arms).subtype hc
  rw [RadicalCoordinates.embedded_center_radical_arms _ rfl] at hm
  change (firstCoreEquiv r q).val ∈ highestRoot (binaryParameters 1 Nat.zero_lt_one) at hm
  rw [firstCoreEquiv_val] at hm
  convert hm using 1
  exact congrArg (fun y : H => (r.left y).val) (Subtype.ext hqx.symm)

/-- An element of the actual core fixed modulo its center by the chosen Sylow
has long-root image under the original first endpoint marking. -/
theorem marked_fixed_core_isLongRoot (r : MarkedTriality T M Mc H)
    (hTH : (T:Subgroup G)≤H) (q : H.pCoreIn 2) (hq1 : (q:G)≠1)
    (hfix : ∀ x∈(T:Subgroup G), ⁅x,(q:G)⁆∈firstCoreCenter H) :
    IsLongRootInvolution 1 Nat.zero_lt_one (firstCoreEquiv r q).val := by
  let P := binaryParameters 1 Nat.zero_lt_one
  have hp : P.prime=2 := rfl
  apply ArmsNormalization.fixed_mod_center_isLongRoot
  · intro hh
    have he : firstCoreEquiv r q=1 := Subtype.ext hh
    exact hq1 (congrArg Subtype.val ((firstCoreEquiv r).injective (he.trans (map_one _).symm)))
  · intro a
    have hu : short P hp 0 a∈unipotent P := by
      exact descendSubgroup_mono P
        (RadicalCoordinates.rootSubgroup_le_positiveSubgroup P hp .central)
        (short_mem P hp .central 0 trivial a)
    obtain ⟨x,hx,hxu⟩ := marked_sylow_lift r hTH _ hu
    let y : H := ⟨q,pCoreIn_le 2 H q.property⟩
    have hc := marked_core_center_mem r ⁅x,y⁆ (hfix x hx)
    have he : (r.left ⁅x,y⁆).val = ⁅(r.left x).val,(r.left y).val⁆ :=
      map_commutatorElement ((parabolic P .arms).subtype.comp r.left.toMonoidHom) x y
    rw [he,hxu,←firstCoreEquiv_val r q] at hc
    exact hc

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

/-- The source mutual-core reduction now lands in the actual model long-root
orbit. Both conjugations occur in the original ambient group. -/
theorem source_mutual_core_long_root (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hzR : z∈(H.pCoreIn 2).map (MulAut.conj a).toMonoidHom)
    (htQ : MulAut.conj a z∈H.pCoreIn 2) :
    ∃ b : Mc, ∃ q : H.pCoreIn 2,
      (q:G)=MulAut.conj (b:G) (MulAut.conj a z) ∧
      IsLongRootInvolution 1 Nat.zero_lt_one (firstCoreEquiv r q).val := by
  obtain ⟨b,hb⟩ := source_mutual_core_fusion_reduction
    hG hempty hM hu hmany hcard e hH r a ha hz hz1 hzR htQ
  have hnQ : Mc≤normalizer (H.pCoreIn 2 : Set G) :=
    (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r).trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hq : MulAut.conj (b:G) (MulAut.conj a z)∈H.pCoreIn 2 :=
    (mem_normalizer_iff.mp (hnQ b.property) _).mp htQ
  let q : H.pCoreIn 2 := ⟨_,hq⟩
  refine ⟨b,q,rfl,marked_fixed_core_isLongRoot r hH.1.1.2 q ?_ ?_⟩
  · intro h
    exact hz1 ((MulAut.conj a).injective ((MulAut.conj (b:G)).injective
      (h.trans (map_one _).symm) |>.trans (map_one _).symm))
  · intro x hx
    rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    exact hb x hx

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
