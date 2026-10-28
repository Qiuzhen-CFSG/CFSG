module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionFixed
public import Theory.SpecificGroups.Triality.ArmsFusionPair

/-!
# The original short-root pair gives mutual-core incidence

The literal quotient H/O₂(H) has elementary Sylow two-subgroups. A pair
in Q centralizing z^a and having commutator z can therefore be conjugated
inside C_G(z^a) so that z belongs to the conjugate core while z^a remains
unchanged. The extraspecial intersection theorem and the Sylow fixed-space
calculation then give an Mc-conjugate marked as a long-root involution.

For the chosen highest short-root representative the actual root coordinate
formula constructs this pair in Q, with the original endpoint marking.
No pair or mutual-incidence premise remains in that specialized application.
The independent marked realization is still explicit; exclusion of the
short/long Mc-orbit intersection, the matching sixth-power relation and
ambient recognition remain with qt-e-14315-eight-borel-exclusion.
Source: Aschbacher--Smith F.4.35, p.292; 14.2.18--19, p.987.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

/-- The actual Sylow commutator lies in the original first core, because its
image in the literal PSL₂(8) quotient is elementary abelian. -/
theorem marked_sylow_commutator_mem (r : MarkedTriality T M Mc H)
    (hTH : (T:Subgroup G)≤H) {x y : G} (hx : x∈(T:Subgroup G)) (hy : y∈(T:Subgroup G)) :
    ⁅x,y⁆∈H.pCoreIn 2 := by
  let π := QuotientGroup.mk' (pCore 2 H)
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let := (first_quotient_sylow r S).1
  let xH : H := ⟨x,hTH hx⟩
  let yH : H := ⟨y,hTH hy⟩
  have hxS : π xH∈(S:Subgroup (H ⧸ pCore 2 H)) := mem_map_of_mem π hx
  have hyS : π yH∈(S:Subgroup (H ⧸ pCore 2 H)) := mem_map_of_mem π hy
  have hc := congrArg Subtype.val (mul_comm (⟨π xH,hxS⟩:S) ⟨π yH,hyS⟩)
  refine ⟨⁅xH,yH⁆,?_,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change π ⁅xH,yH⁆=1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hc

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

/-- A pair in the first core centralizing the fused involution and having
commutator z supplies the mutual-core incidence in F.4.35. Sylow conjugacy
changes the conjugating element while preserving its value on z. -/
theorem source_pair_mutual_core (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    {x y : G} (hx : x∈H.pCoreIn 2) (hy : y∈H.pCoreIn 2)
    (hxt : Commute x (MulAut.conj a z)) (hyt : Commute y (MulAut.conj a z))
    (hxy : ⁅x,y⁆=z) :
    ∃ a' : G, a'∉Mc ∧ MulAut.conj a' z=MulAut.conj a z ∧
      z∈(H.pCoreIn 2).map (MulAut.conj a').toMonoidHom := by
  let Q := H.pCoreIn 2
  let t := MulAut.conj a z
  let D := Q ⊓ centralizer ({t}:Set G)
  let f := MulAut.conj a⁻¹
  have ht : f t=z := by change a⁻¹*(a*z*a⁻¹)*(a⁻¹)⁻¹=z; group
  have hMc := source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r hz hz1
  have hD : D.map f.toMonoidHom≤Mc := by
    rintro d ⟨v,hv,rfl⟩
    rw [hMc,mem_centralizer_singleton_iff]
    have hc := congrArg f (mem_centralizer_singleton_iff.mp hv.2)
    change f v*z=z*f v
    simpa only [map_mul,ht] using hc
  have hTMc : (T:Subgroup G)≤Mc :=
    hH.1.1.2.trans (source_first_le_partner hG hempty hM hu hmany hcard e hH)
  have hp : IsPGroup 2 ((D.map f.toMonoidHom).subgroupOf Mc) :=
    (((isPGroup_pCoreIn 2 H).to_le (show D≤Q from inf_le_left)).map f.toMonoidHom).comap_subtype
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq Mc S (T.subtype hTMc)
  have hbmap : ((D.map f.toMonoidHom).subgroupOf Mc).map (MulAut.conj b).toMonoidHom ≤
      (T:Subgroup G).subgroupOf Mc := by
    have hh := map_mono (f := (MulAut.conj b).toMonoidHom) hS
    have he := congrArg Sylow.toSubgroup hb
    change (S:Subgroup Mc).map (MulAut.conj b).toMonoidHom=(T:Subgroup G).subgroupOf Mc at he
    exact hh.trans_eq he
  let k := MulAut.conj ((b:G)*a⁻¹)
  have hk (d : G) (hd : d∈D) : k d∈(T:Subgroup G) := by
    have hf : f d∈D.map f.toMonoidHom := mem_map_of_mem _ hd
    have hh := hbmap (mem_map_of_mem (MulAut.conj b).toMonoidHom
      (show (⟨f d,hD hf⟩:Mc)∈(D.map f.toMonoidHom).subgroupOf Mc from hf))
    change (b:G)*(a⁻¹*d*(a⁻¹)⁻¹)*(b:G)⁻¹∈(T:Subgroup G) at hh
    convert hh using 1
    dsimp [k,MulAut.conj]
    group
  have hzQ : k z∈Q := by
    rw [←hxy,map_commutatorElement]
    exact marked_sylow_commutator_mem r hH.1.1.2
      (hk x ⟨hx,mem_centralizer_singleton_iff.mpr hxt.eq⟩)
      (hk y ⟨hy,mem_centralizer_singleton_iff.mpr hyt.eq⟩)
  have hbinvz : (b:G)⁻¹*z*b=z := by
    have hbC : (b:G)⁻¹∈centralizer ({z}:Set G) := by
      rw [←hMc]
      exact Mc.inv_mem b.property
    have hh := mem_centralizer_singleton_iff.mp hbC
    rw [hh,mul_assoc,inv_mul_cancel,mul_one]
  refine ⟨a*(b:G)⁻¹,?_,?_,?_⟩
  · intro hh
    exact ha ((Mc.mul_mem_cancel_right (Mc.inv_mem b.property)).mp hh)
  · change (a*(b:G)⁻¹)*z*(a*(b:G)⁻¹)⁻¹=a*z*a⁻¹
    calc
      _ = a*((b:G)⁻¹*z*b)*a⁻¹ := by group
      _ = _ := by rw [hbinvz]
  · refine ⟨k z,hzQ,?_⟩
    change (a*(b:G)⁻¹)*(((b:G)*a⁻¹)*z*((b:G)*a⁻¹)⁻¹)*(a*(b:G)⁻¹)⁻¹=z
    group

/-- The local pair is sufficient for the whole original fixed-space reduction;
the two mutual-core incidence premises are discharged here. -/
theorem source_pair_long_root (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (htQ : MulAut.conj a z∈H.pCoreIn 2)
    {x y : G} (hx : x∈H.pCoreIn 2) (hy : y∈H.pCoreIn 2)
    (hxt : Commute x (MulAut.conj a z)) (hyt : Commute y (MulAut.conj a z))
    (hxy : ⁅x,y⁆=z) :
    ∃ b : Mc, ∃ q : H.pCoreIn 2,
      (q:G)=MulAut.conj (b:G) (MulAut.conj a z) ∧
      _root_.Triality.Standard.EvenInvolutionGeometry.IsLongRootInvolution
        1 Nat.zero_lt_one (firstCoreEquiv r q).val := by
  obtain ⟨a',ha',ht',hz'⟩ := source_pair_mutual_core
    hG hempty hM hu hmany hcard e hH r a ha hz hz1 hx hy hxt hyt hxy
  simpa only [ht'] using source_mutual_core_long_root
    hG hempty hM hu hmany hcard e hH r a' ha' hz hz1 hz' (ht'.symm ▸ htQ)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic


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
/-- The source's noncommuting centralizing pair is realized in the original
core for the marked highest short root. No pair or mutual-incidence premise
is added to this local application. -/
theorem marked_higher_short_pair (r : MarkedTriality T M Mc H)
    (z q : H.pCoreIn 2) (hz : z∈center (H.pCoreIn 2))
    (d : ExtensionField (binaryParameters 1 Nat.zero_lt_one))
    (hq : (firstCoreEquiv r q).val=short (binaryParameters 1 Nat.zero_lt_one) rfl 2 d) :
    ∃ x y : H.pCoreIn 2, Commute (x:G) (q:G) ∧ Commute (y:G) (q:G) ∧
      ⁅(x:G),(y:G)⁆=(z:G) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  have hp : P.prime=2 := rfl
  let f := firstCoreEquiv r
  have hz' : (f z).val∈highestRoot P := by
    have hh := mem_map_of_mem (radical P .arms).subtype (centerCongr f ⟨z,hz⟩).property
    rw [RadicalCoordinates.embedded_center_radical_arms P hp] at hh
    exact hh
  rw [←highestHom_range P hp] at hz'
  obtain ⟨t,ht⟩ := hz'
  obtain ⟨hxl,hyl,hxt,hyt,hxy⟩ := ArmsNormalization.higher_short_root_pair P hp d t.toAdd
  let x := f.symm ⟨long P hp 0 t.toAdd,hxl⟩
  let y := f.symm ⟨long P hp 1 1,hyl⟩
  have hx : (f x).val=long P hp 0 t.toAdd := congrArg Subtype.val (f.apply_symm_apply _)
  have hy : (f y).val=long P hp 1 1 := congrArg Subtype.val (f.apply_symm_apply _)
  have hcx : Commute (f x) (f q) := by
    apply Subtype.ext
    change (f x).val*(f q).val=(f q).val*(f x).val
    rw [hx,hq]
    exact hxt.eq
  have hcy : Commute (f y) (f q) := by
    apply Subtype.ext
    change (f y).val*(f q).val=(f q).val*(f y).val
    rw [hy,hq]
    exact hyt.eq
  have hc : ⁅x,y⁆=z := by
    apply f.injective
    rw [map_commutatorElement]
    apply Subtype.ext
    change ⁅(f x).val,(f y).val⁆=(f z).val
    rw [hx,hy,hxy]
    exact ht
  exact ⟨x,y,(Commute.of_map f.injective hcx).map (H.pCoreIn 2).subtype,
    (Commute.of_map f.injective hcy).map (H.pCoreIn 2).subtype,congrArg Subtype.val hc⟩

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

/-- For the actual marked short-root representative, the original centralizer
hypotheses force an Mc-conjugate into the model long-root class. The remaining
source nonfusion step must exclude this Mc-orbit intersection. -/
theorem source_higher_short_fusion_reduction (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (htQ : MulAut.conj a z∈H.pCoreIn 2)
    (d : ExtensionField (binaryParameters 1 Nat.zero_lt_one))
    (hshort : (firstCoreEquiv r ⟨MulAut.conj a z,htQ⟩).val=
      short (binaryParameters 1 Nat.zero_lt_one) rfl 2 d) :
    ∃ b : Mc, ∃ q : H.pCoreIn 2,
      (q:G)=MulAut.conj (b:G) (MulAut.conj a z) ∧
      IsLongRootInvolution 1 Nat.zero_lt_one (firstCoreEquiv r q).val := by
  have hzC : z∈firstCoreCenter H :=
    (source_firstCore_center hG hempty hM hu hmany hcard e hH r).symm ▸ hz
  obtain ⟨zQ,hzQ,hzval⟩ := hzC
  obtain ⟨x,y,hx,hy,hxy⟩ := marked_higher_short_pair r zQ ⟨_,htQ⟩ hzQ d hshort
  exact source_pair_long_root hG hempty hM hu hmany hcard e hH r a ha hz hz1 htQ
    x.property y.property hx hy (hxy.trans hzval)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
