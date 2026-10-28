module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionWitness
public import Theory.SpecificGroups.Triality.ArmsOrbit

/-!
# Excluding short-root fusion in the original triality setup

Transport ambient conjugation by Mc through the first endpoint and its
characteristic two-core. The two induced automorphisms intertwine the actual
core action. The intrinsic quotient-orbit bounds therefore prevent an
Mc-conjugate of the marked short root from being Sylow-fixed modulo the
center. The preceding pair and mutual-core arguments force precisely that
fixedness if the original central involution is fused to this short root.
This closes the short-root obstruction, including the cubic Mc extension.

The earlier marked realization remains explicit. The matching sixth-power
relation, ambient recognition and Borel exclusion stay with
qt-e-14315-eight-borel-exclusion. Source: Aschbacher--Smith F.4.35, p.292;
14.2.18--19, p.987.
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
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "Qm" => radical P Node.arms
local notation "Lm" => parabolic P Node.arms
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

omit [Finite G] in
/-- Transporting a normalizing ambient conjugation through the whole marking
intertwines the actual first-parabolic action on its core quotient. -/
theorem marked_core_automorphism_compatible (r : MarkedTriality T M Mc H)
    (b : G) (hb : b∈normalizer (H:Set G)) :
    let f := firstCoreEquiv r
    let nQ := normalizer_le_normalizer_characteristic_image H (pCore 2 H) hb
    let a := MulAut.congr r.left (H.normalizerMonoidHom ⟨b,hb⟩)
    let c := MulAut.congr f ((H.pCoreIn 2).normalizerMonoidHom ⟨b,nQ⟩)
    ∀ h : Lm, ∀ q : Qm, c (ArmsOrbit.coreAction h q)=ArmsOrbit.coreAction (a h) (c q) := by
  dsimp only
  let f := firstCoreEquiv r
  let nQ := normalizer_le_normalizer_characteristic_image H (pCore 2 H) hb
  let a := MulAut.congr r.left (H.normalizerMonoidHom ⟨b,hb⟩)
  let c := MulAut.congr f ((H.pCoreIn 2).normalizerMonoidHom ⟨b,nQ⟩)
  let j : Lm →* G := H.subtype.comp r.left.symm.toMonoidHom
  let k : Qm →* G := (H.pCoreIn 2).subtype.comp f.symm.toMonoidHom
  have hk : Function.Injective k := (H.pCoreIn 2).subtype_injective.comp f.symm.injective
  have hkj : k=j.comp (inclusion (radical_le_parabolic P .arms)) := by
    ext q
    have he := firstCoreEquiv_val r (f.symm q)
    change (f (f.symm q)).val = (r.left ⟨(f.symm q:G),pCoreIn_le 2 H (f.symm q).property⟩).val at he
    rw [f.apply_symm_apply] at he
    have hh : (⟨(f.symm q:G),pCoreIn_le 2 H (f.symm q).property⟩:H)=
        r.left.symm ⟨q,radical_le_parabolic P .arms q.property⟩ := by
      apply r.left.injective
      rw [r.left.apply_symm_apply]
      exact Subtype.ext he.symm
    exact congrArg Subtype.val hh
  have hcore (h : Lm) (q : Qm) :
      k (ArmsOrbit.coreAction h q)=j h*k q*(j h)⁻¹ := by
    rw [hkj]
    change j (h*inclusion (radical_le_parabolic P .arms) q*h⁻¹)=_
    simp only [map_mul,map_inv,MonoidHom.comp_apply]
  have ha (h : Lm) : j (a h)=b*j h*b⁻¹ := by
    change (r.left.symm (r.left (H.normalizerMonoidHom ⟨b,hb⟩ (r.left.symm h))):G)=_
    rw [r.left.symm_apply_apply]
    rfl
  have hc (q : Qm) : k (c q)=b*k q*b⁻¹ := by
    change (f.symm (f ((H.pCoreIn 2).normalizerMonoidHom ⟨b,nQ⟩ (f.symm q))):G)=_
    rw [f.symm_apply_apply]
    rfl
  intro h q
  apply hk
  change k (c (ArmsOrbit.coreAction h q))=k (ArmsOrbit.coreAction (a h) (c q))
  rw [hc,hcore,hcore,ha,hc]
  group

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

/-- A marked short-root element cannot have an Mc-conjugate fixed modulo
its core center. The same argument includes the original cubic extension. -/
theorem source_short_not_fixed (r : MarkedTriality T M Mc H)
    (q : H.pCoreIn 2) (d : ExtensionField P) (hd : d≠0)
    (hshort : (firstCoreEquiv r q).val=short P ArmsOrbit.prime_two 2 d)
    (b : Mc) :
    ¬ (∀ x∈(T:Subgroup G), ⁅x,MulAut.conj (b:G) q⁆∈centralInvolutions T) := by
  intro hfix
  let f := firstCoreEquiv r
  have hb := source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r b.property
  have hn := normalizer_le_normalizer_characteristic_image H (pCore 2 H) hb
  let a := MulAut.congr r.left (H.normalizerMonoidHom ⟨b,hb⟩)
  let c := MulAut.congr f ((H.pCoreIn 2).normalizerMonoidHom ⟨b,hn⟩)
  let cq := (H.pCoreIn 2).normalizerMonoidHom ⟨b,hn⟩ q
  have hcq : c (f q)=f cq := by
    change f ((H.pCoreIn 2).normalizerMonoidHom ⟨b,hn⟩ (f.symm (f q)))=f cq
    rw [f.symm_apply_apply]
  have hq : f q=⟨short P ArmsOrbit.prime_two 2 d,ArmsOrbit.short_two_mem d⟩ := Subtype.ext hshort
  apply ArmsOrbit.short_not_fixed_of_core_compatible d hd a c
    (marked_core_automorphism_compatible r b hb)
  intro h hh
  rw [←hq,hcq]
  obtain ⟨x,hx,hxe⟩ := marked_sylow_lift r hH.1.1.2 h.val hh
  have hxr : r.left x=h := Subtype.ext hxe
  have hmem : ⁅(r.left x).val,(f cq).val⁆∈highestRoot P := by
    let y : H := ⟨cq,pCoreIn_le 2 H cq.property⟩
    have hz := hfix x hx
    rw [←source_firstCore_center hG hempty hM hu hmany hcard e hH r] at hz
    have hm := marked_core_center_mem r ⁅x,y⁆ hz
    have he : (r.left ⁅x,y⁆).val=⁅(r.left x).val,(r.left y).val⁆ :=
      map_commutatorElement ((parabolic P .arms).subtype.comp r.left.toMonoidHom) x y
    rw [he,←firstCoreEquiv_val r cq] at hm
    exact hm
  rw [hxr] at hmem
  exact (ArmsOrbit.action_point_fixed_iff h (f cq)).mpr hmem

/-- The original central involution is not fused to the marked highest short
root. Mutual-core incidence and the orbit obstruction are both discharged. -/
theorem source_higher_short_not_fused (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (htQ : MulAut.conj a z∈H.pCoreIn 2)
    (d : ExtensionField P)
    (hshort : (firstCoreEquiv r ⟨MulAut.conj a z,htQ⟩).val=short P ArmsOrbit.prime_two 2 d) : False := by
  let q : H.pCoreIn 2 := ⟨MulAut.conj a z,htQ⟩
  have hd : d≠0 := by
    intro hd
    have he : firstCoreEquiv r q=1 := Subtype.ext (hshort.trans (hd ▸ short_zero P ArmsOrbit.prime_two 2))
    have hq : q=1 := (firstCoreEquiv r).injective (he.trans (map_one _).symm)
    have hz' : MulAut.conj a z=1 := congrArg Subtype.val hq
    exact hz1 ((MulAut.conj a).injective (hz'.trans (map_one _).symm))
  have hzC : z∈firstCoreCenter H :=
    (source_firstCore_center hG hempty hM hu hmany hcard e hH r).symm ▸ hz
  obtain ⟨zQ,hzQ,hzval⟩ := hzC
  obtain ⟨x,y,hx,hy,hxy⟩ := marked_higher_short_pair r zQ q hzQ d hshort
  obtain ⟨a',ha',ht',hz'⟩ := source_pair_mutual_core hG hempty hM hu hmany hcard e hH r
    a ha hz hz1 x.property y.property hx hy (hxy.trans hzval)
  have htQ' : MulAut.conj a' z∈H.pCoreIn 2 := ht'.symm ▸ htQ
  obtain ⟨b,hb⟩ := source_mutual_core_fusion_reduction hG hempty hM hu hmany hcard e hH r
    a' ha' hz hz1 hz' htQ'
  apply source_short_not_fixed hG hempty hM hu hmany hcard e hH r q d hd hshort b
  simpa only [ht'] using hb
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
