module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CompletionStructure
public import Theory.GroupTheory.ExtraspecialIntersection

/-!
# The extraspecial-core intersection step in original triality fusion

The original partner Mc is the normalizer of the central line of Q=O₂(H).
Thus a conjugate by a∉Mc has a different central line, and its intersection
with Q is elementary abelian of order at most 32. If z lies in the other
core and its centralizer there lies in T, the two exact core orders force
T=Q C_{Q^a}(z), with intersection order 32. Every element of Q in the other
central line is consequently fixed modulo Z(Q) by T.

This is the counting step of Aschbacher--Smith F.4.35, printed p.292, applied
to the original 14.2.18 setup. The conjugate-core placement and the exclusion
of short-root fusion still require the preceding source argument. Neither
ambient recognition nor the matching sixth-power relation is assumed proved.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
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

/-- Exact normalizer of the actual source central line, also in the cubic case. -/
theorem source_firstCore_center_normalizer (r : MarkedTriality T M Mc H) :
    normalizer (firstCoreCenter H : Set G)=Mc := by
  have hZ : Nat.card (firstCoreCenter H)=2 := by
    rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  rw [source_partner_centralizer hG hempty hM hu hmany hcard e hH r]
  exact le_antisymm (Subgroup.normalizer_le_centralizer_of_card_two _ hZ)
    (Subgroup.centralizer_le_normalizer _)

/-- No global normality is used: the two centers are compared as subgroups of G. -/
theorem source_conjugate_core_centers_disjoint (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) :
    Disjoint (firstCoreCenter H)
      ((center ((H.pCoreIn 2).map (MulAut.conj a).toMonoidHom)).map
        ((H.pCoreIn 2).map (MulAut.conj a).toMonoidHom).subtype) := by
  let Q := H.pCoreIn 2
  let R := Q.map (MulAut.conj a).toMonoidHom
  let : IsExtraspecial 2 Q := firstCore_extraspecial r
  let : IsExtraspecial 2 R := IsExtraspecial.of_mulEquiv
    (Q.equivMapOfInjective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective)
    (firstCore_extraspecial r)
  apply ExtraspecialIntersection.disjoint_centers_of_ne Q R
  intro he
  have hz : (firstCoreCenter H).map (MulAut.conj a).toMonoidHom=firstCoreCenter H := by
    exact (map_subgroup_center_eq _ (MulAut.conj a).injective Q).trans he.symm
  apply ha
  rw [←source_firstCore_center_normalizer hG hempty hM hu hmany hcard e hH r]
  exact mem_normalizer_iff_map_conj_eq.mpr hz

/-- The intersection of the literal distinct conjugate cores is elementary
abelian, with the triality bound of order 32. -/
theorem source_conjugate_core_intersection (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) :
    let Q := H.pCoreIn 2
    let R := Q.map (MulAut.conj a).toMonoidHom
    IsElementaryAbelian 2 (Q ⊓ R : Subgroup G) ∧ Nat.card (Q ⊓ R : Subgroup G)≤32 := by
  let Q := H.pCoreIn 2
  let R := Q.map (MulAut.conj a).toMonoidHom
  let : IsExtraspecial 2 Q := firstCore_extraspecial r
  let : IsExtraspecial 2 R := IsExtraspecial.of_mulEquiv
    (Q.equivMapOfInjective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective)
    (firstCore_extraspecial r)
  have hd := source_conjugate_core_centers_disjoint hG hempty hM hu hmany hcard e hH r a ha
  have hb := ExtraspecialIntersection.card_inf_sq_le Q R hd
  have hc : Nat.card Q=512 := firstCore_card r
  rw [hc] at hb
  exact ⟨ExtraspecialIntersection.elementary_inf Q R hd,by nlinarith⟩

/-- The exact source Sylow factorization in the mutual-core placement case.
The placement premises are the preceding fusion step, not an ambient recognition
or a desired factorization assumption. -/
theorem source_conjugate_core_sylow_factorization (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hzR : z∈(H.pCoreIn 2).map (MulAut.conj a).toMonoidHom)
    (hcT : (H.pCoreIn 2).map (MulAut.conj a).toMonoidHom ⊓
      centralizer ({z}:Set G) ≤ (T : Subgroup G)) :
    let Q := H.pCoreIn 2
    let C := Q.map (MulAut.conj a).toMonoidHom ⊓ centralizer ({z}:Set G)
    Nat.card C=256 ∧ Nat.card (Q ⊓ C : Subgroup G)=32 ∧ Q ⊔ C=(T : Subgroup G) := by
  let Q := H.pCoreIn 2
  let R := Q.map (MulAut.conj a).toMonoidHom
  let : IsExtraspecial 2 Q := firstCore_extraspecial r
  let : IsExtraspecial 2 R := IsExtraspecial.of_mulEquiv
    (Q.equivMapOfInjective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective)
    (firstCore_extraspecial r)
  have hQ : Nat.card Q=512 := firstCore_card r
  have hR : Nat.card R=512 := (card_map_of_injective (MulAut.conj a).injective).trans hQ
  have hd := source_conjugate_core_centers_disjoint hG hempty hM hu hmany hcard e hH r a ha
  have hzQ : z∈firstCoreCenter H :=
    (source_firstCore_center hG hempty hM hu hmany hcard e hH r).symm ▸ hz
  have hzout : z∉(center R).map R.subtype := fun h => hz1 (Subgroup.disjoint_def.mp hd hzQ h)
  have hQT : Q≤(T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hH.1.1.2)
    change Q ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hn : (T : Subgroup G)≤normalizer (Q:Set G) :=
    hH.1.1.2.trans (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  exact ExtraspecialIntersection.sylow_supplement Q R (T : Subgroup G)
    hQ hR (source_sylow_card r hH.1.1.2) hd hQT hn z hzR hzout hcT

/-- The conjugate central involution is fixed modulo the original core center
once the source mutual-core placement has been made. -/
theorem source_conjugate_core_fixed_mod_center (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hzR : z∈(H.pCoreIn 2).map (MulAut.conj a).toMonoidHom)
    (hcT : (H.pCoreIn 2).map (MulAut.conj a).toMonoidHom ⊓
      centralizer ({z}:Set G) ≤ (T : Subgroup G))
    (htQ : MulAut.conj a z∈H.pCoreIn 2) :
    ∀ x∈(T : Subgroup G), ⁅x,MulAut.conj a z⁆∈centralInvolutions T := by
  let Q := H.pCoreIn 2
  let R := Q.map (MulAut.conj a).toMonoidHom
  let C := R ⊓ centralizer ({z}:Set G)
  let : IsExtraspecial 2 Q := firstCore_extraspecial r
  have hgen := (source_conjugate_core_sylow_factorization
    hG hempty hM hu hmany hcard e hH r a ha hz hz1 hzR hcT).2.2
  have hn : C≤normalizer (Q:Set G) := hcT.trans (hH.1.1.2.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  have hzQ : z∈firstCoreCenter H :=
    (source_firstCore_center hG hempty hM hu hmany hcard e hH r).symm ▸ hz
  have htZ : MulAut.conj a z∈(center R).map R.subtype :=
    map_subgroup_center_le (MulAut.conj a).toMonoidHom Q (mem_map_of_mem _ hzQ)
  have htC : MulAut.conj a z∈centralizer (C:Set G) := by
    obtain ⟨t,ht,he⟩ := htZ
    rw [←he]
    intro c hc
    exact (congrArg Subtype.val (mem_center_iff.mp ht ⟨c,hc.1⟩))
  intro x hx
  rw [←source_firstCore_center hG hempty hM hu hmany hcard e hH r]
  exact ExtraspecialIntersection.commutator_mem_center_of_supplement Q C (T : Subgroup G)
    hn hgen htQ htC hx

/-- Sylow conjugacy inside the original Mc removes the centralizer-placement
premise: a mutually incident pair of core centers has an Mc-conjugate fixed
modulo the original central line. -/
theorem source_mutual_core_fusion_reduction (r : MarkedTriality T M Mc H)
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hzR : z∈(H.pCoreIn 2).map (MulAut.conj a).toMonoidHom)
    (htQ : MulAut.conj a z∈H.pCoreIn 2) :
    ∃ b : Mc, ∀ x∈(T : Subgroup G),
      ⁅x,MulAut.conj (b:G) (MulAut.conj a z)⁆∈centralInvolutions T := by
  let Q := H.pCoreIn 2
  let R := Q.map (MulAut.conj a).toMonoidHom
  let C := R ⊓ centralizer ({z}:Set G)
  have hMc : Mc=centralizer ({z}:Set G) :=
    source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r hz hz1
  have hCMc : C≤Mc := hMc.symm ▸ inf_le_right
  have hTMc : (T:Subgroup G)≤Mc :=
    hH.1.1.2.trans (source_first_le_partner hG hempty hM hu hmany hcard e hH)
  have hp : IsPGroup 2 (C.subgroupOf Mc) :=
    (((isPGroup_pCoreIn 2 H).map (MulAut.conj a).toMonoidHom).to_le
      (show C≤R from inf_le_left)).comap_subtype (K := Mc)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq Mc P (T.subtype hTMc)
  have hbmap : (C.subgroupOf Mc).map (MulAut.conj b).toMonoidHom ≤
      (T:Subgroup G).subgroupOf Mc := by
    have hh := map_mono (f := (MulAut.conj b).toMonoidHom) hP
    have he := congrArg Sylow.toSubgroup hb
    change (P:Subgroup Mc).map (MulAut.conj b).toMonoidHom =
      (T:Subgroup G).subgroupOf Mc at he
    exact hh.trans_eq he
  let f := MulAut.conj (b:G)
  have hCmap : C.map f.toMonoidHom ≤ (T:Subgroup G) := by
    rintro x ⟨c,hc,rfl⟩
    exact hbmap (mem_map_of_mem (MulAut.conj b).toMonoidHom
      (show (⟨c,hCMc hc⟩:Mc)∈C.subgroupOf Mc from hc))
  have hbz : f z=z := by
    change (b:G)*z*(b:G)⁻¹=z
    have hbC : (b:G)∈centralizer ({z}:Set G) := hMc ▸ b.property
    have he : (b:G)*z=z*(b:G) := mem_centralizer_singleton_iff.mp hbC
    rw [he,mul_inv_cancel_right]
  have hcomp (y:G) : MulAut.conj ((b:G)*a) y=f (MulAut.conj a y) := by
    change ((b:G)*a)*y*((b:G)*a)⁻¹=(b:G)*(a*y*a⁻¹)*(b:G)⁻¹
    group
  have hRmap : Q.map (MulAut.conj ((b:G)*a)).toMonoidHom=R.map f.toMonoidHom := by
    rw [map_map]
    congr 1
    exact MonoidHom.ext hcomp
  have hCZ : (centralizer ({z}:Set G)).map f.toMonoidHom=centralizer ({z}:Set G) := by
    rw [Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton,hbz]
  have hcT : Q.map (MulAut.conj ((b:G)*a)).toMonoidHom ⊓ centralizer ({z}:Set G)≤
      (T:Subgroup G) := by
    rw [hRmap,←hCZ,←map_inf _ _ _ f.injective]
    exact hCmap
  have hzR' : z∈Q.map (MulAut.conj ((b:G)*a)).toMonoidHom := by
    rw [hRmap,←hbz]
    exact mem_map_of_mem _ hzR
  have hnQ : Mc≤normalizer (Q:Set G) :=
    (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r).trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have htQ' : MulAut.conj ((b:G)*a) z∈Q := by
    rw [hcomp]
    exact (mem_normalizer_iff.mp (hnQ b.property) (MulAut.conj a z)).mp htQ
  have hout : (b:G)*a∉Mc := fun hh => ha ((Mc.mul_mem_cancel_left b.property).mp hh)
  refine ⟨b,?_⟩
  intro x hx
  rw [←hcomp]
  exact source_conjugate_core_fixed_mod_center hG hempty hM hu hmany hcard e hH r
    ((b:G)*a) hout hz hz1 hzR' hcT htQ' x hx

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
