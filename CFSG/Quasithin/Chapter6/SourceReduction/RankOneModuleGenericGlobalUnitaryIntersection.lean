module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryMaximal
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Core intersections in the nonnormal unitary branch

Put K = O²(H), Q = O₂(K) and R = O₂(J), for an actual local overcomponent
J of K. The full ambient Sylow gives R ≤ O₂(H) ≤ S. Thus R normalizes K,
K normalizes R, and K ∩ R ≤ Q. If this intersection centralized K, the
three-subgroup lemma and perfectness would make R centralize K; characteristic
two in J would then put the nontrivial perfect K in the two-group R.

In the actual unitary point core every noncentral element has every central
element as a commutator. The proof uses the Hermitian Heisenberg coordinates
and surjectivity of the trace onto the fixed field, then transports along the
proved original-factor isomorphism. Since K centralizes Z(Q), the noncentral
intersection therefore satisfies [K ∩ R,Q] = Z(Q), placing Z(Q) in R.
The existing core-index bound, through O₂(H) ≤ O₂(KS), gives |R : K ∩ R| ≤ 2.

For the literal inclusion K → J/O₂(J), the kernel is R ∩ K. It lies in Q
and contains Φ(Q) = Z(Q). Hence its image has elementary two-core, and
removing that core preserves the original PSL₂(2^m) quotient. All these
statements include both unitary orientations and the degree-two extension;
no equality O₂(H) = Q or normality of Q in J is assumed.

The companion applies these calculations to the remaining Chapter12
nonnormal-core alternative. The natural-constituent calculation, embedding
selection and second-parabolic contradiction remain to be proved, as do the
outstanding maximality rows, exhaustive comparison and ambient recognition.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPointLocal
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryIntersection
variable (F : Type*) [Field F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "Q" => radical F σ hσ
local notation "κ" => coordinatesOfRadical F σ hσ

private theorem coord_ext (a b : Q) (hx : (κ a).x = (κ b).x)
    (hy : (κ a).y = (κ b).y) (hz : (κ a).z = (κ b).z) : a = b := by
  apply (radicalCoordinatesEquiv F σ hσ).symm.injective
  change κ a = κ b
  cases hca : κ a
  cases hcb : κ b
  simp_all

private theorem coord_mul (a b : Q) :
    (κ (a*b)).x = (κ a).x + (κ b).x ∧
    (κ (a*b)).y = (κ a).y + (κ b).y ∧
    (κ (a*b)).z = (κ a).z + (κ b).z + σ (κ a).y * (κ b).x +
      σ (κ a).x * (κ b).y := by
  obtain ⟨c, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective a
  obtain ⟨d, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective b
  exact radical_mul_coordinates F σ hσ c d

include hσ in
private theorem pair_surjective (hnt : ∃ u, σ u ≠ u) {x : F} (hx : x ≠ 0)
    (t : FixedBy.subfield F σ) : ∃ y : F, σ x*y + σ y*x = t := by
  obtain ⟨b,hb⟩ := exists_trace_eq F σ hσ hnt t
  refine ⟨b / σ x,?_⟩
  rw [map_div₀,hσ]
  have hsx : σ x ≠ 0 := by simpa using hx
  calc
    σ x * (b / σ x) + σ b / x * x = b + σ b := by field_simp [hx, hsx]
    _ = t := hb

/-- Nondegeneracy in the actual Heisenberg group: each noncentral element
has every central element as one of its commutators. -/
private theorem commutator_surjective (hnt : ∃ u, σ u ≠ u)
    (a : Q) (ha : a ∉ center Q) (z : center Q) : ∃ b : Q, ⁅a,b⁆ = z.val := by
  let t := (centerEquivFixedField F σ hσ hnt z).toAdd
  have hz : centralElement F σ hσ t = z.val :=
    congrArg Subtype.val ((centerEquivFixedField F σ hσ hnt).left_inv z)
  have hc (b : Q) (hxy : σ (κ a).y * (κ b).x + σ (κ a).x * (κ b).y =
      (t : F) + σ (κ b).y * (κ a).x + σ (κ b).x * (κ a).y) : ⁅a,b⁆ = z.val := by
    have hab : a*b = centralElement F σ hσ t * (b*a) := by
      apply coord_ext F σ hσ
      · simp only [(coord_mul F σ hσ _ _).1]
        change (κ a).x + (κ b).x = 0 + ((κ b).x + (κ a).x)
        simp [add_comm]
      · simp only [(coord_mul F σ hσ _ _).2.1]
        change (κ a).y + (κ b).y = 0 + ((κ b).y + (κ a).y)
        simp [add_comm]
      · simp only [(coord_mul F σ hσ _ _).2.2,
          (coord_mul F σ hσ _ _).1,(coord_mul F σ hσ _ _).2.1]
        change (κ a).z + (κ b).z + σ (κ a).y * (κ b).x + σ (κ a).x * (κ b).y =
          (t : F) + ((κ b).z + (κ a).z + σ (κ b).y * (κ a).x + σ (κ b).x * (κ a).y) +
            σ 0 * ((κ b).x + (κ a).x) + σ 0 * ((κ b).y + (κ a).y)
        rw [map_zero]
        linear_combination hxy
    rw [commutatorElement_def,hab]
    simpa [mul_assoc] using hz
  by_cases hx : (κ a).x = 0
  · have hy : (κ a).y ≠ 0 := fun hy => ha ((mem_center_radical_iff F σ hσ hnt a).mpr ⟨hx,hy⟩)
    obtain ⟨b,hb⟩ := pair_surjective F σ hσ hnt hy t
    refine ⟨radicalOfCoordinates F σ hσ ⟨b,0,0,by simp⟩,hc _ ?_⟩
    change σ (κ a).y * b + σ (κ a).x * 0 = t + σ 0 * (κ a).x + σ b * (κ a).y
    simp only [mul_zero,map_zero,zero_mul,add_zero]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hb
  · obtain ⟨b,hb⟩ := pair_surjective F σ hσ hnt hx t
    refine ⟨radicalOfCoordinates F σ hσ ⟨0,b,0,by simp⟩,hc _ ?_⟩
    change σ (κ a).y * 0 + σ (κ a).x * b = t + σ b * (κ a).x + σ 0 * (κ a).y
    simp only [mul_zero,map_zero,zero_mul,zero_add,add_zero]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryIntersection

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem overcomponent_intersection_noncentral
    {T : Sylow 2 G} {L H K J : Subgroup G}
    (hE : IsEvenCharacteristicAt T)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hK : K = residual H)
    (hp : Group.IsPerfect K) (hKne : K ≠ ⊥)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J) :
    J.pCoreIn 2 ≤ H.pCoreIn 2 ∧ J.pCoreIn 2 ≤ sourceS L H ∧
      K ⊓ J.pCoreIn 2 ≤ K.pCoreIn 2 ∧
      ¬ K ⊓ J.pCoreIn 2 ≤ centralizer (K : Set G) := by
  subst K
  let K := residual H
  let R := J.pCoreIn 2
  have hHJ : H ≤ J ⊔ (T : Subgroup G) := by
    rw [←residual_sup_sylow T H hTH]
    exact sup_le_sup hKJ le_rfl
  have hRH : R ≤ H.pCoreIn 2 :=
    (pCoreAmbient_mono_of_isSubnormalIn J (J ⊔ (T : Subgroup G)) 2
      le_sup_left hJ.1.subnormal).trans
        (Chapter3.twoCore_le_of_sylow_le T hTH hHJ)
  have hRS : R ≤ sourceS L H := hRH.trans
    (Chapter3.twoCore_le_of_sylow_le T (le_inf hTL hTH) inf_le_right)
  have hNQ : K ⊓ R ≤ K.pCoreIn 2 :=
    (inf_le_inf_left K hRH).trans (inf_pCoreIn_le_of_le 2 (map_subtype_le _))
  refine ⟨hRH,hRS,hNQ,?_⟩
  intro hc
  let := hp
  have hRK : R ≤ normalizer (K : Set G) :=
    (hRS.trans (sourceS_le_sylow hTL hTH)).trans (hTH.trans (le_normalizer_residual H))
  have hKR : K ≤ normalizer (R : Set G) := hKJ.trans (J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hcomm : ⁅R,K⁆ ≤ K ⊓ R := le_inf
    (le_normalizer_iff_commutator_le_right.mp hRK)
    (by rw [commutator_comm]; exact le_normalizer_iff_commutator_le_right.mp hKR)
  have hz : ⁅R,K⁆ = ⊥ := commutator_eq_bot_of_iterated_eq_bot R K
    (commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hc))
  have hchar := Chapter1.mem_He_iff.mpr
    (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T hE hJ)
  have hKR' : K ≤ R := fun x hx => hchar
    ⟨hKJ hx,le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz) hx⟩
  let : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hKne
  exact Group.IsPerfect.not_isNilpotent K ((isPGroup_pCoreIn 2 J).to_le hKR').isNilpotent

open ChapterF.GreenBook.LieModels.UnitaryFour
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

private theorem core_commutator_surjective
    (x : (residual H).pCoreIn 2) (hx : x ∉ center ((residual H).pCoreIn 2))
    (z : center ((residual H).pCoreIn 2)) :
    ∃ y : (residual H).pCoreIn 2, ⁅x,y⁆ = z.val := by
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  obtain ⟨b⟩ := hf.2.2.2.1
  let a := ((pCore 2 (residual H)).equivMapOfInjective (residual H).subtype
    (residual H).subtype_injective).symm
  let c := (b.subgroupMap (pCore 2 (residual H))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 b))
  let e : (residual H).pCoreIn 2 ≃* PointLocal.Radical m hm :=
    a.trans (c.trans (PointLocal.radicalEquivProjectiveTwoCore m hm).symm)
  have hxe : e x ∉ center (PointLocal.Radical m hm) := by
    intro hx'
    have hh := (centerCongr e.symm ⟨e x,hx'⟩).property
    change e.symm (e x) ∈ center ((residual H).pCoreIn 2) at hh
    exact hx (by simpa only [e.symm_apply_apply] using hh)
  have hex : ∃ y : PointLocal.Radical m hm, ⁅e x,y⁆ = e z.val :=
    UnitaryIntersection.commutator_surjective
      (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
      (PointLocal.fieldConj_nontrivial m hm) (e x) hxe (centerCongr e z)
  obtain ⟨y,hy⟩ := hex
  refine ⟨e.symm y,e.injective ?_⟩
  change e.toMonoidHom ⁅x,e.symm y⁆ = e z.val
  rw [map_commutatorElement]
  change ⁅e x,e (e.symm y)⁆ = e z.val
  rw [e.apply_symm_apply]
  exact hy

/-- In every actual unitary overcomponent, the intersection with its two-core
is noncentral and its commutator with the original right core is the entire
original core center. The enlarged core has index at most two over that
intersection. This includes the degree-two unitary extension. -/
theorem Preparation.unitary_overcomponent_core_intersection
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J) :
    let Q := (residual H).pCoreIn 2
    let R := J.pCoreIn 2
    let Z := (center Q).map Q.subtype
    R ≤ sourceS L H ∧ residual H ⊓ R ≤ Q ∧
      ¬ residual H ⊓ R ≤ centralizer (residual H : Set G) ∧
      ⁅residual H ⊓ R,Q⁆ = Z ∧ Z ≤ residual H ⊓ R ∧
      (residual H ⊓ R).relIndex R ≤ 2 := by
  let K := residual H
  let Q := K.pCoreIn 2
  let R := J.pCoreIn 2
  let N := K ⊓ R
  let Z := (center Q).map Q.subtype
  obtain ⟨hRH,hRS,hNQ,hnot⟩ := overcomponent_intersection_noncentral
    (h.qtke.evenCharacteristic T) h.sylow_normalizes hH.1.1.2 rfl hp
    (fun hb => d.right_outside (hb ▸ bot_le)) hJ hKJ
  obtain ⟨_,_,_,_,_,_,hc,_,_,hZK⟩ := d.unitary_core_structure h hH.1.1.2 hp m hm he
  have hZ : ((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype = Z :=
    map_embeddedCenter (pCore 2 K) K.subtype K.subtype_injective
  have hzcentral : Z ≤ centralizer (K : Set G) := by
    rw [←hZ]
    rintro _ ⟨x,hx,rfl⟩
    exact mem_centralizer_iff.mpr (fun y hy => congrArg Subtype.val
      ((mem_center_iff.mp (hZK hx)) ⟨y,hy⟩))
  have hder : ⁅Q,Q⁆ = Z := by
    change ⁅(pCore 2 K).map K.subtype,(pCore 2 K).map K.subtype⁆ = Z
    rw [←map_commutator,←map_subtype_commutator,←hc]
    exact hZ
  have hnotZ : ¬ N ≤ Z := fun hz => hnot (hz.trans hzcentral)
  obtain ⟨x,hx,hxz⟩ := SetLike.not_le_iff_exists.mp hnotZ
  let a : Q := ⟨x,hNQ hx⟩
  have ha : a ∉ center Q := fun ha => hxz ⟨a,ha,rfl⟩
  have hNZ : ⁅N,Q⁆ = Z := by
    apply le_antisymm ((commutator_mono hNQ le_rfl).trans_eq hder)
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨y,hy⟩ := core_commutator_surjective d h hH hp m hm he a ha ⟨z,hz⟩
    have hh := congrArg Subtype.val hy
    change ⁅x,y.val⁆ = z.val at hh
    change z.val ∈ ⁅N,Q⁆
    rw [←hh]
    exact commutator_mem_commutator hx y.property
  have hQN : Q ≤ normalizer (N : Set G) :=
    (le_inf ((pCoreIn_le 2 K).trans K.le_normalizer)
      ((pCoreIn_le 2 K).trans (hKJ.trans (J.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))))).trans
          inf_normalizer_le_normalizer_inf
  have hHS : H.pCoreIn 2 ≤ sourceS L H :=
    Chapter3.twoCore_le_of_sylow_le T (le_inf h.sylow_normalizes hH.1.1.2) inf_le_right
  have hXH : K ⊔ sourceS L H ≤ H := sup_le (map_subtype_le _)
    ((map_subtype_le _).trans inf_le_right)
  have hHU : H.pCoreIn 2 ≤ (K ⊔ sourceS L H).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hHS.trans le_sup_right)
      (hXH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  have hNU : N.relIndex R ≤ 2 := by
    have hi : N = Q ⊓ R := le_antisymm (le_inf hNQ inf_le_right)
      (inf_le_inf_right R (pCoreIn_le 2 K))
    rw [hi,inf_relIndex_right]
    exact (relIndex_le_of_le_right (hRH.trans hHU) index_ne_zero_of_finite).trans
      (d.core_index_le_two_of_comparison h hH.1.1.2 hp
        (he.elim (.unitary m hm) (.unitaryExtension m hm)))
  refine ⟨hRS,hNQ,hnot,hNZ,?_,hNU⟩
  change Z ≤ N
  rw [←hNZ,commutator_comm]
  exact le_normalizer_iff_commutator_le_right.mp hQN

/-- The literal image in J/O₂(J) has elementary two-core and retains the
original PSL₂(2^m) quotient. Its kernel is precisely the original intersection,
so the core is nontrivial exactly when O₂(K) is not contained in O₂(J). -/
theorem Preparation.unitary_overcomponent_quotient_image
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J) :
    let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
    f.ker = (J.pCoreIn 2).subgroupOf (residual H) ∧
      (pCore 2 (residual H)).map f = f.range.pCoreIn 2 ∧
      IsElementaryAbelian 2 (pCore 2 f.range) ∧
      ClassicalGroup.IsPSL (f.range ⧸ pCore 2 f.range) 2 (2^m) ∧
      (pCore 2 f.range = ⊥ ↔ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) := by
  let K := residual H
  let P := pCore 2 K
  let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
  let r := f.rangeRestrict
  obtain ⟨_,hNQ,_,_,hZN,_⟩ := d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ
  have hk : f.ker = (J.pCoreIn 2).subgroupOf K := by
    ext x
    change (QuotientGroup.mk (inclusion hKJ x) : J ⧸ pCore 2 J) = 1 ↔ x.val ∈ J.pCoreIn 2
    rw [QuotientGroup.eq_one_iff]
    exact (mem_map_iff_mem J.subtype_injective).symm
  have hkP : f.ker ≤ P := by
    intro x hx
    have hxR : x.val ∈ J.pCoreIn 2 := by
      have hh : x ∈ (J.pCoreIn 2).subgroupOf K := hk ▸ hx
      exact hh
    exact (mem_map_iff_mem K.subtype_injective).mp (hNQ ⟨x.property,hxR⟩)
  have hrker : IsPGroup 2 r.ker := by
    have hrk : r.ker = f.ker := f.ker_rangeRestrict
    rw [hrk]
    exact pCore_isPGroup.to_le hkP
  have hr : Function.Surjective r := f.rangeRestrict_surjective
  have hmap : P.map r = pCore 2 f.range := by
    have hpre : (pCore 2 f.range).comap r = P := r.comap_pCore_of_ker_isPGroup hr hrker
    rw [←hpre,map_comap_eq_self_of_surjective hr]
  have hmapG : P.map f = f.range.pCoreIn 2 := by
    change P.map f = (pCore 2 f.range).map f.range.subtype
    rw [←hmap,map_map]
    rfl
  obtain ⟨_,_,_,_,_,_,_,hfr,_,_⟩ := d.unitary_core_structure h hH.1.1.2 hp m hm he
  let g := r.subgroupMap P
  have hfg : frattini P ≤ g.ker := by
    intro x hx
    have hxZ : x ∈ center P := hfr.symm ▸ hx
    have hz : x.val.val ∈ (center (K.pCoreIn 2)).map (K.pCoreIn 2).subtype := by
      have hZmap : ((center P).map P.subtype).map K.subtype =
          (center (K.pCoreIn 2)).map (K.pCoreIn 2).subtype :=
        map_embeddedCenter P K.subtype K.subtype_injective
      rw [←hZmap]
      exact ⟨x.val,⟨x,hxZ,rfl⟩,rfl⟩
    have hxR := (hZN hz).2
    apply Subtype.ext
    apply Subtype.ext
    change (QuotientGroup.mk (inclusion hKJ x.val) : J ⧸ pCore 2 J) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ((mem_map_iff_mem J.subtype_injective).mp hxR)
  let fg := QuotientGroup.lift (frattini P) g hfg
  have hfgsurj : Function.Surjective fg := by
    intro x
    obtain ⟨y,rfl⟩ := r.subgroupMap_surjective P x
    exact ⟨QuotientGroup.mk' (frattini P) y,rfl⟩
  let : Fact (IsPGroup 2 P) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  have helem : IsElementaryAbelian 2 (P.map r) := IsElementaryAbelian.of_surjective fg hfgsurj
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  refine ⟨hk,hmapG,hmap ▸ helem,
    hf.2.2.2.2.of_mulEquiv (r.pCoreQuotientEquiv hr hrker).symm,?_⟩
  rw [←hmap,Subgroup.map_eq_bot_iff]
  change P ≤ r.ker ↔ K.pCoreIn 2 ≤ J.pCoreIn 2
  rw [f.ker_rangeRestrict,hk]
  exact map_le_iff_le_comap.symm

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
