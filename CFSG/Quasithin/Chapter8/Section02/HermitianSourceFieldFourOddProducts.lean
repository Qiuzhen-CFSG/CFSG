module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSolvable
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.SmallPrimePower
public import Theory.GroupTheory.InvolutionCentralizerControl
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Odd rotations and the actual Hermitian parabolic quotient

The order-two image of the original V survives the full maximal core J.
The image of J modulo O₂(H) centralizes that involution. Consequently an
odd cyclic group inverted by it intersects the kernel of H/O₂(H) → H/J
trivially, so the exact rotation order survives. The original dihedral-pair
lifting construction then supplies a selected pair whose two-core quotient
has that same order. Its ambient inclusion, Sylow intersection and full
normal-core quotient are transported together.

When the original maximal subgroup normalizes V, its image in H/O₂(H)
is exactly the centralizer of V⁺. Maximality and the vanishing quotient
two-core prove equality; it is not an assumed automizer identification.
The Chapter12 consumer applies these facts to every inverted odd prime
power on the original chosen-module action and proves the 3/5 restriction.

Source: Aschbacher–Smith 8.2.9, printed p.720, using E.2.9 and B.6.8,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE Offenders.Parabolic.Construction
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem inverted_order_preserved {Y : Type*} [Group Y]
    (f : X →* Y) (v r : X) (ho : Odd (orderOf r))
    (hi : v*r*v⁻¹=r⁻¹) (hc : v ∈ centralizer (f.ker : Set X)) :
    orderOf (f r) = orderOf r := by
  let R := zpowers r
  have hfi : Function.Injective (f.comp R.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hk : (x : X) ∈ f.ker := hx
    have hix : v*(x:X)*v⁻¹=(x:X)⁻¹ := by
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp x.property
      rw [←hk,←conj_zpow,hi,inv_zpow]
    have he : v*(x:X)*v⁻¹=(x:X) := by
      rw [←hc (x:X) hk,mul_inv_cancel_right]
    have hx2 : x^2=1 := by
      apply Subtype.ext
      change (x:X)^2=1
      rw [pow_two]
      exact (congrArg (fun z : X => z * (x:X)) (he.symm.trans hix)).trans (inv_mul_cancel _)
    have hox : Odd (orderOf x) := Odd.of_dvd_nat ho (by
      simpa only [R,Nat.card_zpowers] using orderOf_dvd_natCard x)
    have hx1 : x=1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hox.coprime_two_right dvd_rfl
        (orderOf_dvd_of_pow_eq_one hx2))
    exact hx1
  exact (orderOf_injective (f.comp R.subtype) hfi ⟨r,mem_zpowers r⟩).trans
    (Subgroup.orderOf_coe ⟨r,mem_zpowers r⟩).symm

/-- The marked involution survives the full maximal core, and every odd
rotation it inverts retains its exact order in the star quotient. -/
theorem parabolic_involution_star_transport
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W]
    (hcore : W ≤ (minimalParabolicMax S hP).pCoreIn 2)
    (hout : ¬ W ≤ minimalParabolicCore S hP)
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) = 2) :
    Nat.card (W.map (QuotientGroup.mk' (minimalParabolicCore S hP))) = 2 ∧
      ∃ f : (X ⧸ pCore 2 X) →* (X ⧸ minimalParabolicCore S hP),
        (∀ x : X, f (QuotientGroup.mk' (pCore 2 X) x) =
          QuotientGroup.mk' (minimalParabolicCore S hP) x) ∧
        (∀ v ∈ W.map (QuotientGroup.mk' (pCore 2 X)), ∀ r,
          Odd (orderOf r) → v*r*v⁻¹=r⁻¹ → orderOf (f r)=orderOf r) := by
  let Q := pCore 2 X
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' Q
  let j := QuotientGroup.mk' J
  let f : (X ⧸ Q) →* (X ⧸ J) := QuotientGroup.map Q J (MonoidHom.id X)
    (by simpa using minimalParabolicTwoCore_le_core S hP)
  have hf : f.comp q = j := by ext x; rfl
  have hmap : (W.map q).map f = W.map j := by rw [map_map,hf]
  have hle : Nat.card (W.map j) ≤ 2 := by
    rw [←hmap]
    exact (Nat.le_of_dvd Nat.card_pos (card_dvd_of_surjective (f.subgroupMap (W.map q))
      (f.subgroupMap_surjective _))).trans_eq hcard
  have hne : W.map j ≠ ⊥ := by
    intro he
    apply hout
    simpa only [j,QuotientGroup.ker_mk'] using (map_eq_bot_iff W).mp he
  have htwo : Nat.card (W.map j) = 2 := by
    have := (one_lt_card_iff_ne_bot _).mpr hne
    omega
  refine ⟨htwo,f,(fun _ => rfl),?_⟩
  intro v hv r ho hi
  apply inverted_order_preserved f v r ho hi
  intro z hz
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective Q z
  have hxJ : x ∈ J := (QuotientGroup.eq_one_iff x).mp hz
  have hcomm := Witnesses.Solvable.pair_centralizes_core_modulo_twoCore S hP W hcore 1
  exact hcomm (mem_map.mpr (by
    obtain ⟨w,hw,he⟩ := hv
    exact ⟨w,mem_sup_left hw,he⟩)) (q x) (mem_map_of_mem q hxJ)

/-- The actual maximal image is the centralizer of the marked involution,
with both the two-core quotient and the original maximal subgroup retained. -/
theorem parabolic_maximal_image_involution_centralizer
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W]
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) = 2) :
    (minimalParabolicMax S hP).map (QuotientGroup.mk' (pCore 2 X)) =
      centralizer (W.map (QuotientGroup.mk' (pCore 2 X)) : Set (X ⧸ pCore 2 X)) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let A := W.map q
  let N := normalizer (A : Set (X ⧸ pCore 2 X))
  have hMN : minimalParabolicMax S hP ≤ N.comap q :=
    map_le_iff_le_comap.mp ((map_mono hMW).trans (le_normalizer_map q))
  have hNne : N ≠ ⊤ := by
    intro he
    let : A.Normal := normalizer_eq_top_iff.mp he
    have hA : A ≤ pCore 2 (X ⧸ pCore 2 X) :=
      le_sSup ⟨inferInstance,(IsElementaryAbelian.isPGroup 2 W).map q⟩
    rw [pCore_quotient_pCore_eq_bot 2] at hA
    have hb : A = ⊥ := bot_unique hA
    change Nat.card A = 2 at hcard
    rw [hb,card_bot] at hcard
    omega
  have hpre : N.comap q = minimalParabolicMax S hP := by
    by_contra hne
    have ht := (minimalParabolicMax_spec S hP).1.2 _ (lt_of_le_of_ne hMN (Ne.symm hne))
    apply hNne
    have hh := congrArg (map q) ht
    have hqr : q.range = ⊤ := q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective _)
    simpa only [map_comap_eq,←MonoidHom.range_eq_map,hqr,top_inf_eq] using hh
  have he : (minimalParabolicMax S hP).map q = N := by
    rw [←hpre,map_comap_eq,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),top_inf_eq]
  exact he.trans (le_antisymm (normalizer_le_centralizer_of_card_two A hcard)
    (Subgroup.centralizer_le_normalizer _))

/-- Lift a specified odd prime-power rotation from H/O₂(H) through the
full maximal core. The resulting genuine pair retains the exact dihedral order. -/
theorem parabolic_pair_of_inverted_prime_power
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hWN : (W.subgroupOf (S : Subgroup X)).Normal)
    (hcore : W ≤ (minimalParabolicMax S hP).pCoreIn 2)
    (hout : ¬ W ≤ minimalParabolicCore S hP)
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) = 2)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (v r : X ⧸ pCore 2 X)
    (hv : v ∈ W.map (QuotientGroup.mk' (pCore 2 X))) (hv1 : v ≠ 1)
    (hr : orderOf r = p^a) (hi : v*r*v⁻¹=r⁻¹) :
    ∃ w : Witnesses.QuotientLift.Pair S (minimalParabolicMax S hP) W,
      Nonempty ((w.subgroup ⧸ ((minimalParabolicMax S hP).subgroupOf w.subgroup).normalCore)
        ≃* DihedralGroup (p^a)) := by
  obtain ⟨htwo,f,hf,hord⟩ := parabolic_involution_star_transport S hP W hcore hout hcard
  let J := minimalParabolicCore S hP
  let M := minimalParabolicMax S hP
  let q := QuotientGroup.mk' J
  let R := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let A := W.map q
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hfv : f v ∈ A := by
    obtain ⟨x,hx,rfl⟩ := hv
    rw [hf]
    exact mem_map_of_mem q hx
  have hfv1 : f v ≠ 1 := by
    intro he
    obtain ⟨x,hx,hxv⟩ := hv
    have hxJ : x ∈ J := (QuotientGroup.eq_one_iff x).mp (by
      change QuotientGroup.mk' J x = 1
      exact (hf x).symm.trans ((congrArg f hxv).trans he))
    have hxQ : x ∈ pCore 2 X := (minimalParabolic_sylow_inf_core S hP).le ⟨hWS hx,hxJ⟩
    exact hv1 (hxv.symm.trans ((QuotientGroup.eq_one_iff x).mpr hxQ))
  have hr' : orderOf (f r) = p^a :=
    (hord v hv r (hr ▸ (hp.odd_of_ne_two hp2).pow) hi).trans hr
  have hi' : f v*f r*(f v)⁻¹=(f r)⁻¹ := by
    simpa only [map_mul,map_inv] using congrArg f hi
  have hAcore : A ≤ (M.map q).pCoreIn 2 :=
    (map_mono hcore).trans (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  obtain ⟨w,⟨e⟩⟩ := Witnesses.Involution.exists_pair_of_inverted_prime_power R (M.map q) A
    (map_mono hWS) hAcore htwo hp hp2 ha (f v) (f r) hfv hfv1 hr' hi'
  obtain ⟨w',_,_,_,e',_⟩ := Witnesses.QuotientLift.lift_pair S hP W hWS hWN hcore w
  exact ⟨w',⟨e'.trans e⟩⟩

variable {G : Type*} [Group G] [Finite G]

private theorem map_left_pair {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (W : Subgroup X) (x : X) :
    (W ⊔ W.map (MulAut.conj x).toMonoidHom).map f =
      W.map f ⊔ (W.map f).map (MulAut.conj (f x)).toMonoidHom := by
  rw [Subgroup.map_sup,map_map,map_map]
  congr 2
  ext y
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

private theorem family_of_marked_dihedral_pair
    {H T M V : Subgroup G} (hVH : V ≤ H)
    (hV : IsElementaryAbelian 2 V) (hne : V ≠ ⊥) (hVT : V ≤ T)
    (R : Sylow 2 H) (hR : (R : Subgroup H) = T.subgroupOf H)
    (w : Witnesses.QuotientLift.Pair R (M.subgroupOf H) (V.subgroupOf H))
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (d : (w.subgroup ⧸ ((M.subgroupOf H).subgroupOf w.subgroup).normalCore) ≃*
      DihedralGroup (p^a)) :
    ∃ I : Subgroup G, Family H T M V I 1 ∧
      RankOneAlternative (Star M I) (starImage M I M) 1 ∧
      Nonempty (Star M I ≃* DihedralGroup (p^a)) := by
  let J := w.subgroup
  let I := J.map H.subtype
  let e : J ≃* I := J.equivMapOfInjective H.subtype H.subtype_injective
  let A := (M.subgroupOf H).subgroupOf J
  have hA : (M.subgroupOf I).comap e.toMonoidHom = A := by ext x; rfl
  have hC : (localCore M I).comap e.toMonoidHom = A.normalCore := by
    rw [←normalCore_comap_of_surjective e.toMonoidHom e.surjective,hA]
  have hCm : A.normalCore.map e.toMonoidHom = localCore M I := by
    rw [←hC,map_comap_eq,MonoidHom.range_eq_top.mpr e.surjective,top_inf_eq]
  let ec : A.normalCore ≃* localCore M I :=
    (e.subgroupMap A.normalCore).trans (MulEquiv.subgroupCongr hCm)
  have hclosed : IsTwoClosed (localCore M I) := by
    obtain ⟨P,hP⟩ := w.core_two_closed
    let := hP
    refine ⟨P.mapSurjective (f := ec.toMonoidHom) ec.surjective,?_⟩
    exact Normal.map hP ec.toMonoidHom ec.surjective
  let eqt : (J ⧸ A.normalCore) ≃* Star M I :=
    QuotientGroup.equivOfSurjectiveComap e.toMonoidHom e.surjective _ _ hC
  have hr : RankOneAlternative (Star M I) (starImage M I M) 1 := by
    exact Or.inr (Or.inr ⟨rfl,p,a,hp,hp.odd_of_ne_two hp2,ha,⟨eqt.symm.trans d⟩⟩)
  have hgen : V ⊔ V.map (MulAut.conj (w.conjugator.val.val)).toMonoidHom = I := by
    have hh := congrArg (fun B : Subgroup J => B.map (H.subtype.comp J.subtype)) w.generate
    rw [map_left_pair] at hh
    have hm : ((V.subgroupOf H).subgroupOf J).map (H.subtype.comp J.subtype) = V := by
      rw [←map_map,map_subgroupOf_eq_of_le w.le,map_subgroupOf_eq_of_le hVH]
    rw [hm,←MonoidHom.range_eq_map,MonoidHom.range_comp,J.range_subtype] at hh
    exact hh
  let S := w.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS : (S : Subgroup I) = T.subgroupOf I := by
    apply map_injective I.subtype_injective
    change ((w.sylow : Subgroup J).map e.toMonoidHom).map I.subtype = _
    rw [map_map]
    have hf : I.subtype.comp e.toMonoidHom = H.subtype.comp J.subtype := rfl
    rw [hf,←map_map,w.sylow_eq,hR,map_inf _ _ _ H.subtype_injective,
      subgroupOf_map_subtype,subgroupOf_map_subtype]
    change (T ⊓ H) ⊓ I = T ⊓ I
    rw [inf_assoc,inf_eq_right.mpr (map_subtype_le J)]
  refine ⟨I,⟨hV,hne,hVT,map_subtype_le J,?_,⟨S,hS⟩,hclosed,Or.inl hr,one_dvd _⟩,hr,⟨eqt.symm.trans d⟩⟩
  refine ⟨w.conjugator.val.val⁻¹,?_,?_⟩
  · exact I.inv_mem (mem_map_of_mem H.subtype w.conjugator.property)
  · simpa only [inv_inv] using hgen

/-- Every specified odd prime-power rotation inverted by V⁺ gives an actual
selected pair on the original V, with its exact dihedral two-core quotient. -/
theorem selected_pair_of_inverted_prime_power
    {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hfit : generalizedFitting H = pCore 2 H)
    (hq : 1 < Representation.BinaryOffender.quadraticRatio
      ((automizerRepresentation V).comp
        (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hcard : Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (v r : H ⧸ pCore 2 H)
    (hv : v ∈ (V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) (hv1 : v ≠ 1)
    (hr : orderOf r = p^a) (hi : v*r*v⁻¹=r⁻¹) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      Selected H T M V I 1 i S ∧ Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup (p^a)) := by
  have hVH := h.le_sylow.trans h.le_ambient
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h.minimal
  obtain ⟨hVR,hVN,hcore,hout⟩ := intrinsic_source_data h R hR hP hM
  have hex := parabolic_pair_of_inverted_prime_power R hP (V.subgroupOf H)
    hVR hVN hcore hout hcard hp hp2 ha v r hv hv1 hr hi
  rw [←hM] at hex
  obtain ⟨w,⟨e⟩⟩ := hex
  have hne : V ≠ ⊥ := by intro he; exact h.outside_core (he ▸ bot_le)
  obtain ⟨I,f,hm,⟨eI⟩⟩ := family_of_marked_dihedral_pair hVH h.elementary hne h.le_sylow
    R hR w hp hp2 ha e
  obtain ⟨i,S,s⟩ := exists_selected_of_rank_one_family h hfit f hm hq hTI hNV
  exact ⟨I,i,S,s,⟨(coreQuotientEquiv M I s.core_eq).symm.trans eI⟩⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
