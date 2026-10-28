module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallAutomizer
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Basic
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor

/-!
# Exact odd prime-power rotations in the small-automizer source

An odd prime-power cyclic group inverted by the original order-two image
of V is disjoint from the marked maximal subgroup: its intersection is
inverted by O₂(M), so its square belongs to both an odd group and a two-group.
Retaining the chosen rotation order in the dihedral construction and lifting
through the actual maximal core gives a quotient of the quaternion-core pair.
That pair has order 192, so its odd prime-power rotation has order three.

Source: Aschbacher–Smith E.2.17, the odd-rotation claim on printed p.230.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.Involution
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

omit [Finite H] in
private theorem rotation_disjoint_maximal_of_inverter_in_core
    (M : Subgroup H) (v r : H) {p a : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hv : v ∈ (pCore 2 M).map M.subtype) (hr : orderOf r = p ^ a)
    (hi : v*r*v⁻¹=r⁻¹) : Disjoint (zpowers r) M := by
  have hcop : Nat.Coprime p 2 :=
    Nat.coprime_two_right.mpr ((Fact.out : p.Prime).odd_of_ne_two hp)
  have hR : IsPGroup p (zpowers r) := IsPGroup.of_card (n := a) (by
    simpa only [Nat.card_zpowers] using hr)
  have hd : Disjoint (zpowers r) ((pCore 2 M).map M.subtype) :=
    hR.disjoint_of_coprime (pCore_isPGroup.map M.subtype) hcop
  apply disjoint_def.mpr
  intro x hx hxM
  have hi' : v*x*v⁻¹=x⁻¹ := by
    obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp hx
    rw [← conj_zpow,hi,inv_zpow]
  obtain ⟨vv,hvv,hvvG⟩ := hv
  let xx : M := ⟨x,hxM⟩
  have hcomm : xx*vv*xx⁻¹*vv⁻¹ ∈ pCore 2 M :=
    (pCore 2 M).mul_mem ((inferInstance : (pCore 2 M).Normal).conj_mem vv hvv xx)
      ((pCore 2 M).inv_mem hvv)
  have hix : vv*xx*vv⁻¹=xx⁻¹ := by
    apply Subtype.ext
    change (vv:H)*x*(vv:H)⁻¹=x⁻¹
    change (vv:H)=v at hvvG
    rw [hvvG]
    exact hi'
  have he : xx*vv*xx⁻¹*vv⁻¹=xx^2 := by
    have h := congrArg Inv.inv hix
    have hh : vv*xx⁻¹*vv⁻¹=xx := by simpa only [mul_inv_rev,inv_inv,mul_assoc] using h
    rw [mul_assoc xx vv,mul_assoc xx,hh,pow_two]
  rw [he] at hcomm
  have hx2 : x^2=1 := disjoint_def.mp hd (pow_mem hx 2)
    (mem_map_of_mem M.subtype hcomm)
  let z : zpowers r := ⟨x,hx⟩
  have hz2 : z^2=1 := Subtype.ext hx2
  have hz : z=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hR.orderOf_coprime hcop z) dvd_rfl (orderOf_dvd_of_pow_eq_one hz2))
  exact congrArg Subtype.val hz

/-- The inverted-line construction retains the chosen exponent and literal join.
This also applies when the elementary actor has order larger than two, provided
every actor fixes or inverts the chosen rotation. -/
theorem exists_witness_of_inverted_prime_power_line {p : ℕ} [Fact p.Prime]
    (M V : Subgroup H) [IsElementaryAbelian 2 V] (hVM : V ≤ M)
    (g v : H) (a : ℕ) (hv : v ∈ V) (ha : 0 < a) (hord : orderOf g = p^a)
    (ho : Odd (orderOf g)) (hg : g ≠ 1)
    (hi : v*g*v⁻¹ = g⁻¹) (hsign : ∀ w ∈ V, w*g*w⁻¹=g ∨ w*g*w⁻¹=g⁻¹)
    (hDM : Disjoint (zpowers g) M) :
    ∃ w : Solvable.CoreFreeWitness M V p,
      w.exponent = a ∧ w.subgroup = zpowers g ⊔ V := by
  let D := zpowers g
  let I := D ⊔ V
  have hn := Theory.GroupTheory.normalizes_cyclic_of_identity_or_inversion V g hsign
  have hdM : Disjoint D M := hDM
  have hdV : Disjoint D V := hdM.mono_right hVM
  have hMI : M ⊓ I = V := by
    apply le_antisymm ?_ (le_inf hVM le_sup_right)
    intro x hx
    have hh : x ∈ (D : Set H) * (V : Set H) := by
      rw [← coe_mul_of_right_le_normalizer_left D V hn]
      exact hx.2
    obtain ⟨d,hd,w,hw,he⟩ := hh
    have hd' : d ∈ M := by
      have hh := M.mul_mem hx.1 (M.inv_mem (hVM hw))
      rwa [← he,mul_inv_cancel_right] at hh
    have hd1 := disjoint_def.mp hdM hd hd'
    have heq : w = x := by simpa only [hd1,one_mul] using he
    exact heq ▸ hw
  have hVle : V ≤ I := le_sup_right
  let U := V.subgroupOf I
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVle
  let gg : I := ⟨g,(show D ≤ I from le_sup_left) (mem_zpowers g)⟩
  let vv : I := ⟨v,hVle hv⟩
  have hgen : zpowers gg ⊔ U = ⊤ := by
    apply (map_injective I.subtype_injective)
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,map_subgroupOf_eq_of_le hVle,
      ← MonoidHom.range_eq_map,range_subtype]
    rfl
  have hvU : vv ∈ U := hv
  have hi' : vv*gg*vv⁻¹=gg⁻¹ := Subtype.ext hi
  have hsign' : ∀w∈U,w*gg*w⁻¹=gg ∨ w*gg*w⁻¹=gg⁻¹ := by
    intro w hw
    rcases hsign w hw with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have ho' : Odd (orderOf gg) := by rwa [← Subgroup.orderOf_coe]
  have hg' : gg ≠ 1 := fun hh => hg (congrArg Subtype.val hh)
  have hcard : Nat.card I = orderOf g * Nat.card V := by
    simpa only [D,I,Nat.card_zpowers] using card_sup_eq_mul_of_normalizes_of_disjoint D V hn hdV
  have hidx : U.index = orderOf g := by
    have hh := U.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hVle).toEquiv,hcard] at hh
    have hpos : 0 < Nat.card V := Nat.card_pos
    nlinarith
  have hpU : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  let S : Sylow 2 I := hpU.toSylow (by rw [hidx]; exact ho.not_two_dvd_nat)
  have hM : M.subgroupOf I = U := by
    ext x
    exact ⟨fun hx => hMI.le ⟨hx,x.property⟩,fun hx => hVM hx⟩
  have hquot := Solvable.quotient_equiv_dihedral U gg vv hvU ho' hg' hgen hi' hsign'
  rw [← Subgroup.orderOf_coe,hord] at hquot
  refine ⟨⟨I,hVle,gg,?_,S,?_,hM,a,ha,?_⟩,rfl,rfl⟩
  · exact (Theory.GroupTheory.conjugate_join_eq_cyclic_sup U gg vv hvU ho' hi').trans hgen
  · exact map_subgroupOf_eq_of_le hVle
  · rwa [hM]

/-- Keep the specified prime-power order in the literal core-free dihedral pair. -/
theorem exists_pair_of_inverted_prime_power (T : Sylow 2 H) (M V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hcore : V ≤ (pCore 2 M).map M.subtype) (hcard : Nat.card V = 2)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (v r : H)
    (hv : v ∈ V) (hv1 : v ≠ 1) (hr : orderOf r = p^a) (hi : v*r*v⁻¹=r⁻¹) :
    ∃ w : QuotientLift.Pair T M V,
      Nonempty ((w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore) ≃* DihedralGroup (p^a)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hd := rotation_disjoint_maximal_of_inverter_in_core M v r hp2 (hcore hv) hr hi
  have hsign : ∀ w∈V,w*r*w⁻¹=r ∨ w*r*w⁻¹=r⁻¹ := by
    intro w hw
    by_cases h : w=1
    · left; simp only [h,one_mul,inv_one,mul_one]
    · have he : w=v := by
        obtain ⟨x,hx,hu⟩ := (Nat.card_eq_two_iff' (1:V)).mp hcard
        exact congrArg Subtype.val ((hu ⟨w,hw⟩ (fun he => h (congrArg Subtype.val he))).trans
          (hu ⟨v,hv⟩ (fun he => hv1 (congrArg Subtype.val he))).symm)
      exact Or.inr (he ▸ hi)
  have hlarge : 1 < p^a := Nat.one_lt_pow (Nat.ne_of_gt ha) hp.one_lt
  obtain ⟨w,he,_⟩ := exists_witness_of_inverted_prime_power_line M V (hcore.trans (map_subtype_le _)) r v a hv
    ha hr (hr ▸ (hp.odd_of_ne_two hp2).pow)
    (fun h => hlarge.ne' (hr.symm.trans (h ▸ orderOf_one))) hi hsign hd
  have hTS : (T : Subgroup H).subgroupOf w.subgroup = w.sylow := by
    apply w.sylow.is_maximal' T.isPGroup'.comap_subtype
    intro x hx
    have hV : (x:H) ∈ (w.sylow : Subgroup w.subgroup).map w.subgroup.subtype :=
      mem_map_of_mem w.subgroup.subtype hx
    rw [w.sylow_eq] at hV
    exact hVT hV
  have hmap : (w.sylow : Subgroup w.subgroup).map w.subgroup.subtype =
      (T : Subgroup H) ⊓ w.subgroup := by
    rw [←hTS,subgroupOf_map_subtype]
  have htwo : IsPGroup 2 (M.subgroupOf w.subgroup).normalCore := by
    rw [w.maximal_eq]
    exact ((IsElementaryAbelian.isPGroup 2 V).comap_subtype).to_le (normalCore_le _)
  have hclosed : ∃ S : Sylow 2 (M.subgroupOf w.subgroup).normalCore,
      (S : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal := by
    refine ⟨(htwo.to_subgroup ⊤).toSylow (by simp),?_⟩
    exact inferInstanceAs (⊤ : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal
  exact ⟨⟨w.subgroup,w.le,w.conjugator,w.generate,w.sylow,hmap,hclosed⟩,
    he ▸ w.dihedral⟩

/-- Every nontrivial odd prime-power rotation inverted by the original
order-two V-image has order three in the small-automizer source. -/
theorem source_prime_power_inverter_eq_three
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hcard : Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (v r : H ⧸ ChapterB.minimalParabolicCore T hP)
    (hv : v ∈ V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
    (hv1 : v ≠ 1) (hr : orderOf r = p^a) (hi : v*r*v⁻¹=r⁻¹) : p^a = 3 := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hWcore : W ≤ (pCore 2 (M.map q)).map (M.map q).subtype :=
    (map_mono hcore).trans (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  obtain ⟨w,⟨e⟩⟩ := exists_pair_of_inverted_prime_power S (M.map q) W
    (map_mono hVT) hWcore hcard hp hp2 ha v r hv hv1 hr hi
  obtain ⟨w',_,_,_,e',_⟩ := QuotientLift.lift_pair T hP V hVT hvn hcore w
  let b : BenderPlacement.OriginalWitness T M V 1 :=
    ⟨w',1,by decide,one_dvd _,.dihedral rfl p a hp hp2 ha (e'.trans e)⟩
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hNV := ChapterE.minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  obtain ⟨⟨d⟩,_,_,⟨e6⟩,_⟩ := b.small_quaternion_core hVT hTV hcore hNV hfit hV hTU hU
    f hf hk hD hratio
  have hpc : Nat.card (pCore 2 w'.subgroup) = 32 := by
    have hh := d.card
    change Nat.card ((pCore 2 w'.subgroup).map w'.subgroup.subtype) = 32 at hh
    rwa [card_map_of_injective w'.subgroup.subtype_injective] at hh
  have hidx : (pCore 2 w'.subgroup).index = 6 := by
    change Nat.card (w'.subgroup ⧸ pCore 2 w'.subgroup) = 6
    rw [Nat.card_congr e6.toEquiv,DihedralGroup.nat_card]
  have hI : Nat.card w'.subgroup = 192 := by
    have hh := (pCore 2 w'.subgroup).card_mul_index
    rw [hpc,hidx] at hh
    omega
  have hdvd : p^a ∣ 192 := by
    have hc : Nat.card (w'.subgroup ⧸ (M.subgroupOf w'.subgroup).normalCore) = 2*p^a := by
      rw [Nat.card_congr (e'.trans e).toEquiv,DihedralGroup.nat_card]
    have hq := (M.subgroupOf w'.subgroup).normalCore.index_dvd_card
    change Nat.card (w'.subgroup ⧸ (M.subgroupOf w'.subgroup).normalCore) ∣ _ at hq
    rw [hc,hI] at hq
    exact (dvd_mul_left (p^a) 2).trans hq
  change p^a ∣ 2^6*3 at hdvd
  have hcop : Nat.Coprime (p^a) (2^6) :=
    ((Nat.coprime_two_right.mpr (hp.odd_of_ne_two hp2)).pow_left a).pow_right 6
  have hthree := hcop.dvd_of_dvd_mul_left hdvd
  exact ((Nat.dvd_prime Nat.prime_three).mp hthree).resolve_left
    (Nat.one_lt_pow (Nat.ne_of_gt ha) hp.one_lt).ne'

end CFSG.Quasithin.ChapterE.Witnesses.Involution
