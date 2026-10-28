module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.PlaneDisplacement
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.Center

/-!
# The four-element displacement in the J.4 span

For the original conjugate Uα and its selected involution, the natural four-space
has displacement dimension two. The five-module splitting makes its projection
from Q/U injective on [Q,Uα]. Thus the literal image of this commutator has order
four and is disjoint from HC/U. This is the displacement calculation in J.4.2.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

private theorem natural_involution_range_card (r : L2FourAction) (t : S5)
    (ht : t*t=1) (ht1 : t≠1) : Nat.card (r.action t - 1).range = 4 := by
  let D := r.action t - 1
  have hbin (v : FourSpace) : v+v=0 := by
    have h := @two_smul (ZMod 2) FourSpace _ _ _ v
    rw [show (2:ZMod 2)=0 by decide,zero_smul] at h
    exact h.symm
  have hincl : D.range ≤ D.ker := by
    rintro _ ⟨w,rfl⟩
    change r.action t (r.action t w-w) - (r.action t w-w) = 0
    have haa : r.action t (r.action t w)=w := by
      rw [← Module.End.mul_apply,← map_mul,ht,map_one,Module.End.one_apply]
    rw [map_sub,haa]
    calc
      _ = (w+w)-(r.action t w+r.action t w) := by abel
      _ = 0 := by rw [hbin,hbin,sub_self]
  have hne : Module.finrank (ZMod 2) D.range ≠ 0 := by
    intro hh
    have hz : D=0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hh)
    apply ht1
    apply r.injective
    simpa only [map_one] using sub_eq_zero.mp hz
  have hs := D.finrank_range_add_finrank_ker
  rw [SL2FourNatural.finrank_vector] at hs
  have hm := Submodule.finrank_mono hincl
  have h1 := r.no_rank_one t
  change Module.finrank (ZMod 2) D.range ≠ 1 at h1
  have hd : Module.finrank (ZMod 2) D.range = 2 := by omega
  change Nat.card D.range = 4
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),hd,Nat.card_zmod]
  rfl

abbrev SourceChoice.vH (s : SourceChoice p) : d.toTypeRuSetup.H :=
  ⟨s.v,d.toTypeRuSetup.K_le_H s.v_mem_K⟩

/-- The quotient actor of each original conjugate element is identity or the selected actor. -/
theorem SourceChoice.star_actor_cases (s : SourceChoice p) (u : d.toTypeRuSetup.H)
    (hu : (u:G)∈s.Uα) :
    d.ru2.quotientMap u=1 ∨ d.ru2.quotientMap u=d.ru2.quotientMap s.vH := by
  let A := (s.Uα.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap
  have hA : Nat.card A=2 := s.conjugate_properties.2.1
  have hvA : d.ru2.quotientMap s.vH ∈ A := mem_map.mpr ⟨s.vH,s.v_mem,rfl⟩
  have huA : d.ru2.quotientMap u ∈ A := mem_map.mpr ⟨u,hu,rfl⟩
  by_cases he : d.ru2.quotientMap u=1
  · exact Or.inl he
  have hv1 : d.ru2.quotientMap s.vH ≠ 1 := by
    intro h
    have hh : s.vH∈d.ru2.quotientMap.ker := h
    rw [d.ru2.quotient_kernel] at hh
    exact s.v_not_Q hh
  obtain ⟨a,ha,huniq⟩ := (Nat.card_eq_two_iff' (1:A)).mp hA
  exact Or.inr (congrArg Subtype.val
    ((huniq ⟨_,huA⟩ (fun h => he (congrArg Subtype.val h))).trans
      (huniq ⟨_,hvA⟩ (fun h => hv1 (congrArg Subtype.val h))).symm))

abbrev SourceChoice.displacement (s : SourceChoice p) : Subgroup G :=
  ⁅d.toTypeRuSetup.Q,s.Uα⁆

theorem SourceChoice.displacement_le_Q (s : SourceChoice p) : s.displacement ≤ d.toTypeRuSetup.Q :=
  le_normalizer_iff_commutator_le_left.mp
    (s.Uα_le_K.trans (d.toTypeRuSetup.K_le_H.trans d.ru2.six.normalized))

/-- The actual natural-head image of [Q,Uα] is the selected actor's displacement range. -/
theorem SourceChoice.head_displacement_image (s : SourceChoice p) :
    d.fusionNaturalHead.sectionData.imageSpace s.displacement =
      (d.fusionNaturalHead.action.action (d.ru2.quotientMap s.vH)-1).range := by
  let head := d.fusionNaturalHead
  let D := head.action.action (d.ru2.quotientMap s.vH)-1
  apply le_antisymm
  · let R : Subgroup (Multiplicative FourSpace) := D.range.toAddSubgroup.toSubgroup
    let N : Subgroup G := (R.comap head.sectionData.coordinates).map d.toTypeRuSetup.Q.subtype
    have hbound : s.displacement ≤ N := by
      rw [SourceChoice.displacement,commutator_comm]
      apply commutator_le.mpr
      intro u hu q hq
      let uH : d.toTypeRuSetup.H := ⟨u,d.toTypeRuSetup.K_le_H (s.Uα_le_K hu)⟩
      let a : d.toTypeRuSetup.Q := ⟨q,hq⟩
      let a' : d.toTypeRuSetup.Q := ⟨u*q*u⁻¹,
        (mem_normalizer_iff.mp (d.ru2.six.normalized uH.property) q).mp hq⟩
      have he := head.sectionData.equivariant uH a
      change (head.sectionData.coordinates a').toAdd =
        head.action.action (d.ru2.quotientMap uH) (head.sectionData.coordinates a).toAdd at he
      have hR : a'*a⁻¹ ∈ R.comap head.sectionData.coordinates := by
        change (head.sectionData.coordinates (a'*a⁻¹)).toAdd ∈ D.range
        rw [map_mul,map_inv]
        change (head.sectionData.coordinates a').toAdd +
          -(head.sectionData.coordinates a).toAdd ∈ D.range
        rw [← sub_eq_add_neg]
        rw [he]
        rcases s.star_actor_cases uH hu with h | h
        · rw [h,map_one,Module.End.one_apply,sub_self]
          exact D.range.zero_mem
        · rw [h]
          exact ⟨(head.sectionData.coordinates a).toAdd,rfl⟩
      exact mem_map.mpr ⟨a'*a⁻¹,hR,rfl⟩
    intro v hv
    obtain ⟨q,hq,rfl⟩ := (head.sectionData.mem_imageSpace_iff _ _).mp hv
    obtain ⟨a,ha,he⟩ := hbound hq
    have hqa : a=q := Subtype.ext he
    rw [hqa] at ha
    exact ha
  · exact head.sectionData.displacement_range_le_imageSpace_of_commutator_le
      s.Uα s.displacement (by rw [commutator_comm]) s.vH s.v_mem

/-- The selected nontrivial inner involution has a four-element natural displacement. -/
theorem SourceChoice.head_displacement_card (s : SourceChoice p) :
    Nat.card (d.fusionNaturalHead.sectionData.imageSpace s.displacement) = 4 := by
  rw [s.head_displacement_image]
  apply natural_involution_range_card
  · rw [← map_mul]
    have hv : s.vH*s.vH=1 := Subtype.ext (by
      change s.v*s.v=1
      rw [← pow_two,← s.v_order]
      exact pow_orderOf_eq_one s.v)
    rw [hv,map_one]
  · intro h
    have hh : s.vH∈d.ru2.quotientMap.ker := h
    rw [d.ru2.quotient_kernel] at hh
    exact s.v_not_Q hh

theorem six_image_card_eq_hat (d : LocalSetup G) (A : Subgroup G)
    (hA : A ≤ d.toTypeRuSetup.Q) :
    Nat.card (d.ru2.six.imageSpace A) = Nat.card (hat d A) := by
  let f : d.ru2.six.imageSpace A → hat d A := fun v =>
    ⟨sixToHat d (Multiplicative.ofAdd v.val),by
      obtain ⟨q,hq,hv⟩ := (d.ru2.six.mem_imageSpace_iff A v.val).mp v.property
      rw [← hv]
      change sixToHat d (d.ru2.six.coordinates q) ∈ hat d A
      rw [sixToHat_coordinates]
      exact mem_map.mpr ⟨inclusion (pCoreIn_le 2 _) q,hq,rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact Multiplicative.ofAdd.injective (sixToHat_injective d (congrArg Subtype.val he))
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨h,hh,he⟩ := x.property
    let q : d.toTypeRuSetup.Q := ⟨h,hA hh⟩
    refine ⟨⟨(d.ru2.six.coordinates q).toAdd,
      (d.ru2.six.mem_imageSpace_iff A _).mpr ⟨q,hh,rfl⟩⟩,?_⟩
    apply Subtype.ext
    exact (sixToHat_coordinates d q).trans he
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)

theorem hat_HC_eq_hat_CQ (B5 : Sylow 5 d.toTypeRuSetup.H) :
    hat d d.toTypeRuSetup.HC = hat d (CQ B5) := by
  have hU : hat d d.toTypeRuSetup.U = ⊥ := by
    change (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H).map (hatMap d) = ⊥
    exact (Subgroup.map_eq_bot_iff _).mpr (by intro u hu; exact (hatMap_eq_one d u).mpr hu)
  calc
    _ = hat d (CQ B5 ⊔ d.toTypeRuSetup.U) := congrArg (hat d) (five_centralizer_sup_U B5).symm
    _ = _ := by
      rw [hat_sup d ((five_centralizer_le_HC B5).trans inf_le_left)
        d.ru2.natural.section_le,hU,sup_bot_eq]

/-- The actual displacement has no nonzero fixed-plane component. -/
theorem SourceChoice.hat_displacement_disjoint_HC (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Disjoint (hat d s.displacement) (hat d d.toTypeRuSetup.HC) := by
  rw [hat_HC_eq_hat_CQ B5]
  exact (hat_Q_split d B5).2.symm.mono_left
    (hat_mono d (s.commutator_Q_Uα_le_Q₅ B5 hi))

/-- The native natural-head projection is injective on the actual displacement. -/
theorem SourceChoice.displacement_projection_bijective (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃ f : d.ru2.six.imageSpace s.displacement →
        d.fusionNaturalHead.sectionData.imageSpace s.displacement,
      Function.Bijective f ∧ ∀ v, (f v).val = d.fusionNaturalHead.sixProjection d v.val := by
  let head := d.fusionNaturalHead
  let M := d.ru2.six.imageSpace s.displacement
  let N := head.sectionData.imageSpace s.displacement
  let f : M → N := fun v => ⟨head.sixProjection d v.val,by
    obtain ⟨q,hq,hv⟩ := (d.ru2.six.mem_imageSpace_iff _ _).mp v.property
    apply (head.sectionData.mem_imageSpace_iff _ _).mpr
    exact ⟨q,hq,(head.sixProjection_coordinates d q).symm.trans (congrArg (head.sixProjection d) hv)⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    have hp : head.sixProjection d (x.val-y.val)=0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val he)
    obtain ⟨q,hq,hqxy⟩ := (d.ru2.six.mem_imageSpace_iff _ _).mp (M.sub_mem x.property y.property)
    have hqC : (q:G)∈d.toTypeRuSetup.HC :=
      (head.sixProjection_kernel_coordinates d q).mp (by
        change head.sixProjection d (d.ru2.six.coordinates q).toAdd=0
        rwa [hqxy])
    let qH := inclusion (pCoreIn_le 2 d.toTypeRuSetup.H) q
    have hqe : hatMap d qH ∈ hat d s.displacement := mem_map.mpr ⟨qH,hq,rfl⟩
    have hqc : hatMap d qH ∈ hat d d.toTypeRuSetup.HC := mem_map.mpr ⟨qH,hqC,rfl⟩
    have hh := (s.hat_displacement_disjoint_HC B5 hi).le_bot ⟨hqe,hqc⟩
    have hqU := (hatMap_eq_one d qH).mp hh
    have hzero : (d.ru2.six.coordinates q).toAdd=0 :=
      congrArg Multiplicative.toAdd ((d.ru2.six.coordinates_eq_one_iff q).mpr hqU)
    apply Subtype.ext
    exact sub_eq_zero.mp (hqxy.symm.trans hzero)
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨q,hq,hv⟩ := (head.sectionData.mem_imageSpace_iff _ _).mp v.property
    refine ⟨⟨(d.ru2.six.coordinates q).toAdd,
      (d.ru2.six.mem_imageSpace_iff _ _).mpr ⟨q,hq,rfl⟩⟩,?_⟩
    exact Subtype.ext ((head.sixProjection_coordinates d q).trans hv)
  exact ⟨f,⟨hf,hs⟩,fun _ => rfl⟩

/-- The literal displacement in H/U has order four. -/
theorem SourceChoice.hat_displacement_card (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card (hat d s.displacement) = 4 := by
  obtain ⟨f,hf,_⟩ := s.displacement_projection_bijective B5 hi
  calc
    _ = Nat.card (d.ru2.six.imageSpace s.displacement) :=
      (six_image_card_eq_hat d s.displacement s.displacement_le_Q).symm
    _ = Nat.card (d.fusionNaturalHead.sectionData.imageSpace s.displacement) :=
      Nat.card_congr (Equiv.ofBijective f hf)
    _ = 4 := s.head_displacement_card

end CFSG.Quasithin.ChapterJ.RuSubgroup
