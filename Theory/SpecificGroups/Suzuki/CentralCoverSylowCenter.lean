module
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.InvolutionFusion
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.LocalCover
public import Theory.GroupTheory.Commutator.CentralElementaryEightQuotient
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.InnerInvolutionSylowCenter
public import Theory.SpecificGroups.Suzuki.BorelPointwiseRigidity
public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.RootQuotient

/-!
# Sylow centers in nontrivial perfect central covers of Sz(8)

Fusion and the unique Sylow centralizer show that a nonzero image of the
covering Sylow center covers the whole quotient Sylow center. Then the
covering Sylow has a central elementary-eight quotient, whose derived
order is at most eight. Central Sylow transfer places the nontrivial
covering kernel in that derived group, giving a contradiction. Hence the
covering center is the whole Sylow center. Perfect quotient faithfulness
then eliminates every involutory pointwise Sylow fixer.

Source: Aschbacher--Smith I.2.2(4), pp.409--411, applied to the actual
marked involution in 15.1.20--21, pp.1095--1098. No cover splitting is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups

/-- Conjugators between nontrivial central Sylow elements normalize that Sylow. -/
theorem suzuki_center_conjugator_normalizes {H : Type*} [Group H] [Finite H]
    {m : ℕ} (hm : 0<m) (e : H ≃* SuzukiMatrixGroup m) (P : Sylow 2 H)
    (a b : P) (ha : a ∈ center P) (hb : b ∈ center P)
    (ha1 : (a:H) ≠ 1) (hb1 : (b:H) ≠ 1) (g : H)
    (he : g*(a:H)*g⁻¹=b) : g ∈ normalizer (P : Set H) := by
  have hca : centralizer ({(a:H)} : Set H) = (P : Subgroup H) := by
    apply le_antisymm ((suzukiSylow_borel_structure hm e P).2.1 a a.property ha1)
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp ha (⟨x,hx⟩:P))
  have hcb : centralizer ({(b:H)} : Set H) = (P : Subgroup H) := by
    apply le_antisymm ((suzukiSylow_borel_structure hm e P).2.1 b b.property hb1)
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp hb (⟨x,hx⟩:P))
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    apply hcb.le
    apply mem_centralizer_singleton_iff.mpr
    have hc : Commute x (a:H) := mem_centralizer_singleton_iff.mp (hca.symm ▸ hx)
    have hh := hc.map (MulAut.conj g).toMonoidHom
    change Commute (g*x*g⁻¹) (g*(a:H)*g⁻¹) at hh
    rwa [he] at hh
  · intro hx
    apply hca.le
    apply mem_centralizer_singleton_iff.mpr
    have hc : Commute (g*x*g⁻¹) (b:H) := mem_centralizer_singleton_iff.mp (hcb.symm ▸ hx)
    have hh := hc.map (MulAut.conj g⁻¹).toMonoidHom
    have hg : g⁻¹*(b:H)*g=a := by rw [←he]; group
    simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] at hh
    simpa only [hg,inv_mul_cancel_left,mul_assoc,mul_inv_cancel,inv_mul_cancel,mul_one,one_mul] using hh.eq

variable {E : Type*} [Group E] [Finite E]
/-- A nonzero central Sylow image covers the whole Suzuki Sylow center. -/
theorem suzuki_cover_sylow_center_image
    {m : ℕ} (hm : 0<m) (f : E →* SuzukiMatrixGroup m)
    (hf : Function.Surjective f) (P : Sylow 2 E)
    (r : P) (hr : r ∈ center P) (hr1 : f r ≠ 1) :
    (center (P.mapSurjective hf)).map (P.mapSurjective hf : Subgroup (SuzukiMatrixGroup m)).subtype ≤
      ((center P).map (P : Subgroup E).subtype).map f := by
  let Q := P.mapSurjective hf
  let q : P →* Q := (f.comp (P : Subgroup E).subtype).codRestrict Q
    (fun x => mem_map_of_mem f x.property)
  have hq : Function.Surjective q := by
    rintro ⟨_,⟨x,hx,rfl⟩⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hrZ : q r ∈ center Q := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x,rfl⟩ := hq y
    exact (map_mul q x r).symm.trans ((congrArg q (mem_center_iff.mp hr x)).trans (map_mul q r x))
  have hsq (x : Q) (hx : x ∈ center Q) : (x:SuzukiMatrixGroup m)^2=1 := by
    let : IsElementaryAbelian 2 (omegaOneAmbient (Q : Subgroup (SuzukiMatrixGroup m))) :=
      suzukiSylow_omega_elementary hm (MulEquiv.refl _) Q
    apply elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=omegaOneAmbient (Q : Subgroup (SuzukiMatrixGroup m)))
    rw [suzukiSylow_omega_eq_center hm (MulEquiv.refl _) Q]
    exact mem_map_of_mem (Q : Subgroup (SuzukiMatrixGroup m)).subtype hx
  rintro _ ⟨b,hb,rfl⟩
  by_cases hb1 : (b:SuzukiMatrixGroup m)=1
  · change (b:SuzukiMatrixGroup m) ∈ _
    rw [hb1]; exact one_mem _
  obtain ⟨g,hg⟩ := isConj_iff.mp (suzuki_involutions_isConj m hm (f r) b
    (orderOf_eq_prime (hsq (q r) hrZ) hr1) (orderOf_eq_prime (hsq b hb) hb1))
  have hgN : g ∈ normalizer (Q : Set (SuzukiMatrixGroup m)) :=
    suzuki_center_conjugator_normalizes hm (MulEquiv.refl _) Q (q r) b hrZ hb hr1 hb1 g hg
  change g ∈ normalizer (((P : Subgroup E).map f) : Set (SuzukiMatrixGroup m)) at hgN
  rw [← P.normalizer_map_surjective f hf] at hgN
  obtain ⟨a,ha,rfl⟩ := hgN
  have haZ : a*(r:E)*a⁻¹ ∈ (center P).map (P : Subgroup E).subtype := by
    let hauto := (P : Subgroup E).normalizerMonoidHom ⟨a,ha⟩
    exact ⟨hauto r,(centerCongr hauto ⟨r,hr⟩).property,rfl⟩
  refine ⟨_,haZ,?_⟩
  change f (a*(r:E)*a⁻¹) = (b:SuzukiMatrixGroup m)
  simpa only [map_mul,map_inv] using hg


private noncomputable def centerQuotientEquiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) : (X ⧸ center X) ≃* (Y ⧸ center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem eight_sylow_geometry (Q : Sylow 2 (SuzukiMatrixGroup 1)) :
    _root_.commutator Q = center Q ∧ Nat.card (center Q) = 8 ∧
      IsElementaryAbelian 2 (Q ⧸ center Q) ∧ Nat.card (Q ⧸ center Q) = 8 := by
  obtain ⟨f,hf,_⟩ := suzukiSylow_aligned_equiv (by decide) (MulEquiv.refl _) Q
  let e : SuzukiRootSubgroup 1 ≃* Q :=
    ((SuzukiRootSubgroup 1).equivMapOfInjective f.toMonoidHom f.injective).trans
      (MulEquiv.subgroupCongr hf)
  have hm : (center (SuzukiRootSubgroup 1)).map e.toMonoidHom = center Q := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩
  refine ⟨?_,(suzukiSylow_borel_structure (by decide) (MulEquiv.refl _) Q).1,?_,?_⟩
  · rw [←hm,←SchurCover.Family.root_commutator_eq_center 1 (by decide),
      map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  · let := MultiplierFieldAction.root_quotient_center_elementary
    exact IsElementaryAbelian.of_surjective (centerQuotientEquiv e).toMonoidHom
      (centerQuotientEquiv e).surjective
  · exact (Nat.card_congr (centerQuotientEquiv e).toEquiv).symm.trans
      MultiplierFieldAction.root_quotient_center_card

variable [Group.IsPerfect E]

/-- Nontrivial perfect central covers of Sz(8) have no extra Sylow-center elements. -/
theorem suzuki_eight_cover_sylow_center
    (f : E →* SuzukiMatrixGroup 1) (hf : Function.Surjective f)
    (hc : f.ker = center E) (hk : IsPGroup 2 f.ker) (hne : f.ker ≠ ⊥)
    (P : Sylow 2 E) : (center P).map (P : Subgroup E).subtype = center E := by
  let Q := P.mapSurjective hf
  let q : P →* Q := (f.comp (P : Subgroup E).subtype).codRestrict Q
    (fun x => mem_map_of_mem f x.property)
  have hq : Function.Surjective q := by
    rintro ⟨_,⟨x,hx,rfl⟩⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hker : q.ker = f.ker.subgroupOf (P : Subgroup E) := by
    ext x
    change (⟨f x,_⟩:Q)=1 ↔ f x=1
    exact Subtype.ext_iff
  have hkerC : q.ker ≤ center P := by
    intro x hx
    have hxE : (x:E) ∈ center E := hc ▸ (show x ∈ f.ker.subgroupOf (P : Subgroup E) from hker ▸ hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hxE y)
  have hkerD : q.ker ≤ _root_.commutator P := by
    intro x hx
    have ht := center_inf_commutator_inf_sylow_le_commutator P
      ⟨⟨hc ▸ (show x ∈ f.ker.subgroupOf (P : Subgroup E) from hker ▸ hx),Group.IsPerfect.mem_commutator⟩,x.property⟩
    rw [←map_subtype_commutator] at ht
    obtain ⟨y,hy,he⟩ := ht
    exact (Subtype.ext he : y=x) ▸ hy
  apply le_antisymm ?_ ?_
  · rintro _ ⟨r,hr,rfl⟩
    rw [←hc]
    by_contra hr1
    have hall := suzuki_cover_sylow_center_image (by decide) f hf P r hr hr1
    have hZmap : center Q ≤ (center P).map q := by
      intro b hb
      have hh := hall (mem_map_of_mem (Q : Subgroup (SuzukiMatrixGroup 1)).subtype hb)
      obtain ⟨_,⟨a,ha,rfl⟩,he⟩ := hh
      exact ⟨a,ha,Subtype.ext he⟩
    have hDmap : (_root_.commutator P).map q = center Q := by
      rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hq]
      exact (eight_sylow_geometry Q).1
    have hDC : _root_.commutator P ≤ center P := by
      have hd := (map_le_iff_le_comap.mp (hDmap.le.trans hZmap))
      rwa [comap_map_eq_self hkerC] at hd
    let t := (QuotientGroup.mk' (center Q)).comp q
    have ht : Function.Surjective t := (QuotientGroup.mk'_surjective _).comp hq
    have htker : t.ker = _root_.commutator P := by
      rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk',←hDmap,comap_map_eq_self hkerD]
    let et : (P ⧸ _root_.commutator P) ≃* (Q ⧸ center Q) :=
      (QuotientGroup.quotientMulEquivOfEq htker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective t ht)
    let := (eight_sylow_geometry Q).2.2.1
    let : IsElementaryAbelian 2 (P ⧸ _root_.commutator P) :=
      IsElementaryAbelian.of_surjective et.symm.toMonoidHom et.symm.surjective
    have h8 : Nat.card (P ⧸ _root_.commutator P)=8 :=
      (Nat.card_congr et.toEquiv).trans (eight_sylow_geometry Q).2.2.2
    have hbound := card_commutator_le_eight_of_central_elementary_eight_quotient
      (_root_.commutator P) hDC h8
    have hcard := (q.ker.subgroupOf (_root_.commutator P)).card_mul_index
    change Nat.card (q.ker.subgroupOf (_root_.commutator P)) *
      q.ker.relIndex (_root_.commutator P) = Nat.card (_root_.commutator P) at hcard
    rw [Nat.card_congr (subgroupOfEquivOfLe hkerD).toEquiv,relIndex_ker,hDmap,
      (eight_sylow_geometry Q).2.1] at hcard
    have hck : Nat.card q.ker = Nat.card f.ker := by
      rw [hker,Nat.card_congr (subgroupOfEquivOfLe (hk.le_sylow_of_normal P)).toEquiv]
    rw [hck] at hcard
    have hone : Nat.card f.ker=1 := by have := Nat.card_pos (α:=f.ker); omega
    exact hne (Subgroup.card_eq_one.mp hone)
  · intro z hz
    have hzP : z∈P := hk.le_sylow_of_normal P (hc.symm ▸ hz)
    exact ⟨⟨z,hzP⟩,mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hz y)),rfl⟩


/-- A nontrivial central cover has no nontrivial involutory pointwise Sylow fixer. -/
theorem suzuki_eight_cover_sylow_fixer
    (e : (E ⧸ center E) ≃* SuzukiMatrixGroup 1) (hZ : IsPGroup 2 (center E))
    (hne : center E ≠ ⊥) (P : Sylow 2 E) (α : MulAut E) (hα : α^2=1)
    (hfix : ∀ x ∈ P, α x=x) : α=1 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker=center E := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let Q := P.mapSurjective hf
  have hi : ∃ y, MulAut.centralQuotientAction e α = MulAut.conj y := by
    obtain ⟨y,_,hy⟩ := suzuki_aut_fixing_sylow_inner (by decide) (MulEquiv.refl _) Q
      (MulAut.centralQuotientAction e α) (by
        rintro _ ⟨x,hx,rfl⟩
        change MulAut.centralQuotientAction e α (e (QuotientGroup.mk' (center E) x)) = _
        rw [MulAut.centralQuotientAction_apply,hfix x hx]
        rfl)
    exact ⟨y,hy⟩
  obtain ⟨x,hx⟩ := (MulAut.centralQuotientAction_inner_iff e α).mp hi
  obtain ⟨a,ha,haα⟩ := MulAut.exists_center_sylow_conjugator_of_inner_involution
    P α hα ⟨x,hx.symm⟩ hfix hZ
  have haZ : (a:E) ∈ center E :=
    suzuki_eight_cover_sylow_center f hf hk (hk.symm ▸ hZ) (hk.symm ▸ hne) P ▸
      mem_map_of_mem (P : Subgroup E).subtype ha
  rw [←haα]
  apply MulEquiv.ext
  intro y
  change (a:E)*y*(a:E)⁻¹=y
  rw [←mem_center_iff.mp haZ y,mul_inv_cancel_right]

end BenderSuzuki.MatrixGroups
