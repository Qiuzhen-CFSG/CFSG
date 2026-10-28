module
public import Theory.SpecificGroups.OrthogonalFourBinary.OmegaEightPlaneGeometry
public import Theory.GroupTheory.ElementaryKernelInvolutionNormalizer
public import Theory.GroupTheory.ElementaryEightPlaneImageTransport
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Actual plane images above the natural binary Omega action

Let a finite group map onto the genuine binary Omega group with elementary
kernel of order16 and the natural conjugation action. Two distinct elementary
eights, normalized and self-centralizing in a common subgroup containing the
kernel, give distinct involution images. At least one is an axis involution,
and its elementary eight has an actual plane-stabilizer image of order24.

Kernel normalization puts an outside involution's displacement, of order4,
inside the elementary eight. This forces its quotient image to have order2.
The elementary-kernel coset argument proves distinctness and makes the two
images commute. The finite Omega geometry then selects an axis. Its quotient
centralizer has order12, so the full normalizer has order192. The order2
pointwise fixed-plane kernel bounds the elementary eight's centralizer by8,
which gives the faithful plane image. The final theorem retains the literal
image under any injective ambient inclusion.

Coordinates need only be an equivariant bijection with the natural space;
the proof performs its displacement algebra inside the actual group kernel.
This discharges the plane-actor premise in Aschbacher--Smith 15.1.11,
printed p.1089. The source consumer supplies the original marked pair and
its faithful residual quotient.
-/

open Subgroup
open OrthogonalFourBinary
namespace OrthogonalFourBinary.SylowGeometry
private theorem card_map_mul_inf_ker {G W : Type*} [Group G] [Finite G]
    [Group W] [Finite W] (f : G →* W) (U : Subgroup G) :
    Nat.card (U.map f) * Nat.card (f.ker ⊓ U : Subgroup G) = Nat.card U := by
  let r := f.comp U.subtype
  have hk : r.ker = f.ker.subgroupOf U := rfl
  have hr : r.range = U.map f := by rw [MonoidHom.range_comp,range_subtype]
  have hc : Nat.card r.ker = Nat.card (f.ker ⊓ U : Subgroup G) := by
    rw [hk, ← card_map_of_injective U.subtype_injective, subgroupOf_map_subtype]
  have h := r.ker.index_mul_card
  rwa [index_ker, hr, hc] at h

private theorem fixed_iff_mem
    {G : Type*} [Group G] [Finite G]
    (f : G →* omega) (e : f.ker ≃ Space)
    (hact : ∀ (g:G) (a:f.ker), e (MulAut.conjNormal g a)=f g • e a)
    (U : Subgroup G) (hU : IsElementaryAbelian 2 U)
    (hfixed : f.ker ⊓ centralizer (U:Set G)=f.ker ⊓ U)
    (z:omega) (himage:U.map f=zpowers z) (a:f.ker) :
    z • e a=e a ↔ (a:G)∈U := by
  let := hU
  constructor
  · intro ha
    have hz : zpowers z ≤ MulAction.stabilizer omega (e a) := zpowers_le.mpr ha
    have hac : (a:G)∈centralizer (U:Set G) := by
      intro u hu
      have hu' := hz (himage ▸ mem_map_of_mem f hu)
      have he : MulAut.conjNormal u a=a := e.injective ((hact u a).trans hu')
      have hc := congrArg Subtype.val he
      change u*(a:G)*u⁻¹=(a:G) at hc
      exact mul_inv_eq_iff_eq_mul.mp hc
    exact (hfixed ▸ (show (a:G)∈f.ker⊓centralizer (U:Set G) from ⟨a.property,hac⟩)).2
  · intro ha
    obtain ⟨u,hu,huz⟩ := (himage.symm ▸ mem_zpowers z : z∈U.map f)
    have he : MulAut.conjNormal u a=a := by
      apply Subtype.ext
      change u*(a:G)*u⁻¹=(a:G)
      rw [setLike_mul_comm hu ha,mul_inv_cancel_right]
    rw [←huz,←hact,he]

/-- An axis image lifts to the actual order-24 plane stabilizer on the eight.
The proof derives the full normalizer as the centralizer preimage, its order192,
and self-centralization of the elementary eight. -/
public theorem omega_elementaryEight_plane_image_of_axis
    {G : Type*} [Group G] [Finite G]
    (f : G →* omega) (hfsur : Function.Surjective f)
    (e : f.ker ≃ Space)
    (hact : ∀ (g:G) (a:f.ker), e (MulAut.conjNormal g a)=f g • e a)
    (hA : IsElementaryAbelian 2 f.ker) (hAcard:Nat.card f.ker=16)
    (U : Subgroup G) (hU : IsElementaryAbelian 2 U) (hUcard:Nat.card U=8)
    (hfixed : f.ker ⊓ centralizer (U:Set G)=f.ker ⊓ U)
    (z:omega) (hz:orderOf z=2) (himage:U.map f=zpowers z)
    (hgeometry:OmegaEightPlaneGeometry z) :
    Nonempty (ElementaryEightPlaneImage U) := by
  classical
  let := hA
  let := hU
  let A := f.ker
  let N := normalizer (U:Set G)
  let C := centralizer (U:Set G)
  have hNC : N=(centralizer ({z}:Set omega)).comap f :=
    normalizer_eq_comap_centralizer_of_elementary_kernel f U hA hU hfixed z hz himage
  have hAN : A≤N := by
    intro a ha
    rw [hNC]
    change f a∈centralizer ({z}:Set omega)
    rw [MonoidHom.mem_ker.mp ha]
    exact one_mem _
  have hNmap : N.map f=centralizer ({z}:Set omega) := by
    rw [hNC]
    exact map_comap_eq_self (by rw [f.range_eq_top_of_surjective hfsur]; exact le_top)
  have hNcard : Nat.card N=192 := by
    have h := card_map_mul_inf_ker f N
    rw [hNmap,inf_eq_left.mpr hAN,hAcard,hgeometry.1] at h
    exact h.symm
  have hIcard : Nat.card (A⊓U:Subgroup G)=4 := by
    have h := card_map_mul_inf_ker f U
    rw [himage,Nat.card_zpowers,hz,hUcard] at h
    change 2 * Nat.card (A⊓U:Subgroup G)=8 at h
    omega
  have hCmap : C.map f≤omegaFixedPlaneKernel z := by
    rintro _ ⟨c,hc,rfl⟩ v hv
    let a := e.symm v
    have ha : (a:G)∈U := (fixed_iff_mem f e hact U hU hfixed z himage a).mp (by
      simpa only [a,e.apply_symm_apply] using hv)
    have he : MulAut.conjNormal c a=a := by
      apply Subtype.ext
      change c*(a:G)*c⁻¹=(a:G)
      rw [←mem_centralizer_iff.mp hc a ha,mul_inv_cancel_right]
    have hh := (hact c a).symm.trans (congrArg e he)
    simpa only [a,e.apply_symm_apply] using hh
  have hCcard : Nat.card C≤8 := by
    have hle := Nat.card_le_card_of_injective (Subgroup.inclusion hCmap) (Subgroup.inclusion_injective hCmap)
    rw [hgeometry.2] at hle
    have h := card_map_mul_inf_ker f C
    rw [hfixed,hIcard] at h
    omega
  have hUC : U≤C := by
    intro u hu v hv
    exact setLike_mul_comm hv hu
  have hCE : C=U := (eq_of_le_of_card_ge hUC (by simpa only [hUcard] using hCcard)).symm
  let W := A.subgroupOf U
  have hWcard : Nat.card W=4 := by
    rw [←card_map_of_injective U.subtype_injective,subgroupOf_map_subtype]
    exact hIcard
  refine elementaryEight_plane_image_of_normalizing_subgroup U N hUcard hNcard le_rfl
    ?_ W hWcard ?_
  · change N⊓C=U
    rw [hCE,inf_eq_right.mpr U.le_normalizer]
  · intro n u
    change (n:G)*(u:G)*(n:G)⁻¹∈A ↔ (u:G)∈A
    have hn : (n:G)∈normalizer (A:Set G) := by rw [normalizer_eq_top]; trivial
    exact (mem_normalizer_iff.mp hn (u:G)).symm

/-- An elementary eight normalized by the elementary kernel has involution
image, provided it is not contained in that kernel. The displacement of any
outside involution has order4 and lies in the kernel intersection. -/
public theorem omega_elementaryEight_involution_image
    {G : Type*} [Group G] [Finite G]
    (f : G →* omega) (e : f.ker ≃ Space)
    (hact : ∀ (g:G) (a:f.ker), e (MulAut.conjNormal g a)=f g • e a)
    (hA : IsElementaryAbelian 2 f.ker) (hAcard:Nat.card f.ker=16)
    (U : Subgroup G) (hU : IsElementaryAbelian 2 U) (hUcard:Nat.card U=8)
    (hAN : f.ker≤normalizer (U:Set G)) (hout:¬U≤f.ker) :
    ∃z:omega, orderOf z=2 ∧ U.map f=zpowers z := by
  classical
  let := hA
  let := hU
  let A := f.ker
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨u,hu,huA⟩ := SetLike.not_le_iff_exists.mp hout
  let z := f u
  have hz : z≠1 := fun h => huA (MonoidHom.mem_ker.mpr h)
  have hu2 : u^2=1 := elemPow_eq_one_of_isElementaryAbelian u hu
  have hz2 : z^2=1 := by rw [←map_pow,hu2,map_one]
  have hzord : orderOf z=2 := orderOf_eq_prime hz2 hz
  let d : A →* A := (MulAut.conjNormal u).toMonoidHom / MonoidHom.id A
  have hd (a:A) : d a=1 ↔ z • e a=e a := by
    change MulAut.conjNormal u a / a=1 ↔ _
    rw [div_eq_one]
    exact ⟨fun h => (hact u a).symm.trans (congrArg e h),
      fun h => e.injective ((hact u a).trans h)⟩
  let ek : d.ker ≃ {v:Space // z • v=v} := e.subtypeEquiv (fun a => hd a)
  have hdk : Nat.card d.ker=4 := (Nat.card_congr ek).trans
    (omega_involution_fixed_card z hz hz2)
  have hdr : Nat.card d.range=4 := by
    have h := d.ker.index_mul_card
    rw [index_ker,hdk,hAcard] at h
    omega
  have hDle : d.range≤U.subgroupOf A := by
    rintro _ ⟨a,rfl⟩
    change ((MulAut.conjNormal u a / a : A):G)∈U
    simp only [div_eq_mul_inv]
    change u*(a:G)*u⁻¹*(a:G)⁻¹∈U
    have hconj := (mem_normalizer_iff.mp (hAN a.property) u⁻¹).mp (U.inv_mem hu)
    have hm := U.mul_mem hu hconj
    simpa only [mul_assoc] using hm
  have hIlower : 4≤Nat.card (A⊓U:Subgroup G) := by
    have h := card_le_of_le hDle
    rw [hdr,←card_map_of_injective A.subtype_injective,subgroupOf_map_subtype,inf_comm U A] at h
    exact h
  have hzle : zpowers z≤U.map f := zpowers_le.mpr (mem_map_of_mem f hu)
  have hImlower : 2≤Nat.card (U.map f) := by
    have h := card_le_of_le hzle
    rw [Nat.card_zpowers,hzord] at h
    exact h
  have hcount := card_map_mul_inf_ker f U
  rw [hUcard] at hcount
  change Nat.card (U.map f) * Nat.card (A⊓U:Subgroup G)=8 at hcount
  have hIm : Nat.card (U.map f)=2 := by nlinarith
  refine ⟨z,hzord,?_⟩
  exact (eq_of_le_of_card_ge hzle (by rw [hIm,Nat.card_zpowers,hzord])).symm

private theorem image_eq_implies_eq
    {G : Type*} [Group G] [Finite G]
    (f : G →* omega) (e : f.ker ≃ Space)
    (hact : ∀ (g:G) (a:f.ker), e (MulAut.conjNormal g a)=f g • e a)
    (hA : IsElementaryAbelian 2 f.ker)
    (U V : Subgroup G) (hU:IsElementaryAbelian 2 U) (hV:IsElementaryAbelian 2 V)
    (hUcard:Nat.card U=8) (hVcard:Nat.card V=8)
    (hfixedU:f.ker⊓centralizer (U:Set G)=f.ker⊓U)
    (hfixedV:f.ker⊓centralizer (V:Set G)=f.ker⊓V)
    (z:omega) (hz:orderOf z=2)
    (himageU:U.map f=zpowers z) (himageV:V.map f=zpowers z) : U=V := by
  classical
  let := hA
  let := hU
  let := hV
  obtain ⟨u,hu,huf⟩ := (himageU.symm ▸ mem_zpowers z : z∈U.map f)
  have hu2:u^2=1 := elemPow_eq_one_of_isElementaryAbelian u hu
  have hle:V≤U := by
    intro x hx
    have hx2:x^2=1 := elemPow_eq_one_of_isElementaryAbelian x hx
    have hfx:f x=1 ∨ f x=z := by
      have hm := himageV ▸ mem_map_of_mem f hx
      rw [mem_zpowers_iff_mem_range_orderOf,hz] at hm
      obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
      have hnlt:n<2 := Finset.mem_range.mp hn
      interval_cases n <;> simp_all
    rcases hfx with hfx|hfx
    · let a:f.ker := ⟨x,MonoidHom.mem_ker.mpr hfx⟩
      exact (fixed_iff_mem f e hact U hU hfixedU z himageU a).mp
        ((fixed_iff_mem f e hact V hV hfixedV z himageV a).mpr hx)
    · let a:f.ker := ⟨x*u⁻¹,by simp only [MonoidHom.mem_ker,map_mul,map_inv,hfx,huf,mul_inv_cancel]⟩
      have ha2:(a:G)^2=1 := elemPow_eq_one_of_isElementaryAbelian _ a.property
      have hai:(a:G)⁻¹=a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha2)
      have hui:u⁻¹=u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu2)
      have hxi:x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx2)
      have hcomm:(a:G)*u=u*a := by
        calc
          (a:G)*u=x := by simp [a]
          _=x⁻¹ := hxi.symm
          _=u*a := by rw [show x=(a:G)*u by simp [a],mul_inv_rev,hai,hui]
      have he:MulAut.conjNormal u a=a := by
        apply Subtype.ext
        change u*(a:G)*u⁻¹=a
        rw [←hcomm,mul_inv_cancel_right]
      have haU:(a:G)∈U := (fixed_iff_mem f e hact U hU hfixedU z himageU a).mp (by
        rw [←huf,←hact,he])
      have hh := U.mul_mem haU hu
      simpa only [a,inv_mul_cancel_right] using hh
  exact (eq_of_le_of_card_ge hle (by rw [hUcard,hVcard])).symm

private theorem fixed_and_outside
    {G : Type*} [Group G] [Finite G] (A S U:Subgroup G)
    (hA:IsElementaryAbelian 2 A) (hAcard:Nat.card A=16)
    (hUcard:Nat.card U=8) (hAS:A≤S)
    (hcentral:S⊓centralizer (U:Set G)=U) :
    A⊓centralizer (U:Set G)=A⊓U ∧ ¬U≤A := by
  let := hA
  constructor
  · calc
      A⊓centralizer (U:Set G)=(A⊓S)⊓centralizer (U:Set G) := by rw [inf_eq_left.mpr hAS]
      _=A⊓(S⊓centralizer (U:Set G)) := inf_assoc _ _ _
      _=A⊓U := congrArg (fun K => A⊓K) hcentral
  · intro hUA
    have hAU:A≤U := by
      intro a ha
      rw [←hcentral]
      exact ⟨hAS ha,fun u hu => setLike_mul_comm (hUA hu) ha⟩
    have h:=card_le_of_le hAU
    rw [hAcard,hUcard] at h
    omega

/-- Of two distinct self-centralizing elementary eights normalized by the same
subgroup containing the elementary kernel, at least one has a plane image. -/
public theorem omega_two_elementaryEights_plane_image
    {G : Type*} [Group G] [Finite G]
    (f : G →* omega) (hfsur : Function.Surjective f)
    (e : f.ker ≃ Space)
    (hact : ∀ (g:G) (a:f.ker), e (MulAut.conjNormal g a)=f g • e a)
    (hA : IsElementaryAbelian 2 f.ker) (hAcard:Nat.card f.ker=16)
    (S U V : Subgroup G)
    (hU : IsElementaryAbelian 2 U) (hUcard:Nat.card U=8)
    (hV : IsElementaryAbelian 2 V) (hVcard:Nat.card V=8)
    (hAS:f.ker≤S) (hUN:S≤normalizer (U:Set G)) (hVN:S≤normalizer (V:Set G))
    (hcentralU:S⊓centralizer (U:Set G)=U)
    (hcentralV:S⊓centralizer (V:Set G)=V)
    (hne:U≠V) :
    Nonempty (ElementaryEightPlaneImage U) ∨ Nonempty (ElementaryEightPlaneImage V) := by
  obtain ⟨hfixedU,houtU⟩ := fixed_and_outside f.ker S U hA hAcard hUcard hAS hcentralU
  obtain ⟨hfixedV,houtV⟩ := fixed_and_outside f.ker S V hA hAcard hVcard hAS hcentralV
  obtain ⟨z,hz,hUz⟩ := omega_elementaryEight_involution_image f e hact hA hAcard U hU hUcard (hAS.trans hUN) houtU
  obtain ⟨w,hw,hVw⟩ := omega_elementaryEight_involution_image f e hact hA hAcard V hV hVcard (hAS.trans hVN) houtV
  have hzw:z≠w := by
    intro he
    apply hne
    exact image_eq_implies_eq f e hact hA U V hU hV hUcard hVcard
      hfixedU hfixedV z hz hUz (he.symm ▸ hVw)
  have hc:Commute z w := by
    obtain ⟨v,hv,rfl⟩ := (hVw.symm ▸ mem_zpowers w : w∈V.map f)
    have hVS:V≤S := hcentralV ▸ inf_le_left
    have hn := hUN (hVS hv)
    rw [normalizer_eq_comap_centralizer_of_elementary_kernel f U hA hU hfixedU z hz hUz] at hn
    exact (mem_centralizer_singleton_iff.mp hn).symm
  have hzne:z≠1 := by intro h; simp [h] at hz
  have hwne:w≠1 := by intro h; simp [h] at hw
  rcases omega_commuting_involutions_plane_geometry z w hzne hwne
    (by simpa only [hz] using pow_orderOf_eq_one z) (by simpa only [hw] using pow_orderOf_eq_one w) hzw hc with h|h
  · exact Or.inl (omega_elementaryEight_plane_image_of_axis f hfsur e hact hA hAcard U hU hUcard hfixedU z hz hUz h)
  · exact Or.inr (omega_elementaryEight_plane_image_of_axis f hfsur e hact hA hAcard V hV hVcard hfixedV w hw hVw h)

/-- The selected plane image survives the literal injective ambient inclusion. -/
public theorem omega_two_elementaryEights_plane_image_map
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* omega) (hfsur : Function.Surjective f)
    (e : f.ker ≃ Space)
    (hact : ∀ (g:G) (a:f.ker), e (MulAut.conjNormal g a)=f g • e a)
    (hA : IsElementaryAbelian 2 f.ker) (hAcard:Nat.card f.ker=16)
    (S U V : Subgroup G)
    (hU : IsElementaryAbelian 2 U) (hUcard:Nat.card U=8)
    (hV : IsElementaryAbelian 2 V) (hVcard:Nat.card V=8)
    (hAS:f.ker≤S) (hUN:S≤normalizer (U:Set G)) (hVN:S≤normalizer (V:Set G))
    (hcentralU:S⊓centralizer (U:Set G)=U)
    (hcentralV:S⊓centralizer (V:Set G)=V)
    (hne:U≠V) (i:G→*H) (hi:Function.Injective i) :
    Nonempty (ElementaryEightPlaneImage (U.map i)) ∨
      Nonempty (ElementaryEightPlaneImage (V.map i)) := by
  rcases omega_two_elementaryEights_plane_image f hfsur e hact hA hAcard S U V hU hUcard hV hVcard
    hAS hUN hVN hcentralU hcentralV hne with h|h
  · exact Or.inl (h.map (fun d => d.map i hi))
  · exact Or.inr (h.map (fun d => d.map i hi))
end OrthogonalFourBinary.SylowGeometry
