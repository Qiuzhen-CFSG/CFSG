module
public import Theory.GroupTheory.ElementaryCentralIndexBound
public import Theory.ElementaryAbelian.Join
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterAlignmentSource
/-!
# The fixed-group count forces the small field

After aligning the two literal fixed centers, transport the outside fixed
group into C_T(s). Its involutions lie in that center. The elementary
fixed plane together with s then has order at most four times the center.
The exact source orders force n=2. The two remaining kernel premises are
the actual field-complement action and its fixed-center kernel; their
source producers are connected in the terminal assembly.

Source: Aschbacher–Smith, the final single linear block argument, p.539.
-/
public section
open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource Stellmacher
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_centerless_conjugacy_forces_small_field_of_kernels
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G)∈(d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2) (hsR : (s:G)∉elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (i : G) (hiT : i∈T) (hiS : i∉(d.S : Subgroup d.H).map d.H.subtype) (hi2 : i^2=1)
    (hiZ : i∉centralizer (distinguishedZ d:Set G))
    (g : G) (hgi : (MulAut.conj g) i=(s:G))
    (hIT : (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)⊓centralizer ({i}:Set G)).map
      (MulAut.conj g).toMonoidHom≤(T:Subgroup G)⊓centralizer ({(s:G)}:Set G))
    (hkernel :
      let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      let Zs := (R⊓centralizer (R:Set G))⊓centralizer ({(s:G)}:Set G)
      let Rs := R⊓centralizer ({(s:G)}:Set G)
      ∀E∈elementaryAbelianMaxSubgroups Rs,∀a∈(T:Subgroup G)⊓centralizer ({(s:G)}:Set G),
        a∈normalizer (E:Set G)→(∀u∈E,a*u*a⁻¹*u⁻¹∈Zs)→a∈Rs⊔zpowers (s:G))
    (hindex :
      let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      let Zs := (R⊓centralizer (R:Set G))⊓centralizer ({(s:G)}:Set G)
      let Rs := R⊓centralizer ({(s:G)}:Set G)
      (Rs⊔zpowers (s:G)).relIndex
        (((T:Subgroup G)⊓centralizer ({(s:G)}:Set G))⊓centralizer (Zs:Set G))≤2) : n=2 := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let Z := R⊓centralizer (R:Set G)
  let Cs := centralizer ({(s:G)}:Set G)
  let Rs := R⊓Cs
  let Zs := Z⊓Cs
  let P := ((T:Subgroup G)⊓Cs)⊓centralizer (Zs:Set G)
  let e := MulAut.conj g
  let I₀ := R⊓centralizer ({i}:Set G)
  let J₀ := Z⊓centralizer ({i}:Set G)
  let I := I₀.map e.toMonoidHom
  let J := J₀.map e.toMonoidHom
  have hZdef : distinguishedZ d=Z := distinguishedZ_of_centerless d hZ
  have halign : J=Zs := by
    have hh := source_centerless_fixed_center_alignment_of_quotient_kernel d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR i hiT hiS hi2 hiZ g hgi hIT hkernel
    simpa only [hZdef] using hh
  have hRT : R≤(T:Subgroup G) := (sSup_le fun _ h=>h.1).trans hST.le
  have hclosed := c.centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hu hZ
  have hsord : orderOf (s:G)=2 := (orderOf_coe s).trans hs2
  have hspow : (s:G)^2=1 := by simpa only [hsord] using pow_orderOf_eq_one (s:G)
  have hsI : (s:G)∉I := by
    rintro ⟨a,ha,he⟩
    have ha2 : orderOf a=2 := (e.orderOf_eq a).symm.trans (he ▸ hsord)
    exact hsR (hclosed ⟨a,hRT ha.1⟩ s ((orderOf_coe _).symm.trans ha2) ha.1
      (isConj_iff.mpr ⟨g,he⟩))
  have hIJ : I≤centralizer (J:Set G) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨j,hj,rfl⟩
    change e j * e a=e a * e j
    simpa only [map_mul] using congrArg e (hj.1.2 a ha.1).symm
  have hIP : I≤P := le_inf hIT (halign ▸ hIJ)
  have hZsI : Zs≤I := halign ▸ map_mono (show J₀≤I₀ from inf_le_inf_right _ inf_le_left)
  have hInv : ∀ r : G, r ∈ I → r ^ 2 = 1 → r ∈ Zs := by
    rintro _ ⟨a,ha,rfl⟩ ha2
    rw [←halign]
    apply mem_map_of_mem e.toMonoidHom
    refine ⟨?_,ha.2⟩
    exact source_outside_fixed_involution_mem_center d hG T hST hsingle hL hM hTM hu i hiT hiS a ha.1
      (e.injective (by change e a ^ 2=1 at ha2; simpa only [map_pow,map_one] using ha2))
      (mem_centralizer_singleton_iff.mp ha.2).symm
  obtain ⟨m,hm,hn,hZsc,hRsc⟩ := source_centerless_field_fixed_orders d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR
  obtain ⟨k,_,hk,_,hIc,_,_⟩ := source_centerless_outside_noncentral_fixed_data d hG T hST hsingle hL hM hTM hu c hZ i hiT hiS hi2 (by simpa only [hZdef] using hiZ)
  have hkm : k=m := by omega
  have hcardI : Nat.card I=Nat.card Rs := by
    rw [card_map_of_injective e.injective,hIc,hRsc,hkm]
  have hsCI : (s:G)∈centralizer (I:Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hIT ha).2
  have hRsP : Rs≤P := by
    intro a ha
    refine ⟨⟨hRT ha.1,ha.2⟩,?_⟩
    intro z hz
    exact (hz.1.2 a ha.1).symm
  have hsP : (s:G)∈P := by
    refine ⟨⟨s.property,mem_centralizer_singleton_iff.mpr (Commute.refl _)⟩,?_⟩
    intro z hz
    exact mem_centralizer_singleton_iff.mp hz.2
  have hsCRs : (s:G)∈centralizer (Rs:Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mp ha.2
  have hcK : Nat.card (I⊔zpowers (s:G) : Subgroup G)=Nat.card (Rs⊔zpowers (s:G) : Subgroup G) := by
    rw [card_sup_zpowers_of_normalizing_involution I s hspow hsI
      (Subgroup.centralizer_le_normalizer _ hsCI),
      card_sup_zpowers_of_normalizing_involution Rs s hspow (fun h=>hsR h.1)
      (Subgroup.centralizer_le_normalizer _ hsCRs),hcardI]
  have hIx : (I⊔zpowers (s:G)).relIndex P≤2 := by
    have h1 := relIndex_mul_relIndex (⊥:Subgroup G) (I⊔zpowers (s:G)) P bot_le
      (sup_le hIP (zpowers_le.mpr hsP))
    have h2 := relIndex_mul_relIndex (⊥:Subgroup G) (Rs⊔zpowers (s:G)) P bot_le
      (sup_le hRsP (zpowers_le.mpr hsP))
    simp only [relIndex_bot_left] at h1 h2
    rw [hcK] at h1
    have he := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=(Rs⊔zpowers (s:G) : Subgroup G))) (h1.trans h2.symm)
    exact he ▸ hindex
  let U := sourceModule L
  let Us := U⊓Cs
  let E := Us⊔zpowers (s:G)
  obtain ⟨_,x,hx,hxS⟩ := source_field_centralizer_supplement d hG T hST hsingle hL hM hTM hu c s hs hs2 hsR
  have hfamily : elementaryAbelianMaxSubgroups Rs={Us,Us.map (MulAut.conj x⁻¹).toMonoidHom} := source_field_fixed_maximum_pair d hG T hST hsingle hL hM hTM hu s x hx.1 hxS hx.2
  have hUs : Us∈elementaryAbelianMaxSubgroups Rs := hfamily.symm ▸ Set.mem_insert _ _
  let : IsElementaryAbelian 2 Us := hUs.2.1
  let : IsElementaryAbelian 2 (zpowers (s:G)) := IsElementaryAbelian.zpowers_of_pow_eq_one hspow
  have hsCUs : (s:G)∈centralizer (Us:Set G) := centralizer_le hUs.1 hsCRs
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hsCUs)
  have hcE : Nat.card E=2*(2^n) := by
    rw [card_sup_zpowers_of_normalizing_involution Us s hspow (fun hh=>hsR (hUs.1 hh).1)
      (Subgroup.centralizer_le_normalizer _ hsCUs),source_centerless_field_plane_card d hG T hST hsingle hL hM hTM hu c hZ s hs hsord]
  have hb := elementary_card_le_of_central_involution_index_two P I Zs E
    (sup_le (hUs.1.trans hRsP) (zpowers_le.mpr hsP)) hZsI s hspow hsI hsCI hInv hIx
  rw [hcE,hZsc] at hb
  have hp : 2^(n+1)≤2^(m+2) := by simpa only [pow_add,pow_one,show (2:ℕ)^2=4 from rfl,Nat.mul_comm] using hb
  have hnm := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hp
  omega
end CFSG.Quasithin.Chapter2.LinearShadows.Single
