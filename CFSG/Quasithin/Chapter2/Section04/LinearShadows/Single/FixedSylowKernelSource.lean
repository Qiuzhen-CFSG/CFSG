module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterAlignmentSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterSplitSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FixedPlaneKernelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FixedCenterKernelSource

/-!
# The original fixed Sylow action kernels

The cyclic field complement splits the fixed subgroup of S as R_s F. Its
proved kernel on the fixed center identifies S ∩ C_T(s) ∩ C_G(Z_s) with
R_s⟨s⟩; since S has index two in T, the desired relative index is at most two.

For a maximum elementary subgroup E of R_s, a normalizing element of C_T(s)
lies in S: otherwise its exchange of the two fixed planes would put the whole
plane in the smaller fixed center. Splitting that element as r f removes the
inner commutator using [R,R] ≤ Z(R). The actual split involution commuting with
F transports the second plane to the first, so the proved field kernel gives
f ∈ ⟨s⟩. All subgroups and conjugation maps are the original source ones.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, printed p.539,
the fixed-center alignment and index bound in the single linear block case.
These two conclusions discharge the literal kernel inputs of CenterAlignmentSource
and CenterlessCountingSource without any extra action or model premise.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource Stellmacher
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem field_fixed_factorization
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {n : ℕ}
    (c : CyclicTorusSetup d T n) (s : G)
    (hs : s∈(d.S:Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (a : G) (ha : a∈(d.S:Subgroup d.H).map d.H.subtype ⊓ centralizer ({s}:Set G)) :
    ∃ r∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype) ⊓ centralizer ({s}:Set G),
      ∃ f∈(d.S:Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G), r*f=a := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let F := S⊓normalizer (c.hall:Set G)
  let C := centralizer ({s}:Set G)
  let : IsCyclic F := c.field_cyclic
  obtain ⟨⟨r,f⟩,he⟩ := c.split_sylow.2 (⟨a,ha.1⟩:S)
  have hf : ((f:S):G)∈F := f.property
  have hfC : ((f:S):G)∈C := mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm (⟨((f:S):G),hf⟩:F) ⟨s,hs⟩))
  have heG : ((r:S):G)*((f:S):G)=a := congrArg Subtype.val he
  refine ⟨r,⟨r.property,?_⟩,f,hf,heG⟩
  have hh := C.mul_mem ha.2 (C.inv_mem hfC)
  rw [←heG] at hh
  change ((r:S):G)∈C
  simpa only [mul_inv_cancel_right] using hh

/-- The fixed-center centralizer contains R_s⟨s⟩ with relative index at most two. -/
theorem source_centerless_fixed_center_index
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G)∈(d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2) (hsR : (s:G)∉elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Zs := (R⊓centralizer (R:Set G))⊓centralizer ({(s:G)}:Set G)
    let Rs := R⊓centralizer ({(s:G)}:Set G)
    (Rs⊔zpowers (s:G)).relIndex
      (((T:Subgroup G)⊓centralizer ({(s:G)}:Set G))⊓centralizer (Zs:Set G))≤2 := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let C := centralizer ({(s:G)}:Set G)
  let Z := R⊓centralizer (R:Set G)
  let Zs := Z⊓C
  let Rs := R⊓C
  let F := S⊓normalizer (c.hall:Set G)
  let P := ((T:Subgroup G)⊓C)⊓centralizer (Zs:Set G)
  let K := Rs⊔zpowers (s:G)
  have hRS : R≤S := sSup_le fun _ h=>h.1
  have hRT : R≤(T:Subgroup G) := hRS.trans hST.le
  have hsord : orderOf (s:G)=2 := (orderOf_coe s).trans hs2
  have hRZ : R≤centralizer (Zs:Set G) :=
    (le_centralizer_iff.mp (show Z≤centralizer (R:Set G) from inf_le_right)).trans
      (centralizer_le inf_le_left)
  have hKSP : K≤S⊓P := by
    apply sup_le
    · exact le_inf (inf_le_left.trans hRS)
        (le_inf (le_inf (inf_le_left.trans hRT) inf_le_right) (inf_le_left.trans hRZ))
    · apply zpowers_le.mpr
      refine ⟨hs.1,⟨s.property,mem_centralizer_singleton_iff.mpr rfl⟩,?_⟩
      intro z hz
      exact mem_centralizer_singleton_iff.mp hz.2
  have hSP : S⊓P=K := by
    apply le_antisymm _ hKSP
    intro a ha
    obtain ⟨r,hr,f,hf,he⟩ := field_fixed_factorization c (s:G) hs a ⟨ha.1,ha.2.1.2⟩
    have hfZ : f∈centralizer (Zs:Set G) := by
      have hh := (centralizer (Zs:Set G)).mul_mem
        ((centralizer (Zs:Set G)).inv_mem (hRZ hr.1)) ha.2.2
      rw [←he] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hsf : f∈zpowers (s:G) := by
      apply source_field_fixed_center_centralizer_le_zpowers d hG T hST hsingle hL
        hM hTM hu c s hs hsord hsR
      refine ⟨hf,?_⟩
      rw [distinguishedZ_of_centerless d hZ]
      exact hfZ
    rw [←he]
    exact mul_mem_sup hr hsf
  change K.relIndex P≤2
  rw [←hSP,inf_relIndex_right]
  have hL' := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hi : S.relIndex (T:Subgroup G)=2 := (d.lemma_2_4_8_1 hG T hST hsingle hL').1
  exact (relIndex_le_of_le_right (show P≤(T:Subgroup G) from inf_le_left.trans inf_le_left)
    (by rw [hi]; decide)).trans_eq hi


/-- An actual Sylow actor trivial on a fixed plane modulo its center lies in R_s⟨s⟩. -/
theorem source_centerless_fixed_plane_sylow_kernel
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G)∈(d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2) (hsR : (s:G)∉elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Zs := (R⊓centralizer (R:Set G))⊓centralizer ({(s:G)}:Set G)
    let Rs := R⊓centralizer ({(s:G)}:Set G)
    ∀E∈elementaryAbelianMaxSubgroups Rs,∀a∈(T:Subgroup G)⊓centralizer ({(s:G)}:Set G),
      a∈normalizer (E:Set G)→(∀u∈E,a*u*a⁻¹*u⁻¹∈Zs)→a∈Rs⊔zpowers (s:G) := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let U := sourceModule (d.block.map d.H.subtype)
  let C := centralizer ({(s:G)}:Set G)
  let Z := R⊓centralizer (R:Set G)
  let Zs := Z⊓C
  let Rs := R⊓C
  let Us := U⊓C
  let F := S⊓normalizer (c.hall:Set G)
  have hsord : orderOf (s:G)=2 := (orderOf_coe s).trans hs2
  obtain ⟨m,hm,hn,hZsc,_⟩ := source_centerless_field_fixed_orders
    d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR
  have hUsc : Nat.card Us=2^n := source_centerless_field_plane_card
    d hG T hST hsingle hL hM hTM hu c hZ s hs hsord
  have hnot : ¬Us≤Zs := by
    intro hh
    have hc := card_le_of_le hh
    rw [hUsc,hZsc] at hc
    have hnm := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hc
    omega
  have hder : ⁅R,R⁆≤Z := (source_thompson_root_geometry d hG T hST hsingle hL hM hTM hu).2.2.1
  have hRZs : R≤centralizer (Zs:Set G) :=
    (le_centralizer_iff.mp (show Z≤centralizer (R:Set G) from inf_le_right)).trans
      (centralizer_le inf_le_left)
  have hclosed := c.centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hu hZ
  obtain ⟨x,hx,hxS,_,hxfix,_,hxf,_⟩ := source_centerless_split_involution
    d hG T hST hsingle hL hM hTM hu c hZ hclosed
  have hxs : x∈C := mem_centralizer_singleton_iff.mpr (hxf s hs)
  let e := MulAut.conj x⁻¹
  let Vs := Us.map e.toMonoidHom
  have hxZ : x∈centralizer (Z:Set G) := by
    intro z hz
    have hz' : z∈R⊓centralizer ({x}:Set G) := hxfix.symm ▸ hz
    exact mem_centralizer_singleton_iff.mp hz'.2
  have heZ : Zs.map e.toMonoidHom=Zs := mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer (Zs:Set G)
      ((centralizer (Zs:Set G)).inv_mem (centralizer_le inf_le_left hxZ)))
  have hpair : elementaryAbelianMaxSubgroups Rs={Us,Vs} :=
    source_field_fixed_maximum_pair d hG T hST hsingle hL hM hTM hu s x hx.1 hxS hxs
  change ∀ E∈elementaryAbelianMaxSubgroups Rs, ∀ a∈(T:Subgroup G)⊓C,
    a∈normalizer (E:Set G) → (∀u∈E,a*u*a⁻¹*u⁻¹∈Zs) → a∈Rs⊔zpowers (s:G)
  intro E hE a ha haN hac
  have haS : a∈S := by
    by_contra haS
    let j := MulAut.conj a⁻¹
    have hpaira : elementaryAbelianMaxSubgroups Rs={Us,Us.map j.toMonoidHom} :=
      source_field_fixed_maximum_pair d hG T hST hsingle hL hM hTM hu s a ha.1 haS ha.2
    have hEj : E.map j.toMonoidHom=E :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (E:Set G)).inv_mem haN)
    have hEa : E.map (MulAut.conj a).toMonoidHom=E := mem_normalizer_iff_map_conj_eq.mp haN
    have hcancel : (MulAut.conj a).toMonoidHom.comp j.toMonoidHom=MonoidHom.id G := by
      ext u
      change a*(a⁻¹*u*(a⁻¹)⁻¹)*a⁻¹=u
      group
    have hEU : E=Us := by
      rw [hpaira] at hE
      rcases hE with rfl | he
      · rfl
      · have hm := congrArg (fun K:Subgroup G=>K.map (MulAut.conj a).toMonoidHom) he
        rw [hEa,map_map,hcancel,map_id] at hm
        exact hm
    have hUj : Us.map j.toMonoidHom=Us := hEU ▸ hEj
    have hUZ : Us≤Zs := by
      have hi : U⊓U.map j.toMonoidHom=Z :=
        source_absorbed_center_pair d hG T hST hsingle hL hM hTM hu a ha.1 haS
      intro u huU
      refine ⟨?_,huU.2⟩
      rw [←hi]
      refine ⟨huU.1,?_⟩
      have hle : Us.map j.toMonoidHom≤U.map j.toMonoidHom := map_mono inf_le_left
      exact hle (hUj.symm ▸ huU)
    exact hnot hUZ
  obtain ⟨r,hr,f,hf,he⟩ := field_fixed_factorization c (s:G) hs a ⟨haS,ha.2⟩
  have hfc : ∀u∈E,f*u*f⁻¹*u⁻¹∈Zs := by
    intro u huE
    have huR := (hE.1 huE).1
    have huC := (hE.1 huE).2
    have hd : r⁻¹*u*r*u⁻¹∈Zs := by
      refine ⟨?_,C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem hr.2) huC) hr.2) (C.inv_mem huC)⟩
      have hh := hder (commutator_mem_commutator (R.inv_mem hr.1) huR)
      change r⁻¹*u*r*u⁻¹∈Z
      simpa only [commutatorElement_def,inv_inv] using hh
    have ht : r⁻¹*(a*u*a⁻¹*u⁻¹)*r∈Zs := by
      have hrn : r⁻¹∈normalizer (Zs:Set G) :=
        Subgroup.centralizer_le_normalizer _ ((centralizer (Zs:Set G)).inv_mem (hRZs hr.1))
      simpa only [inv_inv] using (mem_normalizer_iff.mp hrn (a*u*a⁻¹*u⁻¹)).mp (hac u huE)
    have hh := Zs.mul_mem ht hd
    have heq : f*u*f⁻¹*u⁻¹=(r⁻¹*(a*u*a⁻¹*u⁻¹)*r)*(r⁻¹*u*r*u⁻¹) := by
      rw [←he]
      group
    exact heq ▸ hh
  have hfu : ∀u∈Us,f*u*f⁻¹*u⁻¹∈Zs := by
    have hcase : E=Us ∨ E=Vs := by simpa only [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] using hE
    rcases hcase with hEU | hEV
    · exact hEU ▸ hfc
    · intro u huU
      have hEU : e u∈E := hEV.symm ▸ mem_map_of_mem e.toMonoidHom huU
      have hh := hfc (e u) hEU
      have hef : e f=f := by
        change x⁻¹*f*(x⁻¹)⁻¹=f
        exact mul_inv_eq_iff_eq_mul.mpr (Commute.inv_left (hxf f hf)).eq
      have hmap : e (f*u*f⁻¹*u⁻¹)∈Zs := by
        simpa only [map_mul,map_inv,hef] using hh
      rw [←heZ] at hmap
      exact (mem_map_iff_mem e.injective).mp hmap
  have hfs : f∈zpowers (s:G) := source_centerless_field_fixed_plane_kernel
    d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR f hf hfu
  rw [←he]
  exact mul_mem_sup hr hfs

end CFSG.Quasithin.Chapter2.LinearShadows.Single
