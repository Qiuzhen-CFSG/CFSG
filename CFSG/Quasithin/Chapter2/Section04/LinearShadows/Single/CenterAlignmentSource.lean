module
public import Theory.GroupTheory.FrattiniFixedCenterAlignment
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FixedFrattiniSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterlessTerminalRows
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedPairSource
public import Stellmacher.ElementaryAbelianMaxPair.Normalizers
/-!
# Original fixed-center alignment

Transport an outside involution centralizer into the actual Sylow
centralizer of the marked field involution. The source TI and numerical
fixed-group rows, together with their Frattini subgroups and the two fixed
planes, identify the transported fixed center. The only independent input
is the literal kernel of the plane action modulo its center; the original
field-action producer discharges that input in the terminal assembly.

Source: Aschbacher–Smith, the end of the single linear block case, p.539.
-/
public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
open Stellmacher
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_centerless_fixed_center_alignment_of_quotient_kernel
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
        a∈normalizer (E:Set G)→(∀u∈E,a*u*a⁻¹*u⁻¹∈Zs)→a∈Rs⊔zpowers (s:G)) :
    ((distinguishedZ d)⊓centralizer ({i}:Set G)).map (MulAut.conj g).toMonoidHom=
      (distinguishedZ d)⊓centralizer ({(s:G)}:Set G) := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let Z := R⊓centralizer (R:Set G)
  let C := centralizer ({(s:G)}:Set G)
  let Rs := R⊓C
  let Zs := Z⊓C
  let P := (T:Subgroup G)⊓C
  let K := Rs⊔zpowers (s:G)
  let e := MulAut.conj g
  let I₀ := R⊓centralizer ({i}:Set G)
  let J₀ := Z⊓centralizer ({i}:Set G)
  let I := I₀.map e.toMonoidHom
  let J := J₀.map e.toMonoidHom
  have hZdef : distinguishedZ d=Z := distinguishedZ_of_centerless d hZ
  rw [hZdef]
  change J=Zs
  have hIP : I≤P := hIT
  have hJ₀I : J₀≤I₀ := inf_le_inf_right _ inf_le_left
  have hJI : J≤I := map_mono hJ₀I
  have hJP : J≤P := hJI.trans hIP
  have hRT : R≤(T:Subgroup G) := (sSup_le fun _ h=>h.1).trans hST.le
  have hclosed := c.centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hu hZ
  let : IsElementaryAbelian 2 Z := hZdef ▸ (source_distinguished_elementary d hG T hST hsingle hL hM hTM hu).1
  let : IsElementaryAbelian 2 J₀ := IsElementaryAbelian.of_injective (inclusion (show J₀≤Z from inf_le_left)) (inclusion_injective _)
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map e.toMonoidHom
  have hJR : J≤R := by
    rintro j ⟨a,ha,rfl⟩
    by_cases ha1 : a=1
    · simp only [ha1,map_one];exact one_mem R
    have haR : a∈R := ha.1.1
    have ha2 : orderOf a=2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha) ha1
    exact hclosed ⟨a,hRT haR⟩ ⟨e a,(hJP (mem_map_of_mem _ ha)).1⟩
      ((orderOf_coe _).symm.trans ha2) haR (isConj_iff.mpr ⟨g,rfl⟩)
  have hJRs : J≤Rs := le_inf hJR (hJP.trans inf_le_right)
  obtain ⟨m,hm,hn,hZsc,hRsc⟩ := source_centerless_field_fixed_orders d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR
  obtain ⟨k,_,hk,hJc,_,_,hphi⟩ := source_centerless_outside_noncentral_fixed_data d hG T hST hsingle hL hM hTM hu c hZ i hiT hiS hi2 (by simpa only [hZdef] using hiZ)
  have hkm : k=m := by omega
  have hcardJ : Nat.card J=Nat.card Zs := by
    rw [card_map_of_injective e.injective]
    rw [hJc,hZsc,hkm]
  have hphiI : (frattini I).map I.subtype=J := by
    rw [frattini_image_map I₀ e.toMonoidHom e.injective,hphi]
  have hIJ : I≤centralizer (J:Set G) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨j,hj,rfl⟩
    change e j * e a=e a * e j
    simpa only [map_mul] using congrArg e (hj.1.2 a ha.1).symm
  have hTIZ : J=Zs ∨ Disjoint Zs J := by
    have ht := (source_distinguished_TI d hG T hST hsingle hL hM hTM hu).eq_or_disjoint_conjugate g
    rw [hZdef] at ht
    rcases ht with he | hd
    · left
      change (Z⊓centralizer ({i}:Set G)).map e.toMonoidHom=Z⊓C
      rw [map_inf _ _ _ e.injective,he,Theory.GroupTheory.map_centralizer_singleton,hgi]
    · exact Or.inr (hd.symm.mono inf_le_left (map_mono inf_le_left))
  have hL' := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hTR := (d.lemma_2_4_8_1 hG T hST hsingle hL').2.2
  have hTZ : (T:Subgroup G)≤normalizer (Z:Set G) := by
    rw [←hZdef]
    exact source_distinguished_normalized_by_sylow d hG T hST hsingle hL hZ
  have hPRs : P≤normalizer (Rs:Set G) :=
    (le_inf (inf_le_left.trans hTR) (inf_le_right.trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hPZs : P≤normalizer (Zs:Set G) :=
    (le_inf (inf_le_left.trans hTZ) (inf_le_right.trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hsord : orderOf (s:G)=2 := (orderOf_coe s).trans hs2
  have hspow : (s:G)^2=1 := by simpa only [hsord] using pow_orderOf_eq_one (s:G)
  have hKp : IsPGroup 2 K := T.isPGroup'.to_le
    (sup_le (inf_le_left.trans hRT) (zpowers_le.mpr s.property))
  have hphiK : (frattini K).map K.subtype≤Zs := source_fixed_central_supplement_frattini_le
    d hG T hST hsingle hL hM hTM hu s s.property hspow
  obtain ⟨_,x,hx,hxS⟩ := source_field_centralizer_supplement d hG T hST hsingle hL hM hTM hu c s hs hs2 hsR
  let U := sourceModule L
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Us := U⊓C
  let Vs := Us.map (MulAut.conj x⁻¹).toMonoidHom
  have hCmap : C.map (MulAut.conj x⁻¹).toMonoidHom=C :=
    mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer (C.inv_mem hx.2))
  have hVs : Vs=V⊓C := by
    change (U⊓C).map (MulAut.conj x⁻¹).toMonoidHom=U.map (MulAut.conj x⁻¹).toMonoidHom⊓C
    rw [map_inf _ _ _ (MulAut.conj x⁻¹).injective,hCmap]
  have hUV : Us⊓Vs=Zs := by
    rw [hVs]
    have hpair := source_absorbed_center_pair d hG T hST hsingle hL hM hTM hu x hx.1 hxS
    change U⊓V=Z at hpair
    change (U⊓C)⊓(V⊓C)=Z⊓C
    rw [←hpair]
    ext a
    simp only [mem_inf]
    tauto
  have hpair : elementaryAbelianMaxSubgroups Rs={Us,Vs} := source_field_fixed_maximum_pair d hG T hST hsingle hL hM hTM hu s x hx.1 hxS hx.2
  have hUs : Us∈elementaryAbelianMaxSubgroups Rs := hpair.symm ▸ Set.mem_insert _ _
  have hVsM : Vs∈elementaryAbelianMaxSubgroups Rs := hpair.symm ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hUc : Nat.card Us=Nat.card Zs^2 := by
    rw [hZsc,source_centerless_field_plane_card d hG T hST hsingle hL hM hTM hu c hZ s hs hsord,hn,←pow_mul]
    congr 1;omega
  have hVc : Nat.card Vs=Nat.card Zs^2 := (card_map_of_injective (MulAut.conj x⁻¹).injective).trans hUc
  have hrun (A B:Subgroup G) (hfamily:elementaryAbelianMaxSubgroups Rs={A,B}) (hAB:A⊓B=Zs)
      (hAc:Nat.card A=Nat.card Zs^2)(hJA:J≤A) : J=Zs := by
    have hAm : A∈elementaryAbelianMaxSubgroups Rs := hfamily.symm ▸ Set.mem_insert _ _
    have hZsA : Zs≤A := hAB.ge.trans inf_le_left
    apply eq_fixed_center_of_frattini_quotient_kernel P A B Zs I J K hIP hJA hZsA hAB
      ((inf_le_left.trans inf_le_right).trans (centralizer_le (hAm.1.trans inf_le_left))) hPZs hIJ
      (fun a ha=>by
        have hh := maxFamily_conj_mem hAm (hPRs ha)
        simpa only [hfamily,Set.mem_insert_iff,Set.mem_singleton_iff,Subgroup.conjBy] using hh)
      hTIZ hcardJ hAc hphiI hKp hphiK (hkernel A hAm)
  rcases (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hu x hx.1 hxS).2 J hJR inferInstance with hj | hj
  · exact hrun Us Vs hpair hUV hUc (le_inf hj (hJP.trans inf_le_right))
  · exact hrun Vs Us (by simpa only [Set.pair_comm] using hpair) (by simpa only [inf_comm] using hUV) hVc
      (hVs ▸ le_inf hj (hJP.trans inf_le_right))
end CFSG.Quasithin.Chapter2.LinearShadows.Single
