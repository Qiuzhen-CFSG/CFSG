module
public import Theory.SpecificGroups.SymmetricFive.TranspositionCubic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.MovedModel
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# C.1.24 for an intermediate transposition image

Let G=LR have characteristic two, with L normal and two-perfect, and let
V be its faithful binary five-point augmentation module modulo O₂(G).
For any two-subgroup R containing O₂(G) whose actual image is generated
by a transposition, either Baum(R) has a nontrivial characteristic
subgroup normal in G, or L is an A₅ block.

If J(R) centralizes V, B.2.10 makes Baum(R) normal. Otherwise its image
is the same transposition. A native cubic moves the corresponding fixed
space and generates S₅ together with the transposition normalizer.
The C.1.18 local seed and C.1.21 propagation then give a block; the literal
module coordinates identify it as an A₅ block. R need not be Sylow in G.

The consumer is the actual intermediate Q₂ in source 13.2.12.
Source: Aschbacher--Smith C.1.24, printed pp.130--131, transposition case.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Equiv Stellmacher Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.FiveIntermediate
open GlaubermanNiles GlaubermanArgument
open Theory.SpecificGroups.SymmetricFive.TranspositionCubic
open SymmetricSix
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem normal_baumann_or_swap (V R : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hQR : pCore 2 G ≤ R)
    (q : G →* Sym) (hk : q.ker = centralizer (V : Set G))
    (hcore : q.ker = pCore 2 G)
    (r : Sym) (hr : r.IsSwap) (hR : R.map q = zpowers r) :
    (ChapterB.baumann R).Normal ∨ r ∈ (elementaryAbelianMaxJ R).map q := by
  by_cases hJ : elementaryAbelianMaxJ R ≤ q.ker
  · left
    apply (ChapterB.lemma_B_2_10_centralizing V R hVR hQR ?_ ?_).2.2.2
    · rw [←hk,hcore,inf_eq_right.mpr hQR]
    · simpa only [ChapterB.thompsonJ_zero,hk] using hJ
  · right
    have hle : (elementaryAbelianMaxJ R).map q ≤ zpowers r := by
      rw [←hR]; exact map_mono (sSup_le fun _ hA => hA.1)
    have hne : (elementaryAbelianMaxJ R).map q ≠ ⊥ :=
      fun hz => hJ ((Subgroup.map_eq_bot_iff _).mp hz)
    let J := ((elementaryAbelianMaxJ R).map q).subgroupOf (zpowers r)
    let : Fact (Nat.card (zpowers r)).Prime := ⟨by rw [Nat.card_zpowers,hr.orderOf];decide⟩
    rcases J.eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hh := congrArg (map (zpowers r).subtype) hb
      rw [map_subgroupOf_eq_of_le hle,Subgroup.map_bot] at hh
      exact (hne hh).elim
    · have hh := congrArg (map (zpowers r).subtype) ht
      rw [map_subgroupOf_eq_of_le hle,←MonoidHom.range_eq_map,range_subtype] at hh
      rw [hh];exact mem_zpowers r

private theorem selected_local (R V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M=3)
    (hRq : Nat.card (R.map (QuotientGroup.mk' (pCore 2 G)))=2)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)))
    (hf : generalizedFitting G=pCore 2 G)
    (q : G →* Sym) (r c : Sym)
    (hR : R.map q ≤ zpowers r) (hrJ : r ∈ (elementaryAbelianMaxJ R).map q)
    (hcH : c ∈ (selectedGroup R M).map q)
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (q g) (e v).toAdd)
    (hc : c^3=1) (hi : r*c*r⁻¹=c⁻¹)
    (hm : ¬fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) (zpowers r) ≤
      fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) (zpowers c)) :
    InLocalClass (inclusion (show ChapterB.baumann (R.subgroupOf (selectedGroup R M)) ≤
      pResidual 2 (selectedGroup R M) ⊔ ChapterB.baumann (R.subgroupOf (selectedGroup R M)) from le_sup_right)) := by
  let H := selectedGroup R M
  let V' := V.subgroupOf H
  let eV : V' ≃* V := subgroupOfEquivOfLe (hVR.trans (le_selectedGroup R M))
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.subgroupOf (hVR.trans (le_selectedGroup R M))
  have he' : ∀ (g : H) (v : V'), ((eV.trans e) (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) ((q.comp H.subtype) g) ((eV.trans e) v).toAdd := by
    intro g v
    exact he g (eV v)
  have hR' : (R.subgroupOf H).map (q.comp H.subtype) ≤ zpowers r := by
    rw [←map_map,map_subgroupOf_eq_of_le (le_selectedGroup R M)];exact hR
  have hrJ' : r ∈ (elementaryAbelianMaxJ (R.subgroupOf H)).map (q.comp H.subtype) := by
    rw [←map_map,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (le_selectedGroup R M)];exact hrJ
  have hc' : c ∈ (q.comp H.subtype).range := by
    obtain ⟨x,hx,hxc⟩ := hcH
    exact ⟨⟨x,hx⟩,hxc⟩
  have hm' := Theory.SpecificGroups.SymmetricFive.TranspositionCubic.omega_span_moved
    V' (R.subgroupOf H) (elementaryAbelianMaxJ (R.subgroupOf H)) (comap_mono hVR)
    (q.comp H.subtype) (eV.trans e) he' r c hR' hrJ' hc' hc hi hm
  obtain ⟨T,hT,hiT⟩ := selected_sylow R hpR hQR M hM hRq hn
  rw [←hT] at hm' ⊢
  exact FiveBlockSource.cubic_omega_inLocalClass T hiT (selected_characteristic_two R M hf) hm'

private theorem cubic_noncentral (L Y : Subgroup G) (hL : L.IsSubnormal)
    (hYL : Y ≤ L) (q : G →* Sym) (hQ : pCore 2 G ≤ q.ker)
    (hLq : L.map q = alternatingGroup (Fin 5)) (c : Sym)
    (hc : orderOf c=3) (hY : Y.map q=zpowers c) :
    ¬ (Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L) := by
  have hk : pCore 2 L ≤ (q.comp L.subtype).ker := by
    rw [←hL.pCore_subgroupOf 2]
    intro x hx
    exact hQ hx
  let f := QuotientGroup.lift (pCore 2 L) (q.comp L.subtype) hk
  have hcY : c∈Y.map q := by rw [hY];exact mem_zpowers c
  obtain ⟨y,hy,hyc⟩ := hcY
  let z : L := ⟨y,hYL hy⟩
  have hca : c∈alternatingGroup (Fin 5) := by rw [←hLq];exact ⟨y,hYL hy,hyc⟩
  intro hcent
  have hz := hcent (mem_map_of_mem (QuotientGroup.mk' (pCore 2 L)) (show z∈Y.subgroupOf L from hy))
  have hcc : (⟨c,hca⟩ : alternatingGroup (Fin 5))∈center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro a
    have ha : (a:Sym)∈L.map q := by rw [hLq];exact a.property
    obtain ⟨l,hl,hla⟩ := ha
    have he := congrArg f (mem_center_iff.mp hz (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩))
    simp only [map_mul] at he
    change q l*q y=q y*q l at he
    apply Subtype.ext
    change (a:Sym)*c=c*(a:Sym)
    rw [←hla,←hyc]
    exact he
  rw [alternatingGroup.center_eq_bot (by simp)] at hcc
  have he : c=1 := congrArg Subtype.val (mem_bot.mp hcc)
  rw [he,orderOf_one] at hc
  omega

/-- The local cubic seed gives the block alternative for the intermediate R. -/
theorem normal_characteristic_or_block
    (L V R : Subgroup G) [L.Normal] [V.Normal] [IsElementaryAbelian 2 V]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hpL : IsPPerfect 2 L) (hf : generalizedFitting G=pCore 2 G)
    (hfL : generalizedFitting L=pCore 2 L)
    (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R)
    (hgen : L ⊔ R = ⊤)
    (q : G →* Sym) (hq : Function.Surjective q)
    (hcore : q.ker = pCore 2 G) (hk : q.ker=centralizer (V : Set G))
    (hLq : L.map q=alternatingGroup (Fin 5))
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (q g) (e v).toAdd)
    (r : Sym) (hr : r.IsSwap) (hR : R.map q=zpowers r) :
    (∃ C : Subgroup (ChapterB.baumann R), C.Characteristic ∧ C≠⊥ ∧
      (C.map (ChapterB.baumann R).subtype).Normal) ∨ IsBlock L := by
  have hVR : V ≤ R := (show V ≤ pCore 2 G from
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  have hRne : R≠⊥ := by
    intro hb
    have hb' := hR
    rw [hb,Subgroup.map_bot] at hb'
    have hr1 : r=1 := zpowers_eq_bot.mp hb'.symm
    have hh := hr.orderOf
    rw [hr1,orderOf_one] at hh
    omega
  let S := ChapterB.baumann R
  let : Nontrivial S := (nontrivial_iff_ne_bot _).mpr (baumann_ne_bot R hpR hRne)
  rcases normal_baumann_or_swap V R hVR hQR q hk hcore r hr hR with hSn | hrJ
  · left
    exact ⟨⊤,inferInstance,top_ne_bot,by simpa only [←MonoidHom.range_eq_map,range_subtype] using hSn⟩
  obtain ⟨c,hc,hca,hinv,hgn,hcard,hmove⟩ := exists_cubic_for_transposition r hr
  let π := QuotientGroup.mk' (pCore 2 G)
  let a : (G ⧸ pCore 2 G) ≃* Sym :=
    (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have ha : a.toMonoidHom.comp π=q := by ext x;rfl
  let M := (zpowers c).map a.symm.toMonoidHom
  have hMa : M.map a.toMonoidHom=zpowers c := by
    change ((zpowers c).map a.symm.toMonoidHom).map a.toMonoidHom = _
    rw [map_map];simp
  have hM : Nat.card M=3 := (card_map_of_injective a.symm.injective).trans (by rw [Nat.card_zpowers,hc])
  have hRa : (R.map π).map a.toMonoidHom=zpowers r := by rw [map_map,ha,hR]
  have hRq : Nat.card (R.map π)=2 := by
    rw [←card_map_of_injective (K := R.map π) (f := a.toMonoidHom) a.injective,hRa,Nat.card_zpowers,hr.orderOf]
  have hn : R.map π ≤ normalizer (M : Set (G ⧸ pCore 2 G)) := by
    rw [←map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective,map_equiv_normalizer_eq,hRa,hMa]
    apply zpowers_le.mpr
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (r*c*r⁻¹)=zpowers c
    rw [hinv,zpowers_inv]
  let H := selectedGroup R M
  let B := ChapterB.baumann (R.subgroupOf H)
  let K := pResidual 2 H ⊔ B
  let i : K →* G := H.subtype.comp K.subtype
  let Y := (pResidual 2 H).map H.subtype
  have hYq : Y.map q=zpowers c := by
    rw [←ha,←map_map,selected_residual_image R hpR M hM hn]
    exact hMa
  have hcH : c∈H.map q := (map_mono (map_subtype_le _)) (by rw [hYq];exact mem_zpowers c)
  have hloc : InLocalClass (inclusion (show B≤K from le_sup_right)) :=
    selected_local R V hVR hpR hQR M hM hRq hn hf q r c hR.le hrJ hcH e he
      (hc ▸ pow_orderOf_eq_one c) hinv hmove
  obtain ⟨E,hE⟩ := exists_selected_marking R M
  let emb : S →* K := (inclusion (show B≤K from le_sup_right)).comp E.toMonoidHom
  have hlocal : InLocalClass emb := hloc.precomp_equiv E
  have him : i.range=Y ⊔ S := by
    rw [MonoidHom.range_comp,range_subtype,Subgroup.map_sup,selected_baumann_map]
  have hi : Function.Injective i := H.subtype_injective.comp K.subtype_injective
  have hRpre : (zpowers r).comap q=R := by
    rw [←hR,comap_map_eq,sup_of_le_left (hcore ▸ hQR)]
  have hN : normalizer (zpowers r : Set Sym) ≤ (normalizer (S : Set G)).map q := by
    have hh : (normalizer (zpowers r : Set Sym)).comap q ≤ normalizer (S : Set G) :=
      ((zpowers r).le_normalizer_comap q).trans (hRpre ▸ normalizer_le_normalizer_baumann R)
    exact (map_comap_eq_self_of_surjective hq _).symm.le.trans (map_mono hh)
  have hKgen : i.range ⊔ normalizer (S : Set G)=⊤ := by
    rw [him,sup_assoc,sup_of_le_right S.le_normalizer]
    let D := Y ⊔ normalizer (S : Set G)
    have hfull : D.map q=⊤ := by
      apply top_unique
      rw [←hgn]
      exact sup_le (hN.trans (map_mono le_sup_right)) (hYq ▸ map_mono le_sup_left)
    have hker : q.ker ≤ D := (hcore ▸ hQR).trans
      (R.le_normalizer.trans ((normalizer_le_normalizer_baumann R).trans le_sup_right))
    have hh := congrArg (comap q) hfull
    rwa [comap_map_eq,comap_top,sup_of_le_left hker] at hh
  have hYlocal : (pResidual 2 K).map i=Y := selected_local_residual_map R hpR M
  have hYL : Y≤L := (map_pResidual_le 2 H.subtype).trans
    (sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top L R hpR hgen⟩)
  have hQY : pCore 2 G≤normalizer (Y : Set G) := core_normalizes_selected_residual R M
  have hne := cubic_noncentral L Y (inferInstance : L.Normal).isSubnormal hYL q
    hcore.symm.le hLq c hc hYq
  obtain ⟨D,hD⟩ := exists_universal_characteristicPair.{u,u}
    (hpR.to_le (show S≤R from inf_le_left)) (baumann_intrinsic_fixed R)
  exact embedded_local_seed_alternative S L emb i hi hE hlocal D hD hKgen
    (by rw [hYlocal];exact hYL) (inferInstance : L.Normal).isSubnormal hpL hfL
    (by rw [hYlocal];exact hQY) (by rw [hYlocal];exact hne)

/-- The given five-point module identifies the resulting block as an A₅ block. -/
theorem normal_characteristic_or_alternatingBlock
    (L V R : Subgroup G) [L.Normal] [V.Normal] [IsElementaryAbelian 2 V]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hpL : IsPPerfect 2 L) (hf : generalizedFitting G=pCore 2 G)
    (hfL : generalizedFitting L=pCore 2 L)
    (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R)
    (hgen : L ⊔ R = ⊤)
    (q : G →* Sym) (hq : Function.Surjective q)
    (hcore : q.ker = pCore 2 G) (hk : q.ker=centralizer (V : Set G))
    (hLq : L.map q=alternatingGroup (Fin 5))
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (q g) (e v).toAdd)
    (r : Sym) (hr : r.IsSwap) (hR : R.map q=zpowers r) :
    (∃ C : Subgroup (ChapterB.baumann R), C.Characteristic ∧ C≠⊥ ∧
      (C.map (ChapterB.baumann R).subtype).Normal) ∨ IsAlternatingBlock L 5 := by
  rcases normal_characteristic_or_block L V R hpL hf hfL hpR hQR hgen q hq hcore hk
    hLq e he r hr hR with hc | hb
  · exact Or.inl hc
  · right
    let f : Additive V →ₗ[ZMod 2] BinaryPermutation.core (Fin 5) := {
      toFun := fun v => (e v.toMul).toAdd
      map_add' := fun x y => by change (e (x.toMul*y.toMul)).toAdd = _;rw [map_mul];rfl
      map_smul' := ZMod.map_smul (e.toAdditive.trans
        (AddEquiv.additiveMultiplicative (BinaryPermutation.core (Fin 5)))) }
    have hfe : ∀ g v, f (NormalElementaryQuotient.representation V q hq hk g v) =
        BinaryPermutation.coreRepresentation (Fin 5) g (f v) := by
      intro g v
      obtain ⟨a,rfl⟩ := hq g
      change (e (NormalElementaryQuotient.representation V q hq hk (q a) v).toMul).toAdd = _
      have hv : (NormalElementaryQuotient.representation V q hq hk (q a) v).toMul =
          MulAut.conjNormal a v.toMul :=
        Subtype.ext (NormalElementaryQuotient.representation_apply V q hq hk a v)
      rw [hv]
      exact he a v.toMul
    exact (FiveBlockSource.alternating_block_of_covered_quotient V q hq hk L hLq hb
      (hcore.symm.trans hk).le f
      (fun v => ⟨Additive.ofMul (e.symm (Multiplicative.ofAdd v)),congrArg Multiplicative.toAdd (e.apply_symm_apply _)⟩)
      hfe (by
        intro v hv g _
        have hv0 : v=0 := by
          apply Additive.toMul.injective
          apply e.injective
          exact Multiplicative.toAdd.injective (hv.trans (map_one e).symm)
        rw [hv0,map_zero])).1
end CFSG.Quasithin.ChapterC.RankOne.FiveIntermediate
