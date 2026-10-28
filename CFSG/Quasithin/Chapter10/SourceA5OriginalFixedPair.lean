module
public import CFSG.Quasithin.Chapter10.SourceBlockModulePlacement
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.NormalizerFixedLine
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# The original pair of Sylow-fixed alternating-five layer vectors

The index-two block stabilizer in T acts on the first nontrivial binary
layer and therefore fixes a nonidentity vector. Distinct original blocks
commute, while an alternating-five layer has trivial intersection with
its own block centralizer. Consequently no Sylow element exchanging the
blocks fixes this vector, so its centralizer in T is precisely N_T(L).
Conjugation gives the second vector and the same exact centralizer.
The natural-module Sylow fixed-line bound makes both vectors unique.

All vectors remain in the original block layers and original local module;
no fixed-center hypothesis or model coordinates enter this construction.
Source: Aschbacher–Smith 10.2.1, printed p.743, using C.1.9 and C.1.13(c).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
private theorem ambient_layer_map (K : Subgroup G) (a : MulAut G) :
    ((blockU K).map K.subtype).map a.toMonoidHom =
      (blockU (K.map a.toMonoidHom)).map (K.map a.toMonoidHom).subtype := by
  let b : K ≃* (K.map a.toMonoidHom) := a.subgroupMap K
  rw [←RankOne.Solvable.blockU_map_equiv b,map_map,map_map]
  rfl

private theorem exists_fixed_layer (K R : Subgroup G)
    (hK : IsAlternatingBlock K 5) (hR : IsPGroup 2 R)
    (hRK : R ≤ normalizer (K : Set G)) :
    ∃ v : G, v ∈ (blockU K).map K.subtype ∧ v ≠ 1 ∧
      v ∈ centralizer (R : Set G) := by
  let V := (blockU K).map K.subtype
  have hRV : R ≤ normalizer (V : Set G) :=
    hRK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  let := conjMulDistribMulActionOfLeNormalizer R V hRV
  have hVp : IsPGroup 2 V := hK.2.1.elementary.isPGroup.map K.subtype
  have hVne : V ≠ ⊥ := by
    intro he
    exact hK.2.1.blockU_ne_bot ((map_eq_bot_iff_of_injective (blockU K) K.subtype_injective).mp he)
  have hdiv : 2 ∣ Nat.card V := hVp.card_eq_or_dvd.resolve_left
    (fun he => hVne (card_eq_one.mp he))
  obtain ⟨v,hv,hvn⟩ := hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdiv
    (a := 1) (fun r => smul_one r)
  refine ⟨v,v.property,?_,?_⟩
  · intro he
    exact hvn (Subtype.ext he.symm)
  · intro r hr
    have he := congrArg Subtype.val (hv (⟨r,hr⟩ : R))
    exact mul_inv_eq_iff_eq_mul.mp he

omit [Finite G] in
private theorem layer_fixed_disjoint (K : Subgroup G) (hK : IsAlternatingBlock K 5) :
    Disjoint ((blockU K).map K.subtype) (centralizer (K : Set G)) := by
  rw [Subgroup.disjoint_def]
  rintro z ⟨u,hu,rfl⟩ hc
  have huc : u ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (hc k k.property)
  have hz : blockU K ⊓ center K = ⊥ := by
    rw [←blockFixed_map,hK.blockFixed_eq_bot,Subgroup.map_bot]
  exact congrArg Subtype.val (show u=1 from hz.le ⟨hu,huc⟩)

private theorem source_pair_commutes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅L,L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
  let H := localJoin T L
  let A := L.subgroupOf H
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    dsimp only [B]
    rw [map_map,show H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
  obtain ⟨hA,_,_⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  have hB : IsBlock B := hA.map_equiv (MulAut.conj tH)
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA)
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLH).symm))
  have hc := congrArg (map H.subtype)
    (hA.commutator_eq_bot_of_quasisimple_quotient hB hqA hne)
  rwa [map_commutator,hmapA,hmapB,Subgroup.map_bot] at hc


private theorem source_fixed_vector_centralizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {v : G} (hv : v ∈ (blockU L).map L.subtype) (hvn : v ≠ 1)
    (hvR : v ∈ centralizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G)) :
    (T : Subgroup G) ⊓ centralizer ({v} : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  apply le_antisymm
  · rintro s ⟨hsT,hsv⟩
    refine ⟨hsT,?_⟩
    by_contra hsN
    have hc := source_pair_commutes D e hn hout hsT hsN
    have hc' : L.map (MulAut.conj s).toMonoidHom ≤ centralizer (L : Set G) := by
      rw [commutator_comm] at hc
      exact commutator_eq_bot_iff_le_centralizer.mp hc
    have hfixed : (MulAut.conj s) v = v := by
      change s*v*s⁻¹=v
      rw [mem_centralizer_singleton_iff.mp hsv,mul_inv_cancel_right]
    have hvL : v ∈ L.map (MulAut.conj s).toMonoidHom :=
      hfixed ▸ mem_map_of_mem (MulAut.conj s).toMonoidHom ((map_subtype_le _) hv)
    exact hvn ((Subgroup.disjoint_def.mp (layer_fixed_disjoint L hL)) hv (hc' hvL))
  · intro s hs
    exact ⟨hs.1,mem_centralizer_singleton_iff.mpr (hvR s hs)⟩

private theorem ambient_sylow_fixed_small (K R : Subgroup G)
    (hK : IsAlternatingBlock K 5) (hR : Chapter1.IsSylowIn 2 R K) :
    Nat.card ((blockU K).map K.subtype ⊓ centralizer (R : Set G) : Subgroup G) ≤ 2 := by
  obtain ⟨P,hP⟩ := hR
  let f : ((blockU K).map K.subtype ⊓ centralizer (R : Set G) : Subgroup G) →
      (blockU K ⊓ centralizer (P : Set K) : Subgroup K) := fun x =>
    ⟨⟨x,(map_subtype_le (blockU K)) x.property.1⟩,by
      refine ⟨?_,?_⟩
      · obtain ⟨l,hl,he⟩ := x.property.1
        exact (Subtype.ext he : l = ⟨x,_⟩) ▸ hl
      · intro p hp
        apply Subtype.ext
        exact x.property.2 p (hP ▸ mem_map_of_mem K.subtype hp)⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : (blockU K ⊓ centralizer (P : Set K) : Subgroup K) =>
      ((z : K) : G)) he)
  exact (Nat.card_le_card_of_injective f hf).trans (hK.sylow_fixed_card_le_two P)

private theorem unique_nonidentity_of_card_le_two (F : Subgroup G)
    (hcard : Nat.card F ≤ 2) {v : G} (hv : v ∈ F) (hvn : v ≠ 1) :
    ∀ w ∈ F, w ≠ 1 → w = v := by
  have hne : F ≠ ⊥ := fun he => hvn (he.le hv)
  have hc : Nat.card F = 2 := le_antisymm hcard (F.one_lt_card_iff_ne_bot.mpr hne)
  obtain ⟨z,_,hunique⟩ := (Nat.card_eq_two_iff' (1:F)).mp hc
  intro w hw hwn
  exact congrArg Subtype.val ((hunique ⟨w,hw⟩ (fun he => hwn (congrArg Subtype.val he))).trans
    (hunique ⟨v,hv⟩ (fun he => hvn (congrArg Subtype.val he))).symm)

/-- The two original Sylow-fixed vectors, with their literal conjugation and
all group-theoretic markings needed by the positive-center argument. -/
structure SourceA5OriginalFixedPair
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (t : G) where
  blocks_commute : ⁅L,L.map (MulAut.conj t).toMonoidHom⁆ = ⊥
  first : G
  second : G
  conjugate : second = (MulAut.conj t) first
  first_ne : first ≠ 1
  second_ne : second ≠ 1
  first_layer : first ∈ (blockU L).map L.subtype
  second_layer : second ∈ (blockU (L.map (MulAut.conj t).toMonoidHom)).map
    (L.map (MulAut.conj t).toMonoidHom).subtype
  first_module : first ∈ D.moduleSubgroup
  second_module : second ∈ D.moduleSubgroup
  first_sylow : first ∈ (T : Subgroup G)
  second_sylow : second ∈ (T : Subgroup G)
  first_opposite : first ∈ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)
  second_opposite : second ∈ centralizer (L : Set G)
  first_fixed : first ∈ centralizer ((T : Subgroup G) ⊓ L : Set G)
  second_fixed : second ∈ centralizer
    ((T : Subgroup G) ⊓ L.map (MulAut.conj t).toMonoidHom : Set G)
  first_centralizer : (T : Subgroup G) ⊓ centralizer ({first} : Set G) =
    (T : Subgroup G) ⊓ normalizer (L : Set G)
  second_centralizer : (T : Subgroup G) ⊓ centralizer ({second} : Set G) =
    (T : Subgroup G) ⊓ normalizer (L : Set G)
  first_unique : ∀ w ∈ (blockU L).map L.subtype,
    w ∈ centralizer ((T : Subgroup G) ⊓ L : Set G) → w ≠ 1 → w = first
  second_unique : ∀ w ∈ (blockU (L.map (MulAut.conj t).toMonoidHom)).map
      (L.map (MulAut.conj t).toMonoidHom).subtype,
    w ∈ centralizer ((T : Subgroup G) ⊓ L.map (MulAut.conj t).toMonoidHom : Set G) →
    w ≠ 1 → w = second

/-- Every prescribed original Sylow exchanger admits the actual pair of
nonidentity fixed vectors. No fixed-center or orthogonal marking is assumed. -/
theorem source_a5_original_fixed_pair
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    Nonempty (SourceA5OriginalFixedPair D t) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let B := L.map (MulAut.conj t).toMonoidHom
  let a := MulAut.conj t
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hB : IsAlternatingBlock B 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv (a.subgroupMap L) hL
  have hcomm := source_pair_commutes D e hn hout ht htn
  have hLB : L ≤ centralizer (B : Set G) := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hBL : B ≤ centralizer (L : Set G) := le_centralizer_iff.mp hLB
  obtain ⟨v,hv,hvn,hvR⟩ := exists_fixed_layer L R hL (T.isPGroup'.to_le inf_le_left) inf_le_right
  have hCT := source_fixed_vector_centralizer D e hn hout hv hvn hvR
  have hi : (R.subgroupOf (T : Subgroup G)).index = 2 := by
    change R.relIndex (T : Subgroup G) = 2
    rw [show R = (T : Subgroup G) ⊓ normalizer (L : Set G) from rfl,inf_relIndex_left]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  let : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from inf_le_left)).mp
      inferInstance
  have hTmap : (T : Subgroup G).map a.toMonoidHom = (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
  have hRmap : R.map a.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp (hTR ht)
  have hCT' : (T : Subgroup G) ⊓ centralizer ({a v} : Set G) = R := by
    have he := congrArg (map a.toMonoidHom) hCT
    rw [map_inf _ _ _ a.injective,hTmap,Theory.GroupTheory.map_centralizer_equiv,
      Set.image_singleton,hRmap] at he
    exact he
  have hav : a v ∈ (blockU B).map B.subtype := by
    rw [←ambient_layer_map L a]
    exact mem_map_of_mem a.toMonoidHom hv
  have havn : a v ≠ 1 := fun he => hvn (a.injective (he.trans (a.map_one).symm))
  have hvM : v ∈ D.moduleSubgroup := source_a5_original_block_module_le D e hn hout hv
  have havM : a v ∈ D.moduleSubgroup := (D.sylow_normalizes_module ht v).mp hvM
  have hvP : v ∈ centralizer ((T : Subgroup G) ⊓ L : Set G) :=
    centralizer_le (inf_le_inf_left _ L.le_normalizer) hvR
  have havR : a v ∈ centralizer (R : Set G) := by
    intro r hr
    exact mem_centralizer_singleton_iff.mp ((hCT'.symm ▸ hr).2)
  have havP : a v ∈ centralizer ((T : Subgroup G) ⊓ B : Set G) :=
    centralizer_le (inf_le_inf_left _ (hBL.trans (Subgroup.centralizer_le_normalizer _))) havR
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hc : (L.subgroupOf (localJoin T L)).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hP : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ L) L :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right),
        map_subgroupOf_eq_of_le le_sup_right⟩ hLH hc.subnormal
  have hPB : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ B) B := by
    have hh := (Chapter1.IsSylowIn.map_iff a.toMonoidHom a.injective).mpr hP
    rwa [map_inf _ _ _ a.injective,hTmap] at hh
  refine ⟨⟨hcomm,v,a v,rfl,hvn,havn,hv,hav,hvM,havM,D.module_le_sylow hvM,
    D.module_le_sylow havM,hLB ((map_subtype_le _) hv),hBL ((map_subtype_le _) hav),
    hvP,havP,hCT,hCT',?_,?_⟩⟩
  · intro w hw hwP hwn
    exact unique_nonidentity_of_card_le_two _ (ambient_sylow_fixed_small L _ hL hP)
      ⟨hv,hvP⟩ hvn w ⟨hw,hwP⟩ hwn
  · intro w hw hwP hwn
    exact unique_nonidentity_of_card_le_two _ (ambient_sylow_fixed_small B _ hB hPB)
      ⟨hav,havP⟩ havn w ⟨hw,hwP⟩ hwn

/-- The source nonnormal orbit supplies an exchanger and its original
fixed pair together with the literal two-block orbit decomposition. -/
theorem source_a5_exists_original_fixed_pair
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      Nonempty (SourceA5OriginalFixedPair D t) := by
  obtain ⟨t,ht,htn,he,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  exact ⟨t,ht,htn,he,source_a5_original_fixed_pair D e hn hout ht htn⟩

end CFSG.Quasithin.Chapter10
