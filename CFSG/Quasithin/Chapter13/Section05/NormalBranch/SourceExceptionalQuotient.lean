module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalComponent
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import Theory.GroupTheory.PrimeRankWitness
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalQuotientSylow
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalRadical
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Exclusion

/-!
# The original exceptional quotient and the normal-branch core identity

Let C=C_T(K) for the actual selected A₅ block and let J=K_D C. The radical
argument identifies O₂(J)=C. The original V survives in J/O₂(J) with order
sixteen, making that C-component quotient quasisimple. The original K embeds
as an alternating-five block, with its literal module equal to the image of V.
Normalizer control from the earlier maximality theorem makes this module
self-centralizing and forces its normalizer to normalize the same block.

Together with the actual quotient Sylow subgroup and its index bound, these
marks apply the complete deleted-five Theorem C obstruction. Thus the order-two
case for C is impossible and O₂(LT)=V. The final theorem derives every
component, core, quotient and model input from the original normal A₆ setup,
retaining the genuine earlier maximality hypothesis from 13.3.2.

Source: Aschbacher--Smith 13.5.15(7), printed pp.920--921.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalQuotient
open Section08.SourceCompletion

private theorem quotient_module_self_centralizing
    {X : Type*} [Group X] (V Z : Subgroup X) [Z.Normal]
    (hZ : Z ≤ center X) (hdis : V ⊓ Z = ⊥)
    (hn : normalizer ((V ⊔ Z : Subgroup X) : Set X) ≤ normalizer (V : Set X))
    (hc : centralizer ((V ⊔ Z : Subgroup X) : Set X) ≤ V ⊔ Z) :
    centralizer (V.map (QuotientGroup.mk' Z) : Set (X ⧸ Z)) ≤
      V.map (QuotientGroup.mk' Z) := by
  let q := QuotientGroup.mk' Z
  let R := (centralizer (V.map q : Set (X ⧸ Z))).comap q
  have hRN : R ≤ normalizer ((V ⊔ Z : Subgroup X) : Set X) := by
    have hh := comap_mono (f := q) (centralizer_le_normalizer (V.map q : Set (X ⧸ Z)))
    rwa [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      comap_map_eq, QuotientGroup.ker_mk'] at hh
  have hRmap : R.map q ≤ centralizer (V.map q : Set (X ⧸ Z)) := map_comap_le _ _
  have hcommZ : ⁅V,R⁆ ≤ Z := by
    have hh : (⁅V,R⁆ : Subgroup X).map q = ⊥ := by
      rw [map_commutator,commutator_eq_bot_iff_le_centralizer]
      exact le_centralizer_iff.mp hRmap
    rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hh
    exact hh
  have hcommV : ⁅V,R⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hRN.trans hn)
  have hRV : R ≤ centralizer (V : Set X) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique ((le_inf hcommV hcommZ).trans hdis.le)))
  have hRQ : R ≤ centralizer ((V ⊔ Z : Subgroup X) : Set X) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hRV) (hZ.trans (center_le_centralizer _))
  intro x hx
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective Z x
  have hr : r ∈ R := hx
  have hm : q r ∈ (V ⊔ Z).map q := mem_map_of_mem q (hc (hRQ hr))
  have hzmap : Z.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  simpa only [Subgroup.map_sup,hzmap,sup_bot_eq] using hm

variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)

include d hmax in
theorem original_core_centralizer_le :
    centralizer (D.LT.pCoreIn 2 : Set G) ≤ D.LT.pCoreIn 2 := by
  have hu := hmax.sylow_normalized_maximal_unique d.normalizes_L
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  rw [← d.local_normalizer] at hu
  have hTM : (D.T : Subgroup G) ≤ M := by
    rw [d.local_normalizer]
    exact d.normalizes_L
  have hLM : D.L ≤ M := d.local_normalizer ▸ D.L.le_normalizer
  have hchar : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2 := by
    have hh := d.counterexample.qtke.evenCharacteristic D.T M hu.1 hTM
    rintro x ⟨hxM,hxC⟩
    exact mem_map_of_mem M.subtype (hh (show (⟨x,hxM⟩ : M) ∈
      centralizer (pCore 2 M : Set M) from fun q hq =>
        Subtype.ext (hxC q (mem_map_of_mem M.subtype hq))))
  have hQne : D.LT.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact d.chosen.ne_bot (bot_unique (d.chosen.le_core.trans he.le))
  obtain ⟨hc,hi⟩ := centralizer_pCoreIn_le_of_unique_twoLocal D.T
    (show (D.T : Subgroup G) ≤ D.LT from le_sup_right) (sup_le hLM hTM)
    hQne hu.2 hchar
  exact hc.trans hi

include d in
theorem original_maximal_normalizes_module (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) : M ≤ normalizer (D.V : Set G) := by
  obtain ⟨-,hV,-⟩ := SourceSixBlock.source13_5_15_four d h e hseed hn hU
  rw [← hV,d.local_normalizer]
  exact normalizer_le_normalizer_characteristic_image D.L (ChapterC.blockU D.L)

include d in
theorem exceptional_maximal_centralizer_normalizes_pair
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (PlaneGeometry.TwoBlocks.localMap d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2 = D.V)
    (hsplit : D.LT.pCoreIn 2 = D.V ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)))
    (hCL : (D.T : Subgroup G) ⊓ centralizer (D.L : Set G) = ⊥)
    (hcard : Nat.card ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2) :
    M ⊓ centralizer (((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G) ≤
      normalizer (NormalBranch.K D g.val : Set G) := by
  let K := NormalBranch.K D g.val
  let C := (D.T : Subgroup G) ⊓ centralizer (K : Set G)
  let X := D.L ⊓ centralizer (C : Set G)
  have hres : (pResidual 2 X).map X.subtype = K :=
    SourceExceptionalNormalizer.exceptional_local_centralizer_residual d h e g hK hp a hi hS hsplit hCL hcard
  have hMN : M ≤ normalizer (D.L : Set G) := d.local_normalizer.le
  have hn : M ⊓ centralizer (C : Set G) ≤ normalizer (X : Set G) :=
    (le_inf (inf_le_left.trans hMN)
      (inf_le_right.trans (centralizer (C : Set G)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hh := hn.trans (normalizer_le_normalizer_characteristic_image X (pResidual 2 X))
  rwa [hres] at hh


include d hmax in
theorem exceptional_quotient_control
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH)
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (PlaneGeometry.TwoBlocks.localMap d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2 = D.V)
    (hsplit : D.LT.pCoreIn 2 = D.V ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)))
    (hcard : Nat.card ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2)
    (KD : Subgroup G) (hKKD : NormalBranch.K D g.val ≤ KD)
    (hKD : KD ≤ centralizer (((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))
    (hcore : (KD ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))).pCoreIn 2 =
      (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))
    (hdis : D.V ⊓ (KD ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))).pCoreIn 2 = ⊥) :
    let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
    let J := KD ⊔ C
    let q := QuotientGroup.mk' (pCore 2 J)
    let U := (D.V.subgroupOf J).map q
    let K₀ := ((NormalBranch.K D g.val).subgroupOf J).map q
    centralizer (U : Set (J ⧸ pCore 2 J)) ≤ U ∧
      normalizer (U : Set (J ⧸ pCore 2 J)) ≤ normalizer (K₀ : Set (J ⧸ pCore 2 J)) := by
  let K := NormalBranch.K D g.val
  let C := (D.T : Subgroup G) ⊓ centralizer (K : Set G)
  let J := KD ⊔ C
  let Z := pCore 2 J
  let VJ := D.V.subgroupOf J
  let q := QuotientGroup.mk' Z
  have hcore' : J.pCoreIn 2 = C := hcore
  have hVJ : D.V ≤ J := (hS ▸ pCoreIn_le 2 K).trans (hKKD.trans le_sup_left)
  have hKJ : K ≤ J := hKKD.trans le_sup_left
  let : IsCyclic C := isCyclic_of_prime_card (p := 2) hcard
  have hJG : J ≤ centralizer (C : Set G) := sup_le hKD C.le_centralizer
  have hZ : Z ≤ center J := by
    intro z hz
    have hc : (z : G) ∈ C := hcore' ▸ (mem_map_of_mem J.subtype hz : (z : G) ∈ J.pCoreIn 2)
    exact mem_center_iff.mpr (fun y => Subtype.ext ((hJG y.property z hc).symm))
  have hd : VJ ⊓ Z = ⊥ := by
    apply eq_bot_iff.mpr
    rintro x ⟨hxV,hxZ⟩
    have hx : (x : G) ∈ (⊥ : Subgroup G) := hdis ▸ ⟨hxV,mem_map_of_mem J.subtype hxZ⟩
    exact Subtype.ext hx
  have hmap : (VJ ⊔ Z).map J.subtype = D.LT.pCoreIn 2 := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVJ]
    change D.V ⊔ J.pCoreIn 2 = D.LT.pCoreIn 2
    rw [hcore,hsplit]
  have hNQ : normalizer (D.LT.pCoreIn 2 : Set G) ≤ M :=
    SourceExceptionalRadical.original_core_normalizer_le d hmax
  have hNM : (normalizer ((VJ ⊔ Z : Subgroup J) : Set J)).map J.subtype ≤ M := by
    have hh := (VJ ⊔ Z).le_normalizer_map J.subtype
    rw [hmap] at hh
    exact hh.trans hNQ
  have hNV : normalizer ((VJ ⊔ Z : Subgroup J) : Set J) ≤ normalizer (VJ : Set J) := by
    have hm : normalizer ((VJ ⊔ Z : Subgroup J) : Set J) ≤ (normalizer (D.V : Set G)).comap J.subtype :=
      map_le_iff_le_comap.mp (hNM.trans (original_maximal_normalizes_module d h e hseed hn hU))
    exact hm.trans (D.V.le_normalizer_comap J.subtype)
  have hCQ : centralizer ((VJ ⊔ Z : Subgroup J) : Set J) ≤ VJ ⊔ Z := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hmap]
    have hh : (centralizer ((VJ ⊔ Z : Subgroup J) : Set J)).map J.subtype ≤
        centralizer ((VJ ⊔ Z).map J.subtype : Set G) :=
      map_centralizer_le_centralizer_image ((VJ ⊔ Z : Subgroup J) : Set J) J.subtype
    rw [hmap] at hh
    exact hh.trans (original_core_centralizer_le d hmax)
  refine ⟨quotient_module_self_centralizing VJ Z hZ hd hNV hCQ,?_⟩
  have hCL := SourcePairCentralizer.sylow_local_centralizer_eq_bot_of_generated_core d h e hseed hn hU
  have hMK := exceptional_maximal_centralizer_normalizes_pair d h e g hK hp a hi hS hsplit hCL hcard
  intro x hx
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective Z x
  have hr : r ∈ normalizer ((VJ ⊔ Z : Subgroup J) : Set J) := by
    have hh : r ∈ (normalizer (VJ.map q : Set (J ⧸ Z))).comap q := hx
    rwa [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      comap_map_eq,QuotientGroup.ker_mk'] at hh
  have hrK : (r : G) ∈ normalizer (K : Set G) :=
    hMK ⟨hNM (mem_map_of_mem J.subtype hr),hJG r.property⟩
  have hrKJ : r ∈ normalizer (K.subgroupOf J : Set J) := K.le_normalizer_comap J.subtype hrK
  exact (K.subgroupOf J).le_normalizer_map q (mem_map_of_mem q hrKJ)


include d in
theorem exceptional_quotient_block
    (g : D.L) (hB : ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5)
    (hS : (NormalBranch.K D g.val).pCoreIn 2 = D.V)
    (hc : ⁅D.V,NormalBranch.K D g.val⁆ = D.V)
    (KD : Subgroup G) (hKKD : NormalBranch.K D g.val ≤ KD)
    (hcore : (KD ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))).pCoreIn 2 =
      (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))
    (hdis : D.V ⊓ (KD ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))).pCoreIn 2 = ⊥) :
    let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
    let J := KD ⊔ C
    let q := QuotientGroup.mk' (pCore 2 J)
    let K₀ := ((NormalBranch.K D g.val).subgroupOf J).map q
    ChapterC.IsAlternatingBlock K₀ 5 ∧
      (ChapterC.blockU K₀).map K₀.subtype = (D.V.subgroupOf J).map q ∧
      Nat.card ((ChapterC.blockU K₀).map K₀.subtype) = 16 := by
  let K := NormalBranch.K D g.val
  let C := (D.T : Subgroup G) ⊓ centralizer (K : Set G)
  let J := KD ⊔ C
  let q := QuotientGroup.mk' (pCore 2 J)
  have hcore' : J.pCoreIn 2 = C := hcore
  have hKJ : K ≤ J := hKKD.trans le_sup_left
  have hVJ : D.V ≤ J := (hS ▸ pCoreIn_le 2 K).trans hKJ
  have hNC : K ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (K : Set G) from inf_le_right)).trans
      (centralizer_le_normalizer C)
  have hKC : K ⊓ C ≤ D.V := by
    rw [← hS]
    exact le_pCoreIn_of_normalizes (D.T.isPGroup'.to_le (inf_le_right.trans inf_le_left))
      inf_le_left ((le_inf K.le_normalizer hNC).trans inf_normalizer_le_normalizer_inf)
  let f : K →* J ⧸ pCore 2 J := q.comp (inclusion hKJ)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro k hk
    have hm : (k : G) ∈ J.pCoreIn 2 :=
      mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff _).mp hk)
    have hkV : (k : G) ∈ D.V := hKC ⟨k.property,hcore'.le hm⟩
    have hz : (k : G) ∈ (⊥ : Subgroup G) := hdis ▸ ⟨hkV,hm⟩
    exact Subtype.ext hz
  let K₀ := (K.subgroupOf J).map q
  have hrange : f.range = K₀ := by rw [MonoidHom.range_comp,inclusion_range]
  let ek : K ≃* K₀ := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have hB₀ : ChapterC.IsAlternatingBlock K₀ 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv ek hB
  have hBU : (ChapterC.blockU K).map (inclusion hKJ) = D.V.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hVJ]
    exact SourceCoreSplit.pair_block_layer g hS hc
  have hlayer : (ChapterC.blockU K₀).map K₀.subtype = (D.V.subgroupOf J).map q := by
    rw [← ChapterC.RankOne.Solvable.blockU_map_equiv ek,map_map]
    change (ChapterC.blockU K).map f = _
    rw [← map_map,hBU]
  have hvf : Function.Injective (q.comp (inclusion hVJ)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro v hv
    have hm : (v : G) ∈ J.pCoreIn 2 :=
      mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff _).mp hv)
    have hz : (v : G) ∈ (⊥ : Subgroup G) := hdis ▸ ⟨v.property,hm⟩
    exact Subtype.ext hz
  have hvcard : Nat.card ((D.V.subgroupOf J).map q) = 16 := by
    rw [← inclusion_range hVJ,← MonoidHom.range_comp]
    rw [Nat.card_congr (MonoidHom.ofInjective hvf).symm.toEquiv]
    exact ReturningPlane.module_card d
  refine ⟨hB₀,hlayer,?_⟩
  rw [hlayer]
  exact hvcard


include d in
theorem exceptional_quotient_quasisimple (g : D.L) (KD : Subgroup G)
    (hV : D.V ≤ KD)
    (hKD : KD ≤ centralizer (((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))
    (hcomp : (KD.subgroupOf (centralizer (((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))).IsCComponent)
    (hcard : Nat.card ((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2)
    (hcore : (KD ⊔ ((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G))).pCoreIn 2 =
        (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))
    (hdis : D.V ⊓ (KD ⊔ ((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G))).pCoreIn 2 = ⊥) :
    let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
    let J := KD ⊔ C
    IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) ∧
      IsQuasisimple (J ⧸ pCore 2 J) := by
  let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
  let J := KD ⊔ C
  let q := QuotientGroup.mk' (pCore 2 J)
  have hCne : C ≠ ⊥ := by
    intro he
    change Nat.card C = 2 at hcard
    rw [he, card_bot] at hcard
    contradiction
  have hJne : J.pCoreIn 2 ≠ ⊥ := by rwa [hcore]
  have hsq := Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.counterexample.qtke hJne
  let : IsCyclic C := isCyclic_of_prime_card (p := 2) hcard
  have hJG : J ≤ centralizer (C : Set G) := sup_le hKD C.le_centralizer
  have hKJ : (KD.subgroupOf J).IsCComponent :=
    hcomp.subgroupOf_of_le le_sup_left hJG
  let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
  have hmap := hKJ.map_quotient (pCore 2 J)
  have hCcore : C.subgroupOf J = pCore 2 J := by
    apply (map_injective J.subtype_injective)
    rw [map_subgroupOf_eq_of_le (show C ≤ J from le_sup_right)]
    exact hcore.symm
  have hCmap : (C.subgroupOf J).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hCcore, QuotientGroup.ker_mk']
  have htop : (KD.subgroupOf J).map q = ⊤ := by
    have hs : KD.subgroupOf J ⊔ C.subgroupOf J = ⊤ :=
      (codisjoint_subgroupOf_sup KD C).eq_top
    have hm := congrArg (map q) hs
    simpa only [Subgroup.map_sup, hCmap, sup_bot_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using hm
  have htopcomp : (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent := htop ▸ hmap
  let f : D.V →* J ⧸ pCore 2 J := q.comp (inclusion (hV.trans le_sup_left))
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro v hv
    have hm : (v : G) ∈ J.pCoreIn 2 := by
      have hq : inclusion (hV.trans le_sup_left) v ∈ pCore 2 J :=
        (QuotientGroup.eq_one_iff _).mp hv
      exact mem_map_of_mem J.subtype hq
    have hz : (v : G) ∈ (⊥ : Subgroup G) := hdis ▸ ⟨v.property, hm⟩
    exact Subtype.ext hz
  let : IsElementaryAbelian 2 D.V := d.chosen.elementary
  let : CommGroup D.V := IsMulCommutative.instCommGroup
  have hpow : ∀ v : D.V, v ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 D.V)
  have hr : 4 ≤ primeRank 2 (J ⧸ pCore 2 J) :=
    primeRank_ge_of_elementary_embedding hpow
      (by simpa using ReturningPlane.module_card d) f hf
  have hrtop : 2 ≤ primeRank 2 (⊤ : Subgroup (J ⧸ pCore 2 J)) := by
    rw [Theory.GroupTheory.primeRank_equiv 2 topEquiv]
    omega
  let : IsQuasisimple (⊤ : Subgroup (J ⧸ pCore 2 J)) :=
    ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank hsq
      (pCore_quotient_pCore_eq_bot 2) htopcomp hrtop
  exact ⟨hsq, IsQuasisimple.of_mulEquiv topEquiv⟩


include d hmax in
theorem exceptional_impossible_of_component_core
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH)
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (PlaneGeometry.TwoBlocks.localMap d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2 = D.V)
    (hcard : Nat.card ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2)
    (KD : Subgroup G) (hKKD : NormalBranch.K D g.val ≤ KD)
    (hKD : KD ≤ centralizer (((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))
    (hcomp : (KD.subgroupOf (centralizer (((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))).IsCComponent)
    (hcore : (KD ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))).pCoreIn 2 =
      (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))
    (hdis : D.V ⊓ (KD ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))).pCoreIn 2 = ⊥) :
    False := by
  let K := NormalBranch.K D g.val
  let C := (D.T : Subgroup G) ⊓ centralizer (K : Set G)
  let T₀ := (D.T : Subgroup G) ⊓ centralizer (C : Set G)
  let J := KD ⊔ C
  let q := QuotientGroup.mk' (pCore 2 J)
  let K₀ := (K.subgroupOf J).map q
  let P := ((T₀ ⊓ J).subgroupOf J).map q
  have hB := SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have hc := SourceFiveSpan.module_commutator d hK a hi h hL hseed
  have hsplit := SourceCoreSplit.core_eq_module_sup_centralizer h g hK hB hS hc
  have hq := exceptional_quotient_quasisimple d g KD
    ((hS ▸ pCoreIn_le 2 K).trans hKKD) hKD hcomp hcard hcore hdis
  let : IsQuasisimple (J ⧸ pCore 2 J) := hq.2
  obtain ⟨hB₀,hlayer,hcard₀⟩ := exceptional_quotient_block d g hB hS hc KD hKKD hcore hdis
  change (ChapterC.blockU K₀).map K₀.subtype = (D.V.subgroupOf J).map q at hlayer
  obtain ⟨hself,hctrl⟩ := exceptional_quotient_control d hmax h e hseed hn hU
    g hK hp a hi hS hsplit hcard KD hKKD hKD hcore hdis
  obtain ⟨R,hPR,hindex⟩ := SourceExceptionalQuotientSylow.exists_exceptional_quotient_sylow
    d h e hseed hn hU g hK hp a hi hcard KD hKD hcomp
  have hCL := SourcePairCentralizer.sylow_local_centralizer_eq_bot_of_generated_core d h e hseed hn hU
  have hT₀K := SourceExceptionalNormalizer.exceptional_sylow_centralizer_normalizes_pair
    d h e g hK hp a hi hS hsplit hCL hcard
  have hT₀V : T₀ ≤ normalizer (D.V : Set G) := by
    have hh := hT₀K.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
    rwa [show (pCore 2 K).map K.subtype = D.V from hS] at hh
  have hPN : P ≤ normalizer ((D.V.subgroupOf J).map q : Set (J ⧸ pCore 2 J)) := by
    have hnV : (T₀ ⊓ J).subgroupOf J ≤ normalizer (D.V.subgroupOf J : Set J) := by
      intro x hx
      exact D.V.le_normalizer_comap J.subtype (hT₀V hx.1)
    exact (map_mono hnV).trans ((D.V.subgroupOf J).le_normalizer_map q)
  apply DeletedFive.no_deletedFive_normalizer hq.1 K₀ P hB₀ hcard₀ ?_ ?_ ?_ R hPR hindex
  · rw [hlayer]
    exact hself
  · rw [hlayer]
    exact hctrl
  · rw [hlayer]
    exact hPN


include d hmax in
/-- The original normal A₆ branch has Q=V. The exceptional order-two
centralizer is excluded in its actual component quotient by Theorem C. -/
theorem original_core_eq_module
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) : D.LT.pCoreIn 2 = D.V := by
  obtain ⟨a,g,-,-,hK,hL,hp,-,-,hi,hS⟩ :=
    SourceCoreCollapse.exists_original_collapsed_pair d h e hseed hn hU
  let K := NormalBranch.K D g.val
  let C := (D.T : Subgroup G) ⊓ centralizer (K : Set G)
  have hB := SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have hc := SourceFiveSpan.module_commutator d hK a hi h hL hseed
  have hsplit := SourceCoreSplit.core_eq_module_sup_centralizer h g hK hB hS hc
  have hbound : Nat.card C ≤ 2 :=
    SourcePairCentralizerBound.pair_centralizer_card_le_two_source d h e hseed hn hU g hK a hi hS
  by_cases hcard : Nat.card C = 2
  · obtain ⟨KD,hKKD,hKD,hcomp,hdis⟩ :=
      SourceExceptionalComponent.exceptional_component_exists d h e hseed hn hU g hK hL hp a hi hS hcard
    have hcore := (SourceExceptionalRadical.exceptional_radical_and_core
      d h e hseed hn hU g hK hL hp a hi hS hcard KD hKKD hKD hcomp hmax hdis).2.2.2
    exact (exceptional_impossible_of_component_core d hmax h e hseed hn hU
      g hK hL hp a hi hS hcard KD hKKD hKD hcomp hcore hdis).elim
  · have hpos : 0 < Nat.card C := Nat.card_pos
    have hC : C = ⊥ := card_eq_one.mp (by omega)
    change D.LT.pCoreIn 2 = D.V ⊔ C at hsplit
    simpa only [hC,sup_bot_eq] using hsplit

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalQuotient
end
