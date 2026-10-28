module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourSylowAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourPhiCentralizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralEight
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointKernelResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalMiddleStructure

/-!
# Refined displacement bound from the actual Sylow-fixed line

The actual central span meets the intrinsic four in at most a line.
Therefore [W,L] intersect Phi(Q) is a proper subgroup of Z(Q): equality
would place the entire intrinsic four inside W. Its order is at most16.
The literal proper image in the marked dual-pair still has order at most8,
so the full original source gives |[W,L]|≤128. No splitting or whole-span
dimension assertion is used.

The private proper-double argument is reproduced from the frozen
BinaryThreePointFourSpanBound owner to retain that owner's public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem proper_double_card_le
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) A V) [IsIrreducible σ]
    (U : Subrepresentation (σ.prod σ)) (hU : U ≠ ⊤) :
    Nat.card U.toSubmodule ≤ Nat.card V := by
  let F : Subrepresentation σ := {
    toSubmodule := U.toSubmodule.map (LinearMap.fst (ZMod 2) V V)
    apply_mem_toSubmodule g := by
      rintro _ ⟨x,hx,rfl⟩
      exact ⟨(σ.prod σ) g x,U.apply_mem_toSubmodule g hx,rfl⟩ }
  let E : Subrepresentation σ := {
    toSubmodule := U.toSubmodule.comap (LinearMap.inr (ZMod 2) V V)
    apply_mem_toSubmodule g := by
      intro x hx
      have hh := U.apply_mem_toSubmodule g hx
      change (σ g 0,σ g x) ∈ U at hh
      change (0,σ g x) ∈ U
      simpa only [map_zero] using hh }
  rcases eq_bot_or_eq_top E with hE | hE
  · apply Nat.card_le_card_of_injective (fun x : U.toSubmodule => x.val.1)
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext hxy
    have hmem : x.val.2-y.val.2 ∈ E := by
      have hh := U.toSubmodule.sub_mem x.property y.property
      change (0,x.val.2-y.val.2) ∈ U
      change (x.val.1-y.val.1,x.val.2-y.val.2) ∈ U at hh
      simpa only [hxy,sub_self] using hh
    rw [hE] at hmem
    exact sub_eq_zero.mp hmem
  · rcases eq_bot_or_eq_top F with hF | hF
    · apply Nat.card_le_card_of_injective (fun x : U.toSubmodule => x.val.2)
      intro x y hxy
      apply Subtype.ext
      apply Prod.ext ?_ hxy
      have hx : x.val.1 ∈ F := ⟨x.val,x.property,rfl⟩
      have hy : y.val.1 ∈ F := ⟨y.val,y.property,rfl⟩
      rw [hF] at hx hy
      exact (show x.val.1=0 from hx).trans (show y.val.1=0 from hy).symm
    · exfalso
      apply hU
      apply top_unique
      intro x _
      have hx : x.1 ∈ F := hF ▸ Submodule.mem_top
      obtain ⟨y,hy,hyx⟩ := hx
      have hz : x.2-y.2 ∈ E := hE ▸ Submodule.mem_top
      have hh := U.toSubmodule.add_mem hy hz
      change (y.1+0,y.2+(x.2-y.2)) ∈ U at hh
      have hy2 : y.2+(x.2-y.2)=x.2 := by abel
      have hy1 : y.1=x.1 := by simpa only [LinearMap.fst_apply] using hyx
      have heq : (y.1+0,y.2+(x.2-y.2)) = x := Prod.ext (by simpa only [add_zero] using hy1) hy2
      exact heq ▸ hh

private theorem abelian_subgroup_double_section_bound
    {G A V : Type*} [Group G] [Finite G] [Group A]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {L D E T : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    [IsIrreducible σ] [IsMulCommutative T]
    (ha : Function.Surjective a) (hs : HasSectionModel L D E a (σ.prod σ))
    (hTD : T ≤ D) (hLT : L ≤ normalizer T)
    (hED : E ≤ centralizer (D : Set G)) (hne : ⁅D,D⁆ ≠ ⊥) :
    Nat.card T ≤ Nat.card V * Nat.card (T ⊓ E : Subgroup G) := by
  obtain ⟨hE,hLD,_,hn,e,he⟩ := hs
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' (E.subgroupOf D))
  have hk : p.ker = E.subgroupOf D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let U : Subrepresentation (σ.prod σ) := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 ((T.subgroupOf D).map p).toAddSubgroup'
    apply_mem_toSubmodule g := by
      intro v hv
      obtain ⟨l,rfl⟩ := ha g
      change Multiplicative.ofAdd v ∈ (T.subgroupOf D).map p at hv
      obtain ⟨x,hx,hv⟩ := hv
      let y := D.normalizerMonoidHom (inclusion hLD l) x
      have hyT : (y : G) ∈ T := (mem_normalizer_iff.mp (hLT l.property) x).mp hx
      change Multiplicative.ofAdd ((σ.prod σ) (a l) v) ∈ (T.subgroupOf D).map p
      refine ⟨y,hyT,?_⟩
      apply Multiplicative.toAdd.injective
      have hh := he l x y rfl
      change (p y).toAdd = (σ.prod σ) (a l) (p x).toAdd at hh
      rw [hh,hv]
      rfl }
  have hproper : U ≠ ⊤ := by
    intro htop
    have hgen : D = T ⊔ E := by
      apply le_antisymm ?_ (sup_le hTD hE)
      intro d hd
      have hv : (p ⟨d,hd⟩).toAdd ∈ U := htop ▸ Submodule.mem_top
      change p ⟨d,hd⟩ ∈ (T.subgroupOf D).map p at hv
      obtain ⟨t,ht,heq⟩ := hv
      have hz : (⟨d,hd⟩ : D) / t ∈ p.ker := by
        apply MonoidHom.mem_ker.mpr
        rw [map_div,heq,div_self']
      rw [hk] at hz
      have hh := (T ⊔ E).mul_mem (mem_sup_right hz) (mem_sup_left ht)
      change d / (t : G) * (t : G) ∈ T ⊔ E at hh
      simpa only [div_mul_cancel] using hh
    have hc : T ≤ centralizer (T : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hTc : T ≤ centralizer (D : Set G) := by
      apply le_centralizer_iff.mp
      rw [hgen]
      exact sup_le hc (hED.trans (centralizer_le hTD))
    have hDc : D ≤ centralizer (D : Set G) := hgen.le.trans (sup_le hTc hED)
    exact hne (commutator_eq_bot_iff_le_centralizer.mpr hDc)
  have hUcard := proper_double_card_le σ U hproper
  let f := p.comp (inclusion hTD)
  have hfr : f.range = (T.subgroupOf D).map p := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨inclusion hTD t,t.property,rfl⟩
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,hd⟩,rfl⟩
  have hfk : f.ker = (T ⊓ E).subgroupOf T := by
    ext x
    change p (inclusion hTD x) = 1 ↔ (x : G) ∈ T ⊓ E
    have hh : p (inclusion hTD x)=1 ↔ (x : G)∈E := by
      change inclusion hTD x ∈ p.ker ↔ _
      rw [hk]
      rfl
    exact hh.trans (and_iff_right x.property).symm
  have hcard : Nat.card T = Nat.card U.toSubmodule * Nat.card (T ⊓ E : Subgroup G) := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hfr,hfk,
      Nat.card_congr (subgroupOfEquivOfLe (show T ⊓ E ≤ T from inf_le_left)).toEquiv]
    rfl
  rw [hcard]
  exact Nat.mul_le_mul_right _ hUcard

/-- The literal Frattini kernel has at most16 elements, and the actual
four-row central span has at most128 L-displacements. -/
theorem binary_three_source_four_span_refined_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ C
    Nat.card (⁅W,c.L⁆ ⊓ frattiniIn (LinearThree.commutatorCore c.L) : Subgroup G) ≤ 16 ∧
      Nat.card (⁅W,c.L⁆ : Subgroup G) ≤ 128 := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let ZQ := sCenter Q
  let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ C
  let T := ⁅W,c.L⁆
  obtain ⟨_,_,_,hWcenter,hCW,hWe⟩ := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hLW : c.L ≤ normalizer W := hLC.trans hCW
  have hTW : T ≤ W := le_normalizer_iff_commutator_le_left.mp hLW
  have hWN : W ≤ N := hWcenter.trans (map_subtype_le _)
  have hWc : W ≤ centralizer (N : Set G) := by
    intro x hx
    obtain ⟨w,hw,rfl⟩ := hWcenter hx
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨y,hy⟩)
  have hPhiN : Phi ≤ N := binary_three_source_binary_phi_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hNL : ⁅N,c.L⁆ = Q ⊓ N := (binary_three_source_binary_kernel_residual
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm).1
  have hTQ : T ≤ Q := (commutator_mono hWN le_rfl).trans (hNL.le.trans inf_le_left)
  have hTD : T ≤ D := le_inf hTQ (hTW.trans (hWc.trans (centralizer_le hPhiN)))
  have hLT : c.L ≤ normalizer T := normalizer_commutator_ge_right _ _
  let : IsElementaryAbelian 2 W := hWe
  let : IsElementaryAbelian 2 T := IsElementaryAbelian.of_le hTW
  obtain ⟨hcenter,hderived⟩ := binary_three_large_distance_original_middle_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  change sCenter D = Phi at hcenter
  change Nat.card (⁅D,D⁆ : Subgroup G) = 8 at hderived
  have hPhiD : Phi ≤ centralizer (D : Set G) := by
    rw [←hcenter]
    rintro _ ⟨w,hw,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨y,hy⟩)
  have hne : ⁅D,D⁆ ≠ ⊥ := by
    intro hh
    rw [hh,Subgroup.card_bot] at hderived
    norm_num at hderived
  have hTZ : T ⊓ Phi ≤ ZQ := (inf_le_inf hTW le_rfl).trans
    ((binary_three_source_four_phi_centralizer
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm).2.2.2 W hWc)
  have hZcard : Nat.card ZQ = 32 := by
    rw [show ZQ = (center Q).map Q.subtype from rfl,card_map_of_injective Q.subtype_injective]
    exact (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.1
  obtain ⟨common⟩ := t.commonFacts hc
  let earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨_,hHcard,hHF⟩ := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  have hHZ : intrinsicFour c.L ≤ ZQ := by
    intro x hx
    refine ⟨⟨x,(hHF hx).1⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext ((hHF hx).2 y
      (((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)) y.property))
  have hWH := (binary_three_source_four_sylow_fixed_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm).2.2.2.2
  let A := T ⊓ Phi
  have hproper : A.subgroupOf ZQ ≠ ⊤ := by
    intro ht
    have hZA : ZQ ≤ A := subgroupOf_eq_top.mp ht
    have hHW : intrinsicFour c.L ≤ W := hHZ.trans (hZA.trans (inf_le_left.trans hTW))
    have he : W ⊓ intrinsicFour c.L=intrinsicFour c.L := inf_eq_right.mpr hHW
    change Nat.card (W ⊓ intrinsicFour c.L : Subgroup G) ≤ 2 at hWH
    rw [he,hHcard] at hWH
    omega
  have hker : Nat.card (T ⊓ Phi : Subgroup G) ≤ 16 := by
    have hi : 2 ≤ (A.subgroupOf ZQ).index := one_lt_index_of_ne_top hproper
    have hprod := (A.subgroupOf ZQ).card_mul_index
    have hcardA : Nat.card (A.subgroupOf ZQ)=Nat.card A :=
      Nat.card_congr (subgroupOfEquivOfLe hTZ).toEquiv
    rw [hcardA,hZcard] at hprod
    have hh := Nat.mul_le_mul_left (Nat.card A) hi
    rw [hprod] at hh
    change Nat.card A ≤ 16
    omega
  obtain ⟨a,_,hd,_⟩ := binary_three_large_distance_original_core_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  let : IsIrreducible BinaryLinearThree.W.dual := BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  let : Finite (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) := Module.finite_of_finite (ZMod 2)
  have hbound := abelian_subgroup_double_section_bound
    (a.surjective.comp (QuotientGroup.mk'_surjective _)) hd hTD hLT hPhiD hne
  have h8 : Nat.card (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,Subspace.dual_finrank_eq,
      Module.finrank_fin_fun]
    norm_num
  rw [h8] at hbound
  exact ⟨hker,hbound.trans ((Nat.mul_le_mul_left 8 hker).trans_eq (by norm_num))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
