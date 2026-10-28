module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CentralizingCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SplitImageRank
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OvergroupCoreSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModelSource.Geometry
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# The actual proper overcomponent in the centralizer reduction

The original single natural block and Sylow subgroup determine a normal
C-component in any proper local overgroup failing to normalize the block.
Core absorption and the split natural quotient promote that component to
an ordinary quasisimple component. The original torus action also selects
a bad central involution centralized by the entire original local group.

Source: Aschbacher–Smith, 2.4.11, printed p.531.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_proper_overcomponent
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (X : Subgroup G) (hX : X ∈ Chapter1.H G) (hHX : d.H ≤ X)
    (hnot : ¬ X ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    let L := d.block.map d.H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧ twoCore X ≤ (center L).map L.subtype ∧
      ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = (d.S : Subgroup d.H).map d.H.subtype ∧
        ∃ K : Subgroup X, K.IsCComponent ∧ K.Normal ∧ L < K.map X.subtype := by
  let L := d.block.map d.H.subtype
  have hLX : L ≤ X := (map_subtype_le _).trans hHX
  obtain ⟨hgam,⟨P,hP⟩,_⟩ := lemma_2_3_7_2 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl ⟨hX,hHX⟩
  have hcore := (source_overgroup_core_central_or_normalizes d hG T hST hsingle hL hM hTM hunique X hLX).resolve_right hnot
  have h3 : ¬ ChapterC.IsAlternatingBlock d.block 3 := by
    intro ha
    obtain ⟨e⟩ := ha.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable d.block := Group.isSolvable_of_isSolvable_injective (f:=e.toMonoidHom) e.injective
    exact hL.not_solvable
  let B := L.subgroupOf X
  have hBL : B ∈ Chapter1.L X (P : Subgroup X) := by
    apply (Chapter1.mem_L_map_iff X.subtype X.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hLX,hP]
    exact d.ambient_block_mem_L_of_not_three h3
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hHL : d.H ≤ normalizer (L : Set G) := by
    have hh := d.block.le_normalizer_map d.H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hPN : (P : Subgroup X) ≤ normalizer (B : Set X) := by
    apply le_normalizer_iff.mpr
    intro p hp b hb
    have hpH : (p:G) ∈ d.H := map_subtype_le _ (hP ▸ mem_map_of_mem X.subtype hp)
    exact (mem_normalizer_iff.mp (hHL hpH) (b:G)).mp hb
  obtain ⟨K,⟨hK,hBK,hKn⟩,_⟩ := Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hX) P hBL hPN
  have hLK : L ≤ K.map X.subtype := by
    rw [←map_subgroupOf_eq_of_le hLX]
    exact map_mono hBK
  have hXK : X ≤ normalizer (K.map X.subtype : Set G) := by
    let := hKn
    have hh := K.le_normalizer_map X.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  refine ⟨hgam,hcore,P,hP,K,hK,hKn,lt_of_le_of_ne hLK ?_⟩
  intro he
  exact hnot (he.symm ▸ hXK)

theorem source_proper_quasisimple_overcomponent
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (X : Subgroup G) (hX : X ∈ Chapter1.H G) (hHX : d.H ≤ X)
    (hnot : ¬ X ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    let L := d.block.map d.H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧ twoCore X ≤ (center L).map L.subtype ∧
      ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = (d.S : Subgroup d.H).map d.H.subtype ∧
        ∃ K : Subgroup X, Theory.GroupTheory.IsComponent X K ∧ K.Normal ∧
          L < K.map X.subtype ∧ pCore 2 X ≤ centralizer (K : Set X) := by
  let L := d.block.map d.H.subtype
  have hLX : L ≤ X := (map_subtype_le _).trans hHX
  obtain ⟨hgam,hcore,P,hP,K,hK,hKn,hLK⟩ :=
    source_proper_overcomponent d hG T hST hsingle hL hM hTM hunique X hX hHX hnot
  let B := L.subgroupOf X
  have hBK : B ≤ K := by
    intro b hb
    obtain ⟨k,hk,he⟩ := hLK.le hb
    exact (Subtype.ext he : k=b) ▸ hk
  let eB : B ≃* L := subgroupOfEquivOfLe hLX
  have hbl := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hB : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    let : Group.IsSolvable L := Group.isSolvable_of_surjective (f := eB.toMonoidHom) eB.surjective
    exact hbl.not_solvable
  have hBP : B ≤ centralizer (pCore 2 X : Set X) := by
    intro b hb p hp
    obtain ⟨z,hz,he⟩ := hcore (mem_map_of_mem X.subtype hp)
    have hh := congrArg Subtype.val (mem_center_iff.mp hz (⟨b,hb⟩ : L))
    apply Subtype.ext
    change (p:G)*(b:G)=(b:G)*(p:G)
    change (b:G)*(z:G)=(z:G)*(b:G) at hh
    change (z:G)=(p:G) at he
    rw [he] at hh
    exact hh.symm
  have hc := ChapterA.Section03.NoncentralFitting.component_centralizes_of_nonsolvable_subgroup
    K B (pCore 2 X) hK hBK hB hBP
  let q := QuotientGroup.mk' (pCore 2 X)
  let f : L →* K := (inclusion hBK).comp eB.symm.toMonoidHom
  let g := (q.subgroupMap K).comp f
  have hk : g.ker ≤ pCore 2 L := by
    intro l hl
    have he : q ((f l : K) : X)=1 := congrArg Subtype.val hl
    have hlQ : (l:G) ∈ twoCore X := mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff _).mp he)
    have hlU := (source_overgroup_core_le d hG T hST hsingle hL hM hTM hunique X hLX) hlQ
    rw [←(source_core_absorption d hG T hST hsingle hL hM hTM hunique).2] at hlU
    obtain ⟨a,ha,hea⟩ := hlU
    exact (Subtype.ext hea : a=l) ▸ ha
  obtain ⟨x,hx,hxs⟩ := SetLike.exists_of_lt hST
  have hsp := source_core_splits_of_outside d hG T hST hsingle hL hM hTM hunique x hx hxs
  have hr : 2 ≤ primeRank 2 (K.map q) :=
    (show 2 ≤ n by have hn:=hL.1;omega).trans (hbl.two_rank_ge_of_split_map hsp g hk)
  have hquasi := ChapterA.Section03.NoncentralFitting.quasisimple_of_core_centralizes_and_image_rank
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hX) K hK (le_centralizer_iff.mp hc) hr
  exact ⟨hgam,hcore,P,hP,K,⟨hK.subnormal,hquasi⟩,hKn,hLK,le_centralizer_iff.mp hc⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_center_centralizer_counterexample_choice
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (z : G) (hz : z ∈ (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype)
    (hz1 : z ≠ 1)
    (hnot : ¬ centralizer ({z} : Set G) ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    let L := d.block.map d.H.subtype
    ∃ u ∈ (center L).map L.subtype, orderOf u=2 ∧
      d.H ≤ centralizer ({u} : Set G) ∧
      centralizer ({u} : Set G) ∈ Chapter1.H G ∧
      ¬ centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  let L := d.block.map d.H.subtype
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let Z := (center L).map L.subtype
  let N := normalizer (L : Set G)
  have hZne : center L ≠ ⊥ := by
    intro he
    have hh : z ∈ Z := hz
    change z ∈ (center L).map L.subtype at hh
    rw [he,Subgroup.map_bot,mem_bot] at hh
    exact hz1 hh
  have hZn : Z ≠ ⊥ := fun he => hz1 (mem_bot.mp (he ▸ hz))
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hZQ : Z ≤ twoCore d.H := (map_mono (hK.center_le_module
    (source_block_core_eq_module d hG T hST hsingle))).trans_eq
      (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  have hZS : Z ≤ S := hZQ.trans (pCoreIn_le_sylow d.H d.S)
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hHN : d.H ≤ N := by
    have hh := d.block.le_normalizer_map d.H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hSN : S ≤ N := (map_subtype_le _).trans hHN
  have hSZ : S ≤ normalizer (Z : Set G) := hSN.trans
    (normalizer_le_normalizer_characteristic_image L (center L))
  let : (Z.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hSZ
  have hZSn : Z.subgroupOf S ≠ ⊥ := by
    intro he
    have hh := congrArg (map S.subtype) he
    rw [map_subgroupOf_eq_of_le hZS,Subgroup.map_bot] at hh
    exact hZn hh
  obtain ⟨u,hu1⟩ := ne_bot_iff_exists_ne_one.mp
    (center_inf_ne_bot_of_normal (d.S.isPGroup'.map d.H.subtype) (Z.subgroupOf S) hZSn)
  have huZ : ((u:S):G) ∈ Z := u.property.2
  have huG : ((u:S):G) ≠ 1 := fun he => hu1 (Subtype.ext (Subtype.ext he))
  have hSu : S ≤ centralizer ({((u:S):G)} : Set G) := by
    intro s hs
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp u.property.1 (⟨s,hs⟩ : S))
  have hLu : L ≤ centralizer ({((u:S):G)} : Set G) := by
    obtain ⟨v,hv,he⟩ := huZ
    intro l hl
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val (mem_center_iff.mp hv (⟨l,hl⟩ : L))
    change l*(v:G)=(v:G)*l at hh
    change (v:G)=((u:S):G) at he
    simpa only [he] using hh
  have hHu : d.H ≤ centralizer ({((u:S):G)} : Set G) := by
    have he : L ⊔ S=d.H := by simpa only [hsingle] using d.ambient_L0_sup_sylow
    exact he.ge.trans (sup_le hLu hSu)
  let : IsElementaryAbelian 2 (twoCore d.H) := (d.core_source hG T hST).2.2.2.1
  have huo : orderOf ((u:S):G)=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ (hZQ huZ)) huG
  obtain ⟨_,D,_hDM,_hcyc,_hcard,x,hx,hxs,hEL,hreg⟩ :=
    source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
  have hr := (hreg.resolve_left hZne).2.2
  obtain ⟨a,ha,_⟩ := hr ⟨z,hz⟩ (fun he => hz1 (congrArg Subtype.val he))
    ⟨u,huZ⟩ (fun he => huG (congrArg Subtype.val he))
  have haN : (a:G) ∈ N := hEL a.property
  refine ⟨u,huZ,huo,hHu,Chapter1.mem_H_of_isTwoLocal
    (Theory.GroupTheory.isTwoLocal_involution_centralizer huo),?_⟩
  intro hCu
  apply hnot
  intro c hc
  have hc' : (a:G)*c*(a:G)⁻¹ ∈ centralizer ({((u:S):G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have he := mem_centralizer_singleton_iff.mp hc
    rw [←ha]
    calc
      (a:G)*c*(a:G)⁻¹*((a:G)*z*(a:G)⁻¹) = (a:G)*(c*z)*(a:G)⁻¹ := by group
      _ = (a:G)*(z*c)*(a:G)⁻¹ := by rw [he]
      _ = (a:G)*z*(a:G)⁻¹*((a:G)*c*(a:G)⁻¹) := by group
  have hn := N.mul_mem (N.mul_mem (N.inv_mem haN) (hCu hc')) haN
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hn
end CFSG.Quasithin.Chapter2.LinearShadows.Single
