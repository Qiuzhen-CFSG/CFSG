module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourFullAction
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Exact action kernel on the original binary-four central span

Conjugation descends through the actual point two-core because W lies in
its center. The original perfect component acts nontrivially on its moving
eight, so the simple containing carrier acts faithfully on W. The full
point quotient has precisely the component-centralizer as action kernel.
The representative equation retains the original ambient conjugation.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open BinaryLinear.OuterCyclic
private theorem quotient_span_action {G : Type*} [Group G]
    (C W : Subgroup G) (hCW : C ≤ normalizer W)
    (hNW : C.pCoreIn 2 ≤ centralizer (W : Set G)) :
    ∃ ρ : (C ⧸ pCore 2 C) →* MulAut W, ∀ (x : C) (w : W),
      (ρ (QuotientGroup.mk' (pCore 2 C) x) w : G)=x*(w : G)*(x : G)⁻¹ := by
  let a := W.normalizerMonoidHom.comp (inclusion hCW)
  have hk : pCore 2 C ≤ a.ker := by
    intro x hx
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (x : G)*(w : G)*(x : G)⁻¹=(w : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hNW (mem_map_of_mem C.subtype hx) w w.property).symm
  exact ⟨QuotientGroup.lift (pCore 2 C) a hk,fun _ _ => rfl⟩

variable {G : Type*} [Group G] [Finite G]

/-- The literal central span carries a faithful K action, with exactly
C_X(K) as the kernel of the full point quotient action. -/
theorem binary_three_source_four_central_span_action
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
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V C
    ∃ ρ : (C ⧸ pCore 2 C) →* MulAut W,
      (∀ (x : C) (w : W), (ρ (q x) w : G)=x*(w : G)*(x : G)⁻¹) ∧
      Function.Injective (ρ.comp K.subtype) ∧
      ρ.ker=centralizer (K : Set (C ⧸ pCore 2 C)) := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 C)
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  obtain ⟨_,hVcard,hVW,hWZ,hCW,_⟩ := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hNW : N ≤ centralizer (W : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hWZ
    exact le_centralizer_iff.mp (hWZ.trans inf_le_right)
  obtain ⟨ρ,hρ⟩ := quotient_span_action C W hCW hNW
  obtain ⟨_,_,_,a,_,_,_⟩ := binary_three_point_four_endpoint_equality d c.L b z hLS P hP K hBK hm
  let : IsSimpleGroup (PSL(4,ZMod 2)) := Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup (LinearGroup 4) := (projectiveEquivLinear (by decide : 0<4)).symm.isSimpleGroup
  let : IsSimpleGroup K := a.isSimpleGroup
  let : Group.IsPerfect (c.L.subgroupOf (c.L ⊔ d.S)) := b.component.perfect
  let i := subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)
  let : Group.IsPerfect c.L := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
  let σ := ρ.comp K.subtype
  have hinj : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with he | he
    · exact he
    · exfalso
      have hLV : c.L ≤ centralizer (V : Set G) := by
        intro l hl v hv
        let x : C := ⟨l,hLS (mem_sup_left hl)⟩
        let k : K := ⟨q x,hBK (mem_map_of_mem q hl)⟩
        have hk : ρ (q x)=1 := by
          change σ k=1
          exact MonoidHom.mem_ker.mp (he ▸ mem_top k)
        have hh := hρ x ⟨v,hVW hv⟩
        rw [hk] at hh
        change v=l*v*l⁻¹ at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
      have hVL : ⁅V,c.L⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp hLV)
      have hzero : V=⊥ := commutator_eq_bot_of_iterated_eq_bot (coreCenter c.L) c.L hVL
      change Nat.card V=8 at hVcard
      rw [hzero,Subgroup.card_bot] at hVcard
      norm_num at hVcard
  have hZfix := binary_three_source_component_centralizer_fixes_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK
  have hZker : centralizer (K : Set (C ⧸ pCore 2 C)) ≤ ρ.ker := by
    intro x hx
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C) x
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    rw [hρ]
    exact mul_inv_eq_iff_eq_mul.mpr
      (hZfix (mem_map_of_mem C.subtype hx) w w.property).symm
  have hker : ρ.ker=centralizer (K : Set (C ⧸ pCore 2 C)) := by
    apply le_antisymm ?_ hZker
    intro x hx
    have hsplit := binary_three_point_four_component_centralizer_product d c.L b z hLS P hP K hBK hm
    have hxsplit : x ∈ K ⊔ centralizer (K : Set (C ⧸ pCore 2 C)) := hsplit.symm ▸ mem_top x
    obtain ⟨k,hk,s,hs,rfl⟩ := mem_sup_of_normal_left.mp hxsplit
    have hkρ : ρ k=1 := by
      have hh : ρ (k*s)=1 := hx
      rw [map_mul,show ρ s=1 from hZker hs,mul_one] at hh
      exact hh
    have hk1 : k=1 := congrArg Subtype.val (hinj
      (show σ ⟨k,hk⟩=σ 1 from hkρ.trans (map_one σ).symm))
    simpa only [hk1,one_mul] using hs
  exact ⟨ρ,hρ,hinj,hker⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
