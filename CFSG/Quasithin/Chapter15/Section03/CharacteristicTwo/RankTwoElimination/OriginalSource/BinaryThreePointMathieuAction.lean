module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointMathieuCore
public import Theory.Representation.Mathieu.M23InvolutionDisplacement
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# The actual M23 point action and its involution displacement

The literal conjugate span of the original natural eight is central in the
full point kernel. Its action descends through that kernel and is faithful
on the given M23 containing component. The prime23 degree bound and native
three-conjugate theorem apply to this same module, including its fixed layers.
No upper displacement bound or carrier exclusion is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open Sporadic.Mathieu
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

private theorem elementary_m23_bounds
    {X W : Type*} [Group X] [Finite X] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (K : Subgroup X)
    (ρ : X →* MulAut W) (hinj : Function.Injective (ρ.comp K.subtype))
    (eK : K ≃* M23) :
    let σ := elementaryRepresentation (p := 2) ρ
    let τ := σ.comp K.subtype
    Function.Injective τ ∧ 11 ≤ Module.finrank (ZMod 2) (Additive W) ∧
      2048 ≤ Nat.card W ∧ ∀ k : K, orderOf k = 2 →
        4 ≤ Module.finrank (ZMod 2) (τ k - LinearMap.id).range := by
  let σ := elementaryRepresentation (p := 2) ρ
  let τ := σ.comp K.subtype
  have hτ : Function.Injective τ := by
    intro x y hh
    apply hinj
    apply MulEquiv.ext
    intro w
    exact Additive.ofMul.injective (LinearMap.congr_fun hh (Additive.ofMul w))
  have hd : 11 ≤ Module.finrank (ZMod 2) (Additive W) := by
    have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank τ hτ
      (by decide : Nat.Prime 23) (by decide : 23 ≠ 2)
      (show 23 ∣ Nat.card K from by rw [Nat.card_congr eK.toEquiv,m23_order]; norm_num)
    simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_twentyThree] using hh
  have hcard : 2048 ≤ Nat.card W := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
    change 2048 ≤ Nat.card (Additive W)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact hh
  refine ⟨hτ,hd,hcard,?_⟩
  intro k hk
  have hs := Representation.MathieuSmall.m23_involution_displacement_ge_four
    (τ.comp eK.symm.toMonoidHom) (hτ.comp eK.symm.injective) (eK k)
    ((orderOf_injective eK.toMonoidHom eK.injective k).trans hk)
  change 4 ≤ Module.finrank (ZMod 2) (τ (eK.symm (eK k)) - LinearMap.id).range at hs
  rwa [eK.symm_apply_apply] at hs


variable {G : Type*} [Group G] [Finite G]

/-- The original M23 carrier acts faithfully on the literal central span;
its dimension is at least eleven and every involution moves at least four. -/
theorem binary_three_source_m23_span_action
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
    (hK : K.IsCComponent)
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (eK : K ≃* M23) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V C
    ∃ hW : IsElementaryAbelian 2 W,
      let := hW
      ∃ σ : Representation (ZMod 2) (C ⧸ pCore 2 C) (Additive W),
        let τ := σ.comp K.subtype
        Function.Injective τ ∧
        (∀ (x : C) (w : Additive W),
          ((σ (q x) w).toMul : G) = x * (w.toMul : G) * (x : G)⁻¹) ∧
        11 ≤ Module.finrank (ZMod 2) (Additive W) ∧ 2048 ≤ Nat.card W ∧
        ∀ k : K, orderOf k = 2 →
          4 ≤ Module.finrank (ZMod 2) (τ k - LinearMap.id).range := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 C)
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  obtain ⟨_,_,_,hWZ,hW⟩ := binary_three_source_m23_core_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hK hBK eK
  let := hW
  refine ⟨hW,?_⟩
  have hNW : N ≤ centralizer (W : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hWZ
    exact le_centralizer_iff.mp (hWZ.trans inf_le_right)
  have hCW : C ≤ normalizer W := le_normalizer_conjugateSpanBy V C
  have hVW : V ≤ W := le_conjugateSpanBy V C
  obtain ⟨ρ,hρ⟩ := quotient_span_action C W hCW hNW
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  let : IsSimpleGroup K := eK.isSimpleGroup
  let : Group.IsPerfect (c.L.subgroupOf (c.L ⊔ d.S)) := b.component.perfect
  let i := subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)
  let : Group.IsPerfect c.L := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
  let α := ρ.comp K.subtype
  have hinj : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    rcases (inferInstance : α.ker.Normal).eq_bot_or_eq_top with he | he
    · exact he
    · exfalso
      have hLV : c.L ≤ centralizer (V : Set G) := by
        intro l hl v hv
        let x : C := ⟨l,hLS (mem_sup_left hl)⟩
        let k : K := ⟨q x,hBK (mem_map_of_mem q hl)⟩
        have hk : ρ (q x)=1 := by
          change α k=1
          exact MonoidHom.mem_ker.mp (he ▸ mem_top k)
        have hh := hρ x ⟨v,hVW hv⟩
        rw [hk] at hh
        change v=l*v*l⁻¹ at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
      have hVL : ⁅V,c.L⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp hLV)
      have hzero : V=⊥ := commutator_eq_bot_of_iterated_eq_bot (coreCenter c.L) c.L hVL
      have hVcard : Nat.card V=8 := (binary_three_source_point_central_eight
        hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP).2.1
      rw [hzero,Subgroup.card_bot] at hVcard
      norm_num at hVcard
  obtain ⟨hτ,hd,hcard,hinv⟩ := elementary_m23_bounds K ρ hinj eK
  exact ⟨elementaryRepresentation (p := 2) ρ,hτ,(fun x w => hρ x w.toMul),hd,hcard,hinv⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
