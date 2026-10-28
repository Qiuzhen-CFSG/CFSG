module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreStructure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFiniteModels
public import Theory.GroupTheory.PCoreFrattiniAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The actual point-kernel action in the binary degree-four/five rows

The original core has order 2^20 and its whole component-fixed factor has
order four. A binary degree-four/five containing component therefore cannot
centralize the point kernel: otherwise the kernel on the original core has
order at most four, whereas its two-group image has order at most 1024.
Burnside's Frattini kernel theorem makes the action on the actual point
kernel modulo its Frattini subgroup nontrivial. It descends through the
literal point quotient and is faithful on its simple containing component.

The representative equation retains the original conjugation action. No
self-centralization of the point kernel or normality of the original core
in the containing component is assumed. A dimension or marked-section
comparison for this Frattini module remains a separate source obligation.
Source: Aschbacher--Smith15.3.23, pp.1128--1129; the Burnside basis theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource LinearThree.Extension.SourceCases ChapterC BinaryMS.MS93

private theorem perfect_hom_to_two_group_trivial
    {A D : Type*} [Group A] [Group D] [Finite D] [Group.IsPerfect A]
    (hp : IsPGroup 2 D) (f : A →* D) : f = 1 := by
  let : Group.IsNilpotent D := hp.isNilpotent
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  rcases subsingleton_or_nontrivial f.range with hs | hn
  · let := hs
    ext a
    exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict a) 1)
  · exact (Group.IsPerfect.not_isSolvable f.range inferInstance).elim

private theorem faithful_kernel_action
    {C : Type*} [Group C] [Finite C] (K : Subgroup C) [Group.IsPerfect K]
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 C)))]
    (hmove : ¬ K ≤ centralizer (pCore 2 C : Set C)) :
    let N := pCore 2 C
    let q := QuotientGroup.mk' N
    ∃ ρ : K.map q →* MulAut (N ⧸ frattini N), Function.Injective ρ ∧
      ∀ k : K, ρ (q.subgroupMap K k) =
        quotientAut (frattini N) (MulAut.conjNormal (k : C)) := by
  let N := pCore 2 C
  let q := QuotientGroup.mk' N
  let r := q.subgroupMap K
  let a : K →* MulAut N := (MulAut.conjNormal : C →* MulAut N).comp K.subtype
  let f := (quotientAut (frattini N)).comp a
  let : Fact (IsPGroup 2 N) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 (N ⧸ frattini N) := isElementaryAbelian_quotient_frattini
  have hr : Function.Surjective r := q.subgroupMap_surjective K
  have hk : r.ker ≤ f.ker := by
    intro k hk
    have hn : (k : C) ∈ N := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hk)
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini N) v
    change quotientAut (frattini N) (MulAut.conjNormal (k : C)) _ = _
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini N) ((⟨k,hn⟩ : N) * x * (⟨k,hn⟩ : N)⁻¹) = _
    rw [map_mul,map_mul,map_inv,mul_comm (QuotientGroup.mk' (frattini N) (⟨k,hn⟩ : N))
      (QuotientGroup.mk' (frattini N) x),mul_inv_cancel_right]
    rfl
  let ρ : K.map q →* MulAut (N ⧸ frattini N) := r.liftOfSurjective hr ⟨f,hk⟩
  have he (k : K) : ρ (r k) = f k :=
    r.liftOfRightInverse_comp_apply (Function.surjInv hr)
      (Function.rightInverse_surjInv hr) ⟨f,hk⟩ k
  refine ⟨ρ,?_,he⟩
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker inferInstance with hb | ht
  · exact hb
  · exfalso
    have hf (k : K) : f k = 1 := (he k).symm.trans
      (MonoidHom.mem_ker.mp (ht ▸ mem_top (r k)))
    let a₀ : K →* (quotientAut (frattini N)).ker := a.codRestrict _ (fun k => hf k)
    have ha₀ := perfect_hom_to_two_group_trivial
      (isPGroup_quotientAut_frattini_kernel (pCore_isPGroup (p := 2) (G := C))) a₀
    apply hmove
    intro k hk n hn
    have hh := congrArg (fun j : K →* (quotientAut (frattini N)).ker =>
      (((j ⟨k,hk⟩ : MulAut N) ⟨n,hn⟩) : C)) ha₀
    change k*n*k⁻¹ = n at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem binary_two_subgroup_card_le
    {X : Type*} [Group X] [Finite X] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL X n 2) (E : Subgroup X) (hp : IsPGroup 2 E) :
    Nat.card E ≤ 1024 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let a := (e.trans (Atlas.fieldEquivPSL n f)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n))
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  apply (card_le_of_le hS).trans
  rw [S.card_eq_multiplicity]
  have hc : Nat.card X = ∏ i : Fin n, (2^n - 2^i.val) := by
    rw [Nat.card_congr a.toEquiv,←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
      Matrix.card_GL_field]
    simp
  rw [hc]
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] <;> decide +kernel

private theorem original_component_moves_point_kernel
    {G : Type*} [Group G] [Finite G] (L : Subgroup G) (z : G)
    (hLC : L ≤ centralizer ({z} : Set G))
    (hQ : Nat.card (LinearThree.commutatorCore L) = 1048576)
    (hF : Nat.card (coreFixed L) = 4)
    (K : Subgroup (centralizer ({z} : Set G))) (hLK : L.subgroupOf _ ≤ K)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) n 2) :
    ¬ K ≤ centralizer (pCore 2 (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) := by
  let C := centralizer ({z} : Set G)
  let N := pCore 2 C
  let q := QuotientGroup.mk' N
  let Q := LinearThree.commutatorCore L
  have hQL : Q ≤ L := (LinearThree.commutatorCore_le L).trans (L.pCoreIn_le 2)
  let j : Q →* K :=
    { toFun := fun x => ⟨⟨x,hLC (hQL x.property)⟩,hLK (hQL x.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f := (q.subgroupMap K).comp j
  have hqp : IsPGroup 2 Q := (L.isPGroup_pCoreIn 2).to_le (LinearThree.commutatorCore_le L)
  have hrp : IsPGroup 2 f.range := hqp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hrange : Nat.card f.range ≤ 1024 := binary_two_subgroup_card_le hn hm f.range hrp
  intro hcentral
  let k : f.ker →* coreFixed L :=
    { toFun := fun x => ⟨x.val,⟨x.val.property,by
        have hx : ((j x.val : K) : C) ∈ N :=
          (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val x.property)
        intro l hl
        exact (congrArg C.subtype
          (hcentral (hLK (show (⟨l,hLC hl⟩ : C) ∈ L.subgroupOf C from hl))
            ((j x.val : K) : C) hx)).symm⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : coreFixed L => (v : G)) hxy
  have hker : Nat.card f.ker ≤ 4 := hF ▸ Nat.card_le_card_of_injective k hk
  have hc := f.ker.card_mul_index
  rw [index_ker,hQ] at hc
  have hm := Nat.mul_le_mul hker hrange
  omega

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The same original point and containing binary carrier act faithfully on
its literal point-kernel Frattini section, with the original action equation. -/
theorem binary_three_source_point_kernel_action
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
    (K : Subgroup (centralizer ({z} : Set G))) (hK : K.IsCComponent)
    (hLK : c.L.subgroupOf _ ≤ K)
    (hsimple : IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) n 2) :
    let C := centralizer ({z} : Set G)
    let N := pCore 2 C
    let q := QuotientGroup.mk' N
    ∃ ρ : K.map q →* MulAut (N ⧸ frattini N), Function.Injective ρ ∧
      ∀ k : K, ρ (q.subgroupMap K k) =
        quotientAut (frattini N) (MulAut.conjNormal (k : C)) := by
  have hstruct := binary_three_large_distance_original_core_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hfixed := binary_three_large_distance_fixed_factor_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  let := hK.perfect
  let := hsimple
  exact faithful_kernel_action K (original_component_moves_point_kernel c.L z
    (le_sup_left.trans hLS) hstruct.2.2.2.1 hfixed.1 K hLK hn hm)

/-- The original finite-carrier packet retains its point, join quotient and
strict local inclusion, and equips either binary row with its faithful
actual point-kernel action. No faithfulness premise or callback is used. -/
theorem binary_three_large_distance_point_kernel_actions
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
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      primeRank 3 (C ⧸ pCore 2 C) = 2 ∧
      primeRank 3 (normalizer (B : Set (C ⧸ pCore 2 C))) ≤ 1 ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) : Subgroup _) ≤
          normalizer (B : Set (C ⧸ pCore 2 C)) ∧
        Nonempty (((B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
          Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C)) ⧸
          pCore 2 (B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
            Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C))) ≃*
          PSL(3,ZMod 2)) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B < K.map q ∧
          IsSimpleGroup (K.map q) ∧ BinaryThreeFiniteSimpleCarrier (K.map q) ∧
          (∀ n : ℕ, (n = 4 ∨ n = 5) → ClassicalGroup.IsPSL (K.map q) n 2 →
            ∃ ρ : K.map q →* MulAut ((pCore 2 C) ⧸ frattini (pCore 2 C)),
              Function.Injective ρ ∧ ∀ k : K, ρ (q.subgroupMap K k) =
                quotientAut (frattini (pCore 2 C)) (MulAut.conjNormal (k : C))) := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel⟩ :=
    binary_three_large_distance_point_finite_models
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb g hgT hgS
  refine ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel,?_⟩
  intro n hn hm
  exact binary_three_source_point_kernel_action hG d hempty hM hu hmany
    hI htwo hf c e b t hc hb z hLS K hK hLK hsimple hn hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
