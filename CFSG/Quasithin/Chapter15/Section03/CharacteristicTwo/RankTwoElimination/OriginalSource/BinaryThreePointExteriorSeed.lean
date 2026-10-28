module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourStandardModel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreJoin
public import Theory.Representation.BinaryEndpointInduction.EndpointSingularSpace

/-!
# Singularity of the original natural seed in the whole exterior model

The three endpoint radical shears are in the commutator core of the actual
endpoint parabolic. Exact image transport lifts each to the original Q.
The original V lies in Z(Q), so all three shears fix its image. Their
literal exterior fixed space is singular. No seed-coordinate identification
or original point-kernel characteristicity is assumed.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open BinaryEndpointInduction
variable {G : Type*} [Group G] [Finite G]

private theorem core_map_injective
    {A D : Type*} [Group A] [Group D] [Finite A] [Finite D]
    (B : Subgroup A) (f : A →* D) (hf : Function.Injective f) :
    (LinearThree.commutatorCore B).map f=LinearThree.commutatorCore (B.map f) := by
  change (⁅B.pCoreIn 2,B⁆).map f=⁅(B.map f).pCoreIn 2,B.map f⁆
  rw [map_commutator,map_pCoreIn_of_injective 2 B f hf]

/-- For any actual whole exterior realization with the retained original
point quotient and endpoint marking, the original natural seed is singular. -/
theorem binary_three_original_exterior_seed_singular
    (L C W : Subgroup G) [IsElementaryAbelian 2 W] (hLC : L ≤ C)
    (K : Subgroup (C ⧸ pCore 2 C))
    (hBK : (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) ≤ K)
    (σ : Representation (ZMod 2) (C ⧸ pCore 2 C) (Additive W))
    (hσ : ∀ (x : C) (w : Additive W),
      ((σ (QuotientGroup.mk' (pCore 2 C) x) w).toMul : G)=x*(w.toMul:G)*(x:G)⁻¹)
    (eK : K ≃* SL(4,ZMod 2))
    (heK : (((L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))).subgroupOf K).map
      eK.toMonoidHom=endpointParabolic)
    (E : Additive W ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hE : ∀ (k : K) (w : Additive W),
      E (σ k.val w)=E w ᵥ* survivorModelMatrix false ((eK k)⁻¹))
    (w : Additive W) (hw : (w.toMul:G) ∈ coreCenter L) :
    Atlas.Order20160A8.Bivectors.pfaffian (E w)=0 := by
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (L.subgroupOf C).map q
  let D := B.subgroupOf K
  let Q := LinearThree.commutatorCore L
  have hcore : (Q.subgroupOf C).map q=LinearThree.commutatorCore B :=
    binary_three_original_core_image_of_le L C hLC q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  have hKD : (LinearThree.commutatorCore D).map K.subtype=LinearThree.commutatorCore B := by
    rw [core_map_injective D K.subtype K.subtype_injective,map_subgroupOf_eq_of_le hBK]
  have hEP : (LinearThree.commutatorCore D).map eK.toMonoidHom=
      LinearThree.commutatorCore endpointParabolic := by
    rw [core_map_injective D eK.toMonoidHom eK.injective,heK]
  apply exterior_singular_of_endpoint_fixed (E w)
  intro i
  have hi : endpointShear i ∈ (LinearThree.commutatorCore D).map eK.toMonoidHom := by
    rw [hEP]
    exact endpointShear_mem_commutator i
  obtain ⟨k,hk,hki⟩ := hi
  change eK k=endpointShear i at hki
  have hkB : (k : C ⧸ pCore 2 C) ∈ LinearThree.commutatorCore B :=
    hKD ▸ mem_map_of_mem K.subtype hk
  rw [←hcore] at hkB
  obtain ⟨a,ha,haq⟩ := hkB
  have hfix : σ k.val w=w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [←haq,hσ]
    obtain ⟨v,hv,hvw⟩ := hw
    have hcomm : (a:G)*(w.toMul:G)=(w.toMul:G)*(a:G) := by
      rw [←hvw]
      exact congrArg Subtype.val (mem_center_iff.mp hv ⟨a,ha⟩)
    rw [hcomm,mul_inv_cancel_right]
  have hh := hE k w
  rw [hfix,hki] at hh
  exact hh.symm

/-- The full original source gives the same whole-module alternatives, now
with the original center intersection singular in the exterior branch. -/
theorem binary_three_source_four_singular_model
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
    let B := (c.L.subgroupOf C).map q
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V C
    ∃ hW : IsElementaryAbelian 2 W,
      let := hW
      ∃ σ : Representation (ZMod 2) (C ⧸ pCore 2 C) (Additive W),
        (∀ (x : C) (w : Additive W),
          ((σ (q x) w).toMul : G)=x*(w.toMul:G)*(x:G)⁻¹) ∧
        Function.Injective (σ.comp K.subtype) ∧
        σ.ker=centralizer (K : Set (C ⧸ pCore 2 C)) ∧
        ∃ eK : K ≃* SL(4,ZMod 2),
          (B.subgroupOf K).map eK.toMonoidHom=endpointParabolic ∧
          ((∃ E : Additive W ≃ₗ[ZMod 2] (Fin 4 → ZMod 2),
            ∀ (k : K) (w : Additive W),
              E (σ k.val w)=E w ᵥ* survivorModelMatrix true ((eK k)⁻¹)) ∨
          (∃ E : Additive W ≃ₗ[ZMod 2] (Fin 6 → ZMod 2),
            (∀ (k : K) (w : Additive W),
              E (σ k.val w)=E w ᵥ* survivorModelMatrix false ((eK k)⁻¹)) ∧
            ∀ w : Additive W, (w.toMul:G) ∈ coreCenter c.L →
              Atlas.Order20160A8.Bivectors.pfaffian (E w)=0)) := by
  obtain ⟨hW,σ,hσ,hinj,hker,eK,heK,dual,E,hE⟩ :=
    binary_three_source_four_standard_model
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  let := hW
  refine ⟨hW,σ,hσ,hinj,hker,eK,heK,?_⟩
  cases dual
  · exact Or.inr ⟨E,hE,binary_three_original_exterior_seed_singular
      c.L _ _ (le_sup_left.trans hLS) K hBK σ hσ eK heK E hE⟩
  · exact Or.inl ⟨E,hE⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
