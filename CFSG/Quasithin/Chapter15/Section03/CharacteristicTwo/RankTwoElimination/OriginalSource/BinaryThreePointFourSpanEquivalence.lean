module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourInducedCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourSpanRefined
public import Theory.Representation.BinaryEndpointInduction.QuotientRecognition
public import Theory.Representation.BinaryEndpointInduction.AmbientDisplacement

/-!
# Recognition of the whole original binary-four central span

The literal original component span is a nonzero quotient of the induced
endpoint coordinates. Its original component displacement has order at most
128. The exhaustive invariant-kernel certificate therefore gives the exact
four-space or six-space survivor, retaining the original quotient map and
all six marked actor equations. No whole-span module classification is
assumed as input.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open BinaryEndpointInduction
variable {G : Type*} [Group G] [Finite G]

private theorem parabolic_displacement_in_original
    {G X : Type*} [Group G] [Group X]
    (C L W : Subgroup G) [IsElementaryAbelian 2 W]
    (q : C →* X) (hLC : L ≤ C) (B K : Subgroup X)
    (hB : B=(L.subgroupOf C).map q)
    (σ : Representation (ZMod 2) X (Additive W))
    (D : Submodule (ZMod 2) (Additive W))
    (hD : ∀ (l : L) (w : Additive W), σ (q ⟨l,hLC l.property⟩) w-w ∈ D)
    (eK : K ≃* SL(4,ZMod 2))
    (heK : (B.subgroupOf K).map eK.toMonoidHom=endpointParabolic)
    (dual : Bool) (F : (Fin 45 → ZMod 2) →ₗ[ZMod 2] Additive W)
    (hF : ∀ (a : Fin 6) (x : Fin 45 → ZMod 2),
      F (x ᵥ* inducedCosetMatrix dual a)=σ (eK.symm ((cosetActor a)⁻¹)).val (F x)) :
    ∀ k : Fin 4, ∀ x : Fin 45 → ZMod 2,
      F (x ᵥ* inducedCosetMatrix dual ⟨k.val+2,by omega⟩-x) ∈ D := by
  intro k x
  let u := eK.symm ((parabolicGenerator k)⁻¹)
  have hu : (u : X) ∈ B := by
    have hp : (parabolicGenerator k)⁻¹ ∈ (B.subgroupOf K).map eK.toMonoidHom := by
      rw [heK]
      exact endpointParabolic.inv_mem (parabolicGenerator_mem_endpoint k)
    obtain ⟨v,hv,he⟩ := hp
    have hvu : v=u := eK.injective (he.trans (eK.apply_symm_apply _).symm)
    exact hvu ▸ hv
  rw [hB] at hu
  obtain ⟨l,hl,hlq⟩ := hu
  let l' : L := ⟨l,hl⟩
  have hlC : (⟨(l' : G),hLC l'.property⟩ : C)=l := Subtype.ext rfl
  rw [map_sub,hF,cosetActor_parabolic]
  change σ u.val (F x)-F x ∈ D
  rw [←hlq,←hlC]
  exact hD l' (F x)

/-- The entire original central span is one of the two literal survivor
spaces, through an equivalence retaining its actual induced quotient map. -/
theorem binary_three_source_four_span_equivalence
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
          ∃ (dual : Bool) (F : (Fin 45 → ZMod 2) →ₗ[ZMod 2] Additive W)
            (E : Additive W ≃ₗ[ZMod 2] (Fin (if dual then 4 else 6) → ZMod 2)),
            Function.Surjective F ∧
            (∀ (a : Fin 6) (x : Fin 45 → ZMod 2),
              F (x ᵥ* inducedCosetMatrix dual a)=
                σ (eK.symm ((cosetActor a)⁻¹)).val (F x)) ∧
            (∀ x, E (F (x ᵥ* changeMatrix dual))=survivorProjection dual x) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  obtain ⟨hV,hW,hVW,σ,hinj,hσ,hker,_,eK,heK,dual,F,hF,hact⟩ :=
    binary_three_source_four_induced_cover
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  let := hV
  let := hW
  obtain ⟨_,hVcard,_,_,hCW,_⟩ := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hWcard : 8 ≤ Nat.card W := hVcard ▸ card_le_of_le hVW
  have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le (by decide) hWcard)
  obtain ⟨D,hDcard,hD⟩ := exists_ambient_displacement C W c.L q hLC (hLC.trans hCW) σ hσ
  have hbound := (binary_three_source_four_span_refined_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm).2
  have hdim : Module.finrank (ZMod 2) D ≤ 7 := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [Nat.card_zmod,hDcard] at he
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (he ▸ hbound)
  have hFker : ∀ k : Fin 2, ∀ x, x ∈ F.ker → x ᵥ* generator dual k ∈ F.ker := by
    intro k x hx
    rw [←inducedCosetMatrix_generators dual k]
    change F (x ᵥ* inducedCosetMatrix dual ⟨k.val,by omega⟩)=0
    rw [hact,show F x=0 from hx,map_zero]
  obtain ⟨E,hE⟩ := exists_survivor_equivalence dual F hF hFker D hdim
    (parabolic_displacement_in_original C c.L W q hLC B K rfl σ D hD eK heK dual F hact)
  exact ⟨hW,σ,hσ,hinj,hker,eK,heK,dual,F,E,hF,hact,hE⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
