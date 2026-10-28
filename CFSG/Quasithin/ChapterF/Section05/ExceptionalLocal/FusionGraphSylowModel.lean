module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionSylowModel

/-!
# The graph centralizer inside the marked binary Sylow subgroup

The fixed Heisenberg radical has three coordinates in the binary fixed field,
so has order eight. The fixed middle-block map is onto SL2 of that field,
and its upper subgroup has order two. Adjoining the graph coordinate doubles
the resulting order16 fixed upper subgroup. Thus the literal Tf transported
through the source completion has order32.

The existing required endpoint equivalence to (C2 × C2) × S4 then makes
this exact subgroup Sylow in either endpoint centralizer. That endpoint
structure remains an explicit independent source input here; this module
proves the local Sylow implication, not the endpoint recognition itself.

Source: Aschbacher--Smith F.4.37 and F.5.3, printed pp.293 and 300.
-/

@[expose] public noncomputable section
open Subgroup Matrix
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient UnitaryFourSylow
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => localSU F (form F σ hσ)
local notation "K" => FixedBy.subfield F σ

def graphFixedLocal : Subgroup L :=
  ((UnitaryFourOuter.matrixHom F σ hσ).comp (L).subtype).eqLocus (L).subtype

def graphFixedRadical : Subgroup (radical F σ hσ) :=
  (graphFixedLocal).comap (radical F σ hσ).subtype

private theorem fixed_radical_coordinates (r : radical F σ hσ) :
    r ∈ graphFixedRadical ↔
      σ (coordinatesOfRadical F σ hσ r).x = (coordinatesOfRadical F σ hσ r).x ∧
      σ (coordinatesOfRadical F σ hσ r).y = (coordinatesOfRadical F σ hσ r).y ∧
      σ (coordinatesOfRadical F σ hσ r).z = (coordinatesOfRadical F σ hσ r).z := by
  constructor
  · intro hr
    have he : UnitaryFourOuter.matrixHom F σ hσ r.val.val = r.val.val := hr
    exact ⟨congrArg (fun a => a.val.val 1 3) he,
      congrArg (fun a => a.val.val 2 3) he,congrArg (fun a => a.val.val 0 3) he⟩
  · intro hr
    obtain ⟨r,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective r
    change UnitaryFourOuter.matrixHom F σ hσ (radicalElement F σ hσ r) =
      radicalElement F σ hσ r
    have hx : σ r.x = r.x := hr.1
    have hy : σ r.y = r.y := hr.2.1
    have hz : σ r.z = r.z := hr.2.2
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [UnitaryFourOuter.matrixHom_apply,radicalElement,radicalMatrix,hx,hy,hz]

private def fixedRadicalEquiv : graphFixedRadical ≃ K × K × K where
  toFun r :=
    (⟨(coordinatesOfRadical F σ hσ r.val).x,(fixed_radical_coordinates r.val).mp r.property |>.1⟩,
      ⟨(coordinatesOfRadical F σ hσ r.val).y,(fixed_radical_coordinates r.val).mp r.property |>.2.1⟩,
      ⟨(coordinatesOfRadical F σ hσ r.val).z,(fixed_radical_coordinates r.val).mp r.property |>.2.2⟩)
  invFun v := ⟨radicalOfCoordinates F σ hσ
    ⟨v.1.val,v.2.1.val,v.2.2.val,by
      have h1 : σ v.1.val = v.1.val := v.1.property
      have h2 : σ v.2.1.val = v.2.1.val := v.2.1.property
      have h3 : σ v.2.2.val = v.2.2.val := v.2.2.property
      rw [h1,h2,h3,mul_comm v.1.val v.2.1.val]
      simp [CharTwo.add_self_eq_zero]⟩,
    (fixed_radical_coordinates _).mpr ⟨v.1.property,v.2.1.property,v.2.2.property⟩⟩
  left_inv r := by
    apply Subtype.ext
    exact (radicalCoordinatesEquiv F σ hσ).apply_symm_apply r.val
  right_inv v := by rfl

theorem graphFixedRadical_card : Nat.card graphFixedRadical = 8 := by
  rw [Nat.card_congr fixedRadicalEquiv, Nat.card_prod,Nat.card_prod]
  change Nat.card (PointLocal.FixedField 1) *
    (Nat.card (PointLocal.FixedField 1) * Nat.card (PointLocal.FixedField 1)) = 8
  rw [PointLocal.fixedField_card 1 hn]
  norm_num

def graphFixedMiddle : graphFixedLocal →* SpecialLinearGroup (Fin 2) K :=
  (middleSL F σ hσ).comp graphFixedLocal.subtype

private theorem leviSL_graph_fixed (B : SpecialLinearGroup (Fin 2) K) :
    leviSL F σ hσ B ∈ graphFixedLocal := by
  change UnitaryFourOuter.matrixHom F σ hσ (leviSL F σ hσ B).val =
    (leviSL F σ hσ B).val
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp only [UnitaryFourOuter.matrixHom_apply, leviSL_val]
  have hf (i j : Fin 2) : σ (B.val i j).val = (B.val i j).val := (B.val i j).property
  fin_cases i <;> fin_cases j <;> simp [leviMatrix,hf]

theorem graphFixedMiddle_surjective : Function.Surjective graphFixedMiddle := by
  intro B
  exact ⟨⟨leviSL F σ hσ B,leviSL_graph_fixed B⟩,middleSL_leviSL F σ hσ B⟩

private def graphFixedMiddleKerEquiv : graphFixedMiddle.ker ≃ graphFixedRadical where
  toFun r := ⟨⟨r.val.val,(middleSL_ker F σ hσ).le r.property⟩,r.val.property⟩
  invFun r := ⟨⟨r.val.val,r.property⟩,(middleSL_ker F σ hσ).ge r.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem graphFixedMiddle_ker_card : Nat.card graphFixedMiddle.ker = 8 :=
  (Nat.card_congr graphFixedMiddleKerEquiv).trans graphFixedRadical_card

def graphFixedUpper : Subgroup graphFixedLocal :=
  (SpecialLinearGroup.upperUnipotent K).comap graphFixedMiddle

theorem graphFixedUpper_card : Nat.card graphFixedUpper = 16 := by
  have hk : graphFixedMiddle.ker ≤ graphFixedUpper := ker_le_comap _ _
  have hc := (graphFixedMiddle.ker.subgroupOf graphFixedUpper).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv] at hc
  change Nat.card graphFixedMiddle.ker *
    graphFixedMiddle.ker.relIndex graphFixedUpper = _ at hc
  rw [relIndex_ker,graphFixedUpper,map_comap_eq_self_of_surjective graphFixedMiddle_surjective,
    SpecialLinearGroup.card_upperUnipotent,graphFixedMiddle_ker_card] at hc
  change 8 * Nat.card (PointLocal.FixedField 1) = _ at hc
  rw [PointLocal.fixedField_card 1 hn] at hc
  exact hc.symm

local notation "UM" => UnitaryFourOuter.extendedUpper F σ hσ
local notation "XM" => UnitaryFourOuter.Extension F σ hσ

def matrixUpperGraph : Subgroup UM :=
  (centralizer ({UnitaryFourOuter.sigma F σ hσ} : Set XM)).subgroupOf UM

private theorem matrix_commutes_graph_iff (a : XM) :
    a ∈ centralizer ({UnitaryFourOuter.sigma F σ hσ} : Set XM) ↔
      UnitaryFourOuter.matrixHom F σ hσ a.left = a.left := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have he := congrArg SemidirectProduct.left h
    simpa [UnitaryFourOuter.sigma,UnitaryFourOuter.action_generator,
      UnitaryFourOuter.matrixAut] using he.symm
  · intro h
    apply SemidirectProduct.ext
    · simpa [UnitaryFourOuter.sigma,UnitaryFourOuter.action_generator,
        UnitaryFourOuter.matrixAut] using h.symm
    · change a.right * UnitaryFourOuter.generator = UnitaryFourOuter.generator * a.right
      exact mul_comm _ _

private def matrixUpperGraphEquiv : matrixUpperGraph ≃ graphFixedUpper × UnitaryFourOuter.C2 where
  toFun a :=
    (⟨⟨⟨a.val.val.left,((mem_upper F σ hσ _).mp a.val.property).1⟩,
      (matrix_commutes_graph_iff _).mp a.property⟩,
      show middleSL F σ hσ _ ∈ SpecialLinearGroup.upperUnipotent K from
        (mem_upper F σ hσ _).mp a.val.property |>.2 |> (mem_localUpper F σ hσ _).mpr⟩,
      a.val.val.right)
  invFun a := ⟨⟨⟨a.1.val.val.val,a.2⟩,
    ⟨a.1.val.val,a.1.property,rfl⟩⟩,
      (matrix_commutes_graph_iff _).mpr a.1.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem matrixUpperGraph_card : Nat.card matrixUpperGraph = 32 := by
  rw [Nat.card_congr matrixUpperGraphEquiv,Nat.card_prod,graphFixedUpper_card]
  change 16 * Nat.card (ZMod 2) = 32
  norm_num

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

private def sourceUpperEquiv (hi : Function.Injective i) :
    UM ≃* Source.sylowImage c i :=
  ((UM).equivMapOfInjective (Extension.extensionProjection 1 hn)
    (Extension.extensionProjection_injective 1 hn)).trans
    ((subgroupOfEquivOfLe extendedUpper_le_overlap).symm.trans
      (((Extension.extendedUpper 1 hn).subgroupOf (Extension.overlap 1 hn)).equivMapOfInjective
        (i.comp c.middle) (fun _ _ he => c.middle_injective (hi he))))

private def matrixUpperGraphElement : UM :=
  ⟨UnitaryFourOuter.sigma F σ hσ,(upper F σ hσ).one_mem⟩

private theorem sourceUpperEquiv_graph (hi : Function.Injective i) :
    (sourceUpperEquiv c i hi matrixUpperGraphElement).val = Source.graphElement c i := by
  apply congrArg (i.comp c.middle)
  apply Subtype.ext
  exact Extension.extensionProjection_sigma 1 hn

private def sourceTfEquiv (hi : Function.Injective i) : matrixUpperGraph ≃ Tf c i where
  toFun a := ⟨⟨(sourceUpperEquiv c i hi a.val).val,
    mem_centralizer_singleton_iff.mpr (by
      let f := (Source.sylowImage c i).subtype.comp (sourceUpperEquiv c i hi).toMonoidHom
      have hc : a.val * matrixUpperGraphElement = matrixUpperGraphElement * a.val :=
        Subtype.ext (mem_centralizer_singleton_iff.mp a.property)
      have hf : f matrixUpperGraphElement = Source.graphElement c i :=
        sourceUpperEquiv_graph c i hi
      have he : f a.val * f matrixUpperGraphElement = f matrixUpperGraphElement * f a.val := by
        simpa only [map_mul] using congrArg f hc
      rw [hf] at he
      exact he)⟩,(sourceUpperEquiv c i hi a.val).property⟩
  invFun a := ⟨(sourceUpperEquiv c i hi).symm ⟨a.val.val,a.property⟩,by
    apply mem_centralizer_singleton_iff.mpr
    change (((sourceUpperEquiv c i hi).symm ⟨a.val.val,a.property⟩ *
      matrixUpperGraphElement : UM).val) =
      ((matrixUpperGraphElement * (sourceUpperEquiv c i hi).symm ⟨a.val.val,a.property⟩ : UM).val)
    apply congrArg (fun x : UM => x.val)
    apply (sourceUpperEquiv c i hi).injective
    apply Subtype.ext
    simpa only [map_mul,MulEquiv.apply_symm_apply,Subgroup.coe_mul,
      sourceUpperEquiv_graph] using
      mem_centralizer_singleton_iff.mp a.val.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (sourceUpperEquiv c i hi).symm_apply_apply a.val
  right_inv a := by
    have he := congrArg (fun x : Source.sylowImage c i => x.val)
      ((sourceUpperEquiv c i hi).apply_symm_apply ⟨a.val.val,a.property⟩)
    exact Subtype.ext (Subtype.ext he)

/-- The literal Tf in the source involution centralizer has order32. -/
theorem source_Tf_card (hi : Function.Injective i) : Nat.card (Tf c i) = 32 :=
  (Nat.card_congr (sourceTfEquiv c i hi).symm).trans matrixUpperGraph_card

/-- The endpoint model of order96 makes the computed Tf its actual Sylow.
The endpoint structure producer supplies this order; no ambient Sylow premise
is used in this local comparison. -/
theorem source_Tf_sylow_of_endpoint_card (hi : Function.Injective i) (b : Bool)
    (hE : Nat.card (E c i b) = 96) :
    ∃ S : Sylow 2 (E c i b), (S : Subgroup (E c i b)).map (E c i b).subtype = TfImage c i := by
  let H := (TfImage c i).subgroupOf (E c i b)
  have hH : Nat.card H = 32 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (TfImage_le_E c i b)).toEquiv]
    change Nat.card ((Tf c i).map (C c i).subtype) = 32
    rw [card_map_of_injective (C c i).subtype_injective,source_Tf_card c i hi]
  have hp : IsPGroup 2 H := IsPGroup.of_card (n := 5) hH
  have hodd : ¬ 2 ∣ H.index := by
    have he := H.card_mul_index
    rw [hH,hE] at he
    have hind : H.index = 3 := by omega
    rw [hind]; decide
  exact ⟨hp.toSylow hodd,map_subgroupOf_eq_of_le (TfImage_le_E c i b)⟩

/-- Apply the exact endpoint equivalence already required by F5's normalizer
calculation to remove the local Tf-Sylow obligation. -/
theorem source_Tf_sylow_of_endpoint_equiv (hi : Function.Injective i) (b : Bool)
    (e : E c i b ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × Equiv.Perm (Fin 4)) :
    ∃ S : Sylow 2 (E c i b), (S : Subgroup (E c i b)).map (E c i b).subtype = TfImage c i := by
  apply source_Tf_sylow_of_endpoint_card c i hi b
  rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_prod]
  change Nat.card (ZMod 2) * Nat.card (ZMod 2) * Nat.card (Equiv.Perm (Fin 4)) = 96
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
