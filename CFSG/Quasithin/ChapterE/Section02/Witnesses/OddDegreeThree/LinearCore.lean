module
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.NormalElementary
import all CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.NormalElementary
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Centralizer.Residual
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.Linear
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
/-!
# Elementary subgroups of the odd linear core above characteristic three

The involution centralizer has an SL₂ residual, which centralizes its two-core.
An outer involution commuting with both block root groups would square to the
marked inner involution, an impossibility. The elementary core subgroup is
therefore inner, where its residual centralizer is cyclic. Its order is at
most two. The original maximal subgroup and literal quotient maps are retained.

This extension excludes characteristic three: the corresponding local
four-group exists there. No TI or maximal-overgroup normalization is assumed.
Source: Aschbacher--Smith E.2.2(2d), E.2.7, printed pp.215--219.
-/
public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups IsMulCommutative
open Matrix.PSL3 Matrix.PSL3.OuterSolvable Matrix.PSL3.OddInvolutionFixed
open Matrix.PSL3.OddPrimeGraphExtension Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
open CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
open InnerGenerationGeometry
namespace CFSG.Quasithin.ChapterE.Structure.OddDegreeThree.LinearCore
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

private theorem core_centralizes_residual
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (z : graphExtension F) (hzI : z ∈ innerPart F) (hz : orderOf z = 2) :
    pCore 2 (centralizer ({z} : Set (graphExtension F))) ≤
      centralizer (solvableResidual (centralizer ({z} : Set (graphExtension F))) : Set _) := by
  let C := centralizer ({z} : Set (graphExtension F))
  let R := solvableResidual C
  obtain ⟨e⟩ := inner_centralizer_residual_equiv F ho hlarge z hzI hz
  let : IsQuasisimple R := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hlarge e
  let : IsSimpleGroup (R ⧸ center R) := IsQuasisimple.simple
  let : Nontrivial R := (QuotientGroup.mk'_surjective (center R)).nontrivial
  have hc : IsComponent C R := ⟨(inferInstance : R.Normal).isSubnormal, inferInstance⟩
  rcases hc.normal_dichotomy (pCore 2 C) with h | h
  · let : Group.IsNilpotent (pCore 2 C) := pCore_isPGroup.isNilpotent
    let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective (inclusion_injective h)
    exact (Group.IsPerfect.not_isSolvable R inferInstance).elim
  · apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]

omit [Finite F] in
private theorem standard_order_two (h2 : (2 : F) ≠ 0) : orderOf (standardInner F) = 2 :=
  orderOf_eq_prime (by
    simpa only [standardInner, ← map_pow, map_one] using
      congrArg (innerSL F) (SL3.standardInvolution_sq F))
    (NormalElementary.standardInner_ne_one F h2)

private noncomputable def blockSL (h2 : (2 : F) ≠ 0) :
    SL(2,F) →* centralizer ({standardInner F} : Set (graphExtension F)) :=
  ((innerSL F).comp ((SL3.blockEmbedding F).comp SpecialLinearGroup.toGL)).codRestrict _
    (fun x => NormalElementary.block_mem_centralizer F h2 (SpecialLinearGroup.toGL x))

private theorem blockSL_commutes_core
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (a : graphExtension F)
    (ha : a ∈ (centralizer ({standardInner F} : Set (graphExtension F))).pCoreIn 2)
    (x : SL(2,F)) :
    Commute (innerSL F (SL3.blockEmbedding F (SpecialLinearGroup.toGL x))) a := by
  let C := centralizer ({standardInner F} : Set (graphExtension F))
  let f := blockSL F h2
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  have hfr := le_solvableResidual_of_isPerfect f.range
  have hcomm := core_centralizes_residual F ho hlarge (standardInner F)
    (innerSL_range F ▸ ⟨_, rfl⟩) (standard_order_two F h2)
  obtain ⟨b,hb,rfl⟩ := ha
  exact congrArg Subtype.val (hcomm hb (f x) (hfr ⟨x,rfl⟩))

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem block_transvection_01 :
    SL3.blockEmbedding F (SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : F))) =
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F) := by
  apply Subtype.ext
  change SL3.blockMatrix F _ = Matrix.transvection _ _ (1 : F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SL3.blockMatrix, SpecialLinearGroup.toGL, SpecialLinearGroup.transvection,
      Matrix.transvection, GeneralLinearGroup.det, Matrix.det_fin_two]

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem block_transvection_10 :
    SL3.blockEmbedding F (SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : F))) =
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F) := by
  apply Subtype.ext
  change SL3.blockMatrix F _ = Matrix.transvection _ _ (1 : F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SL3.blockMatrix, SpecialLinearGroup.toGL, SpecialLinearGroup.transvection,
      Matrix.transvection, GeneralLinearGroup.det, Matrix.det_fin_two]

private theorem elementary_core_le_inner
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (A : Subgroup (graphExtension F)) [IsElementaryAbelian 2 A]
    (hcore : A ≤ (centralizer ({standardInner F} : Set (graphExtension F))).pCoreIn 2) :
    A ≤ innerPart F := by
  intro a ha
  by_contra hai
  obtain ⟨g,hg⟩:=NormalElementary.outer_coordinates F a hai
  have hgC:innerSL F g∈centralizer ({standardInner F}:Set (graphExtension F)) := by
    have hh:=(centralizer ({standardInner F}:Set (graphExtension F))).mul_mem
      ((pCoreIn_le _ _) (hcore ha)) ((centralizer ({standardInner F}:Set (graphExtension F))).inv_mem
        (graphElement_centralizes_standard F))
    simpa only [hg,mul_inv_cancel_right] using hh
  have hgSL:g∈centralizer ({SL3.standardInvolution F}:Set SL(3,F)) := by
    apply mem_centralizer_singleton_iff.mpr
    apply commutes_of_projective_commutes _ _ (SL3.standardInvolution_sq F)
    have hh:=mem_centralizer_singleton_iff.mp hgC
    have he := NormalElementary.projection_eq_of_innerSL_eq F
      ((map_mul (innerSL F) g _).trans (hh.trans (map_mul (innerSL F) _ g).symm))
    simpa only [map_mul] using he
  obtain ⟨B,hB⟩:=(SL3.blockEmbedding_range F h2 ▸ hgSL)
  have h01 := blockSL_commutes_core F ho hlarge h2 a (hcore ha)
    (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : F))
  rw [block_transvection_01] at h01
  have h10 := blockSL_commutes_core F ho hlarge h2 a (hcore ha)
    (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : F))
  rw [block_transvection_10] at h10
  rw [hg,←hB] at h01 h10
  have he01:=NormalElementary.block_root_equation F B (show (0:Fin 3)≠1 by decide) (by decide) (by decide) 1 h01
  have he10:=NormalElementary.block_root_equation F B (show (1:Fin 3)≠0 by decide) (by decide) (by decide) 1 h10
  have h00:B.val 0 0=0 := by
    have hh:=congrArg (fun x:SL(3,F)=>x.val 1 0) he10
    change (SL3.blockMatrix F B*(1+single (0:Fin 3) (1:Fin 3) (-1:F))) 1 0=
      ((1+single (1:Fin 3) (0:Fin 3) (1:F))*SL3.blockMatrix F B) 1 0 at hh
    simp [SL3.blockMatrix,Matrix.mul_apply,Fin.sum_univ_three] at hh
    exact hh
  have h11:B.val 1 1=0 := by
    have hh:=congrArg (fun x:SL(3,F)=>x.val 0 1) he01
    change (SL3.blockMatrix F B*(1+single (1:Fin 3) (0:Fin 3) (-1:F))) 0 1=
      ((1+single (0:Fin 3) (1:Fin 3) (1:F))*SL3.blockMatrix F B) 0 1 at hh
    simp [SL3.blockMatrix,Matrix.mul_apply,Fin.sum_univ_three] at hh
    exact hh
  have h10:B.val 1 0= -B.val 0 1 := by
    have hh:=congrArg (fun x:SL(3,F)=>x.val 0 0) he01
    change (SL3.blockMatrix F B*(1+single (1:Fin 3) (0:Fin 3) (-1:F))) 0 0=
      ((1+single (0:Fin 3) (1:Fin 3) (1:F))*SL3.blockMatrix F B) 0 0 at hh
    simpa [SL3.blockMatrix,Matrix.mul_apply,Fin.sum_univ_three,h00] using hh.symm
  have ht:SpecialLinearGroup.transpose g=SL3.standardInvolution F*g := by
    apply Subtype.ext
    rw [←hB]
    change (SL3.blockMatrix F B).transpose=(SL3.standardInvolution F).val*SL3.blockMatrix F B
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SL3.blockMatrix,SL3.standardInvolution,Matrix.mul_apply,Fin.sum_univ_three,h00,h11,h10]
  have he:g*graphSL F g=SL3.standardInvolution F := by
    change g*(SpecialLinearGroup.transpose g)⁻¹=SL3.standardInvolution F
    rw [ht,_root_.mul_inv_rev,←mul_assoc,mul_inv_cancel,one_mul]
    exact (eq_inv_of_mul_eq_one_left ((pow_two _).symm.trans (SL3.standardInvolution_sq F))).symm
  have hgraph:(graphElement F)^2=1 := Subtype.ext (graph_sq F)
  have ha2:a^2=standardInner F := by
    rw [hg]
    calc
      (innerSL F g*graphElement F)^2=
        innerSL F g*(graphElement F*innerSL F g*(graphElement F)⁻¹)*(graphElement F)^2 := by
          simp only [pow_two]; group
      _=innerSL F (g*graphSL F g) := by rw [←innerSL_graph,hgraph,mul_one,map_mul]
      _=standardInner F := by rw [he]; rfl
  exact NormalElementary.standardInner_ne_one F h2 (ha2.symm.trans (elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha))


private theorem standard_card_le_two
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (A : Subgroup (graphExtension F)) [IsElementaryAbelian 2 A]
    (hcore : A ≤ (centralizer ({standardInner F} : Set (graphExtension F))).pCoreIn 2) :
    Nat.card A ≤ 2 := by
  have h2 := Field.two_ne_zero_of_odd_card F ho
  let C := centralizer ({standardInner F} : Set (graphExtension F))
  let N := innerCentralizer F (standardInner F)
  have hzI : standardInner F ∈ innerPart F := innerSL_range F ▸ ⟨_,rfl⟩
  have hz := standard_order_two F h2
  have hAI := elementary_core_le_inner F ho hlarge h2 A hcore
  have hAC : A ≤ C := hcore.trans (pCoreIn_le _ _)
  let f : A →* N :=
    { toFun a := ⟨⟨a.val,hAC a.property⟩,hAI a.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hcomm := core_centralizes_residual F ho hlarge (standardInner F) hzI hz
  let : Group.IsNilpotent (C ⧸ N) := (innerCentralizer_quotient F (standardInner F)).isNilpotent
  have hmap : (solvableResidual N).map N.subtype = solvableResidual C :=
    map_solvableResidual_eq_of_solvable_quotient N
  let : IsCyclic (centralizer (solvableResidual N : Set N)) :=
    innerCentralizer_residual_centralizer_cyclic F ho hlarge (standardInner F) hzI hz
  have hf (a : A) : f a ∈ centralizer (solvableResidual N : Set N) := by
    intro r hr
    have ha : (f a).val ∈ pCore 2 C := by
      obtain ⟨b,hb,he⟩ := hcore a.property
      have he' : b = (f a).val := Subtype.ext he
      exact he' ▸ hb
    apply Subtype.ext
    have hh := hcomm ha r.val (hmap ▸ mem_map_of_mem N.subtype hr)
    exact hh
  let j := f.codRestrict _ hf
  have hj : Function.Injective j := by
    intro a b h
    exact Subtype.ext (congrArg (fun x => x.val.val.val) h)
  let : IsCyclic A := isCyclic_of_injective j hj
  have hd : Nat.card A ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 A
  exact Nat.le_of_dvd (by decide) hd

/-- Above characteristic three, every elementary subgroup of the actual
involution-centralizer two-core has at most two elements. -/
theorem card_le_two_of_inner_involution
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (z : graphExtension F) (hz : orderOf z = 2) (hzI : z ∈ innerPart F)
    (A : Subgroup (graphExtension F)) [IsElementaryAbelian 2 A]
    (hcore : A ≤ (centralizer ({z} : Set (graphExtension F))).pCoreIn 2) :
    Nat.card A ≤ 2 := by
  obtain ⟨s,hs⟩ := exists_standard_coordinates F (Field.two_ne_zero_of_odd_card F ho) z hz hzI
  let e := MulAut.conj (innerSL F s)⁻¹
  have he : e z = standardInner F := by
    rw [←hs]
    dsimp [e]
    simp only [inv_inv]
    group
  let A' := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map e.toMonoidHom
  have hC : (centralizer ({z} : Set (graphExtension F))).map e.toMonoidHom =
      centralizer ({standardInner F} : Set (graphExtension F)) := by
    rw [NormalElementary.map_centralizer_singleton,he]
  have hmap : ((centralizer ({z} : Set (graphExtension F))).pCoreIn 2).map e.toMonoidHom ≤
      ((centralizer ({z} : Set (graphExtension F))).map e.toMonoidHom).pCoreIn 2 := by
    let C := centralizer ({z} : Set (graphExtension F))
    let f := e.toMonoidHom.subgroupMap C
    have h : (pCore 2 C).map f ≤ pCore 2 (C.map e.toMonoidHom) :=
      le_sSup ⟨Normal.map inferInstance f (e.toMonoidHom.subgroupMap_surjective C),
        pCore_isPGroup.map f⟩
    have hm := map_mono (f := (C.map e.toMonoidHom).subtype) h
    have he : (C.map e.toMonoidHom).subtype.comp f = e.toMonoidHom.comp C.subtype := by ext x; rfl
    simpa only [pCoreIn,Subgroup.map_map,he] using hm
  have hc := standard_card_le_two F ho hlarge A'
    ((map_mono hcore).trans (hC ▸ hmap))
  rwa [card_map_of_injective e.injective] at hc

end CFSG.Quasithin.ChapterE.Structure.OddDegreeThree.LinearCore

namespace CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem weak_map_core_le {Q : Type*} [Group Q] (f : H →* Q) (M : Subgroup H) :
    (M.pCoreIn 2).map f ≤ (M.map f).pCoreIn 2 := by
  let g := f.subgroupMap M
  have hc : (pCore 2 M).map g ≤ pCore 2 (M.map f) :=
    le_sSup ⟨Normal.map inferInstance g (f.subgroupMap_surjective M), pCore_isPGroup.map g⟩
  have hm := map_mono (f := (M.map f).subtype) hc
  have he : (M.map f).subtype.comp g = f.comp M.subtype := by ext x; rfl
  simpa only [pCoreIn,Subgroup.map_map,he] using hm

/-- The no-TI odd linear source bound away from the exceptional prime three. -/
theorem linear_elementary_card_le_two_of_three_lt
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p) (hm : ClassicalGroup.IsPSL K 3 p)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) : Nat.card A ≤ 2 := by
  obtain ⟨t,ht,_,_,hM,_⟩ := linear_involution_centralizer T hP K hgen hcore hp ho hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  obtain ⟨f,hf⟩ := linear_graph_extension T hP K hgen hcore hp ho hF e
  let A' := A.map f.toMonoidHom
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map f.toMonoidHom
  have hCM : (ChapterB.minimalParabolicMax T hP).map f.toMonoidHom =
      centralizer ({f (t : H)} : Set (graphExtension F)) := by
    rw [hM,NormalElementary.map_centralizer_singleton]
  have hz : orderOf (f (t : H)) = 2 :=
    (orderOf_injective f.toMonoidHom f.injective (t : H)).trans
      ((orderOf_injective K.subtype K.subtype_injective t).trans ht)
  have hzI : f (t : H) ∈ innerPart F := hf ▸ mem_map_of_mem f.toMonoidHom t.property
  have hA' : A' ≤ (centralizer ({f (t : H)} : Set (graphExtension F))).pCoreIn 2 := by
    rw [← hCM]
    exact (map_mono hA).trans (weak_map_core_le f.toMonoidHom _)
  have hc := LinearCore.card_le_two_of_inner_involution F (hF ▸ ho) (hF ▸ hp3)
    _ hz hzI A' hA'
  rwa [card_map_of_injective f.injective] at hc

omit [Finite H] in
/-- The same bound through the literal source quotient map. -/
theorem linear_image_card_le_two_of_three_lt
    (M V : Subgroup H) [IsElementaryAbelian 2 V] (hVcore : V ≤ M.pCoreIn 2)
    {Q : Type*} [Group Q] [Finite Q] (f : H →* Q)
    (Tq : Sylow 2 Q) (hPq : ChapterB.IsMinimalParabolicOver Tq ⊤)
    (K : Subgroup Q) [K.Normal] [IsSimpleGroup K]
    (hgen : K ⊔ (Tq : Subgroup Q) = ⊤) (hcore : pCore 2 Q = ⊥)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p) (hm : ClassicalGroup.IsPSL K 3 p)
    (hM : M.map f = ChapterB.minimalParabolicMax Tq hPq) : Nat.card (V.map f) ≤ 2 := by
  let : IsElementaryAbelian 2 (V.map f) := IsElementaryAbelian.map f
  apply linear_elementary_card_le_two_of_three_lt Tq hPq K hgen hcore hp ho hp3 hm (V.map f)
  rw [←hM]
  exact (map_mono hVcore).trans (weak_map_core_le f M)
end CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
