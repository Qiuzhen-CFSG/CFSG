module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryNatural
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterModel
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator

/-!
# The actual eight actor on the whole secondary module

The original hexacode chart uniquely determines its automizer embedding.
Consequently the original outer-model theorem gives the exact W image in
the same secondary action, up to its specified even relabeling. The proved
literal [VY,W,W]=1 transports to quadraticity on that full eight image.
All original kernels and whole-product coordinates are retained.

Source: Aschbacher--Smith12.7.18 and12.7.20, printed pp.845--846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual W-eight image and its quadratic action are retained in the
same full secondary module and the same original hexacode chart. -/
theorem original_tripleSix_central_closure_secondary_eight_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K)
    (hQ : (K ⊔ (T : Subgroup G)).pCoreIn 2 ≠ U) :
    let M := K ⊔ (T : Subgroup G)
    let X := tripleSixScalarResidual K
    let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
    let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
    let J := (U ⊔ V).subgroupOf M
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    ∃ (hr : IsPReduced 2 (V.subgroupOf M)) (hj : IsPReduced 2 J),
      letI := hr.elementary
      letI := hj.elementary
      ∃ (hMU : M ≤ normalizer (U : Set G)) (f : Automizer U →* HexAutomorphisms),
        Function.Bijective f ∧
        (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k,D.normalizes k.property⟩) =
          (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
        (∀ (b : Automizer U) (u : U),
          (tripleSixPointCoordinates D a (b.val u)).toAdd =
            Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) ∧
        (let π := f.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU))
         let q := hexCoordinateSixHom.comp π
         Function.Surjective π ∧ π.ker = pCore 2 M ∧ Function.Surjective q ∧
         q.ker = (X.subgroupOf M) ⊔ pCore 2 M ∧
         ∃ σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive (V.subgroupOf M)),
           (∃ r : alternatingGroup (Fin 6),
             (W.subgroupOf M).map ((MulAut.conj r.val).toMonoidHom.comp q) =
               DuadCalculation.productCore.map duadProductHom) ∧
           IsQuadratic σ ((W.subgroupOf M).map q) ∧
           Function.Injective σ ∧
           fixedSpace σ (alternatingGroup (Fin 6)) = ⊥ ∧
           subspaceCommutator σ ⊤ (alternatingGroup (Fin 6)) = ⊤ ∧
           IsIrreducible (σ.comp (alternatingGroup (Fin 6)).subtype) ∧
           Module.finrank (ZMod 2) (Additive (V.subgroupOf M)) = 4 ∧
           (Nonempty (σ.Equiv BinaryAlternatingSix.firstNatural) ∨
             Nonempty (σ.Equiv BinaryAlternatingSix.secondNatural)) ∧
           (∀ (m : M) (v : Additive (V.subgroupOf M)),
             ((σ (q m) v).toMul : M) = m * (v.toMul : M) * m⁻¹) ∧
           (∃ e : (hexacode × Additive (V.subgroupOf M)) ≃ₗ[ZMod 2] Additive J,
             ∀ (u : U) (v : V.subgroupOf M),
               (((e ((tripleSixPointCoordinates D a u).toAdd,Additive.ofMul v)).toMul : M) : G) =
                 (u : G) * (v : M)) ∧
           cubicRatio (Hexacode.action.prod (σ.comp hexCoordinateSixHom)) ≤ 2 ∧
           ∃ E : Subgroup HexAutomorphisms, IsElementaryTwo E ∧
             IsCubic (Hexacode.action.prod (σ.comp hexCoordinateSixHom)) E ∧
             ((E ≤ hexSign.ker ∧ rank E = 2 ∧ fixedCodim Hexacode.action E = 2 ∧
               fixedCodim σ (E.map hexCoordinateSixHom) = 2 ∧
               IsOffender σ (E.map hexCoordinateSixHom)) ∨
             (¬ E ≤ hexSign.ker ∧ rank E = 3 ∧ fixedCodim Hexacode.action E = 4 ∧
               fixedCodim σ (E.map hexCoordinateSixHom) = 2 ∧
               IsStrongOffender σ (E.map hexCoordinateSixHom)))) := by
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
  let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  obtain ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,hfaith,hfixed,hm,hirr,hdim,hmodels,
      hσ,he,hbound,hcases⟩ := original_tripleSix_central_closure_secondary_natural_product
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter hQ
  let := hr.elementary
  let := hj.elementary
  let j := U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU)
  let π := f.comp j
  let q := hexCoordinateSixHom.comp π
  obtain ⟨hWT,f',hf',hfk',hK',hchart',hfix,e,r,her,heven',hprod⟩ :=
    original_tripleSix_central_closure_outer_model h structural D a z hz hzT hnot houter
  have hff : f' = f := by
    apply MonoidHom.ext
    intro b
    apply Hexacode.action_injective
    apply LinearMap.ext
    intro v
    let u := (tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd v)
    have hu : (tripleSixPointCoordinates D a u).toAdd = v :=
      congrArg Multiplicative.toAdd ((tripleSixPointCoordinates D a).apply_symm_apply _)
    exact hu ▸ ((hchart' b u).symm.trans (hchart b u))
  subst f'
  let v := (tripleSixPointCoordinates D a z).toAdd
  let N := (inducedAutomizer U W).map f
  let B := N.subgroupOf (Hexacode.fullVectorStabilizer v)
  let c := (MulAut.conj r.val).toMonoidHom.comp hexCoordinateSixHom
  have hN : N.map c = DuadCalculation.productCore.map duadProductHom := by
    have hc : c.comp (Hexacode.fullVectorStabilizer v).subtype =
        duadProductHom.comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact (her x).symm
    calc
      N.map c = (B.map (Hexacode.fullVectorStabilizer v).subtype).map c := by
        rw [map_subgroupOf_eq_of_le hfix]
      _ = (B.map e.toMonoidHom).map duadProductHom := by
        rw [map_map,hc,←map_map]
      _ = DuadCalculation.productCore.map duadProductHom := by rw [hprod]
  have hWM : W ≤ M := hWT.trans le_sup_right
  have hWj : (W.subgroupOf M).map j = inducedAutomizer U W := by
    ext b
    constructor
    · rintro ⟨m,hm,rfl⟩
      exact ⟨⟨m,hMU m.property⟩,hm,rfl⟩
    · rintro ⟨m,hm,rfl⟩
      exact ⟨⟨m,hWM hm⟩,hm,rfl⟩
  have hWimage : (W.subgroupOf M).map ((MulAut.conj r.val).toMonoidHom.comp q) =
      DuadCalculation.productCore.map duadProductHom := by
    change (W.subgroupOf M).map (c.comp (f.comp j)) = _
    calc
      (W.subgroupOf M).map (c.comp (f.comp j)) =
          (((W.subgroupOf M).map j).map f).map c := by rw [map_map,map_map]; rfl
      _ = ((inducedAutomizer U W).map f).map c := by rw [hWj]
      _ = DuadCalculation.productCore.map duadProductHom := hN
  have hs := original_tripleSix_central_closure_scalar_fixed_module
    h structural D a z hz hzT hnot houter
  have hVM : V ≤ M := hs.2.2.1.trans (inf_le_left.trans (pCoreIn_le 2 M))
  have hMV : M ≤ normalizer (V : Set G) := by
    have hh := hs.2.2.2.1
    change V = conjugateSpanBy _ M at hh
    rw [hh]
    exact le_normalizer_conjugateSpanBy _ M
  let cv := (subgroupOfEquivOfLe hVM).symm
  let coordinates : V →* Multiplicative (Additive (V.subgroupOf M)) := {
    toFun := fun x => Multiplicative.ofAdd (Additive.ofMul (cv x))
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hcoordinates : Function.Bijective coordinates := by
    constructor
    · intro x y he
      exact cv.injective he
    · intro y
      obtain ⟨x,hx⟩ := cv.surjective y.toAdd.toMul
      exact ⟨x,hx⟩
  let sectionData : BinaryConjugationSection M V ⊥ (σ.comp q) := {
    section_le := hVM
    kernel_le := bot_le
    normalized := hMV
    coordinates := coordinates
    onto := hcoordinates.2
    kernel_eq := by rw [bot_subgroupOf]; exact coordinates.ker_eq_bot_iff.mpr hcoordinates.1
    equivariant := by
      intro m x
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      exact (congrArg M.subtype (hσ m (Additive.ofMul (cv x)))).symm }
  have hquad : IsQuadratic σ ((W.subgroupOf M).map q) := by
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le M V ⊥ W σ q sectionData
    have hh := hs.2.2.2.2.2.2.2
    change ⁅⁅V,W⁆,W⁆ = ⊥ at hh
    rw [commutator_comm W V,commutator_comm W ⁅V,W⁆]
    exact hh.le
  exact ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,⟨r,hWimage⟩,hquad,
    hfaith,hfixed,hm,hirr,hdim,hmodels,hσ,he,hbound,hcases⟩

end CFSG.Quasithin.Chapter12.Section07
