module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoShearSpace
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoDisjointKernelRows
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoPerfectLift
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoNaturalActor
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSupportComponent
public import Theory.Representation.BinaryConjugationSection.Descent

/-!
# Saturation of the actual canonical kernel rows

Keep the original commutator rows for K intersect N and restrict those same
rows to K intersect L. Natural special-linear precomposition saturates the
first range. Transvection differences lie in the restricted range and
generate every original row. The row images therefore agree before any
claim that their actual evaluation subgroup is the whole denominator.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl

private def saturation_column {D : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    {n : ℕ} (j : Fin n) : D →ₗ[ZMod 2] ((Fin n → ZMod 2) →ₗ[ZMod 2] D) where
  toFun d := (LinearMap.proj j).smulRight d
  map_add' d e := by ext v; simp [smul_add]
  map_smul' a d := by ext v; simp [smul_smul,mul_comm]

private theorem saturation_column_apply {D : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    {n : ℕ} (j : Fin n) (d : D) (v : Fin n → ZMod 2) :
    saturation_column j d v = v j • d := rfl

private theorem saturation_column_difference {D : Type*}
    [AddCommGroup D] [Module (ZMod 2) D] {n : ℕ}
    (f : (Fin n → ZMod 2) →ₗ[ZMod 2] D) {i j : Fin n} (hij : i ≠ j) :
    f.comp (specialLinearNatural n (Matrix.SpecialLinearGroup.transvection hij 1)) - f =
      saturation_column j (f (Pi.single i 1)) := by
  apply LinearMap.ext
  intro v
  change f (((1 : Matrix (Fin n) (Fin n) (ZMod 2)) + Matrix.single i j 1).mulVec v) - f v = _
  rw [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec_eq,one_mul,map_add]
  rw [map_smul,add_sub_cancel_left]
  rfl

private theorem precomposition_differences_generate {D : Type*}
    [AddCommGroup D] [Module (ZMod 2) D] (n : ℕ) (hn : 2 ≤ n)
    (S T : Submodule (ZMod 2) ((Fin n → ZMod 2) →ₗ[ZMod 2] D))
    (hTS : T ≤ S)
    (hdiff : ∀ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      ∀ f ∈ S, f.comp (specialLinearNatural n g) - f ∈ T) : S ≤ T := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hoff (f : (Fin n → ZMod 2) →ₗ[ZMod 2] D) (hf : f ∈ S)
      (i j : Fin n) (hij : i ≠ j) : saturation_column j (f (Pi.single i 1)) ∈ T := by
    rw [←saturation_column_difference f hij]
    exact hdiff _ f hf
  intro f hf
  have hcolumn (i : Fin n) : saturation_column i (f (Pi.single i 1)) ∈ T := by
    obtain ⟨j,hji⟩ := exists_ne i
    have hh := hoff (saturation_column j (f (Pi.single i 1)))
      (hTS (hoff f hf i j hji.symm)) j i hji
    simpa only [saturation_column_apply,Pi.single_eq_same,one_smul] using hh
  have he : f = ∑ i : Fin n, saturation_column i (f (Pi.single i 1)) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply,saturation_column_apply]
    simp_rw [←map_smul]
    rw [←map_sum]
    congr 1
    ext i
    simp [Pi.single_apply]
  rw [he]
  exact T.sum_mem (fun i _ => hcolumn i)

private def natural_linear_rows
    {B D W : Type*} [Group B] [Group D] [IsElementaryAbelian 2 D]
    [AddCommGroup W] [Module (ZMod 2) W] {n : ℕ}
    (e : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (row : B →* (Multiplicative W →* D)) :
    B →* Multiplicative ((Fin n → ZMod 2) →ₗ[ZMod 2] Additive D) where
  toFun b := Multiplicative.ofAdd
    (((row b).toAdditiveRight.toZModLinearMap 2).comp e.symm.toLinearMap)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    change Additive.ofMul (row 1 (Multiplicative.ofAdd (e.symm v))) = 0
    rw [map_one]
    rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    change Additive.ofMul (row (a*b) (Multiplicative.ofAdd (e.symm v))) =
      Additive.ofMul (row a (Multiplicative.ofAdd (e.symm v))) +
        Additive.ofMul (row b (Multiplicative.ofAdd (e.symm v)))
    rw [map_mul]
    rfl

private theorem natural_rows_saturated
    {B D W : Type*} [Group B] [Group D] [IsElementaryAbelian 2 D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (n : ℕ) (hn : 2 ≤ n) (e : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (row : B →* (Multiplicative W →* D))
    (hstable : ∀ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), ∀ b : B,
      ∃ c : B, ∀ w : W, row c (Multiplicative.ofAdd w) =
        row b (Multiplicative.ofAdd (e.symm (specialLinearNatural n g (e w))))) :
    ∀ f : Multiplicative W →* D,
      f ∈ row.range ↔ f.range ≤ ⨆ b : B, (row b).range := by
  let r := natural_linear_rows e row
  let S : Submodule (ZMod 2) ((Fin n → ZMod 2) →ₗ[ZMod 2] Additive D) :=
    AddSubgroup.toZModSubmodule 2 r.range.toAddSubgroup
  let X := Submodule.span (ZMod 2)
    {y : Additive D | ∃ f ∈ S, ∃ w : Fin n → ZMod 2, f w = y}
  have hS (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
      (f : (Fin n → ZMod 2) →ₗ[ZMod 2] Additive D) (hf : f ∈ S) :
      f.comp (specialLinearNatural n g) ∈ S := by
    obtain ⟨b,hb⟩ := hf
    obtain ⟨c,hc⟩ := hstable g b
    refine ⟨c,?_⟩
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    change Additive.ofMul (row c (Multiplicative.ofAdd (e.symm v))) = f _
    rw [hc,e.apply_symm_apply]
    exact congrArg (fun z => z.toAdd (specialLinearNatural n g v)) hb
  have hfull := precomposition_invariant_shears_eq_full_range n hn S hS
  have heval : (⨆ b : B, (row b).range) ≤ X.toAddSubgroup.toSubgroup := by
    apply iSup_le
    intro b y hy
    obtain ⟨w,rfl⟩ := hy
    change Additive.ofMul (row b w) ∈ X
    exact Submodule.subset_span ⟨(r b).toAdd,⟨b,rfl⟩,e w.toAdd,by
      change Additive.ofMul (row b (Multiplicative.ofAdd (e.symm (e w.toAdd)))) = _
      rw [e.symm_apply_apply]
      rfl⟩
  intro f
  constructor
  · rintro ⟨b,rfl⟩
    exact le_iSup (fun b : B => (row b).range) b
  · intro hf
    let f' := (f.toAdditiveRight.toZModLinearMap 2).comp e.symm.toLinearMap
    have hf' : f' ∈ S := (hfull f').mpr (by
      rintro y ⟨v,rfl⟩
      exact heval (hf ⟨Multiplicative.ofAdd (e.symm v),rfl⟩))
    obtain ⟨b,hb⟩ := hf'
    refine ⟨b,?_⟩
    apply MonoidHom.ext
    intro w
    have hh := congrArg (fun z => z.toAdd (e w.toAdd)) hb
    change Additive.ofMul (row b (Multiplicative.ofAdd (e.symm (e w.toAdd)))) =
      Additive.ofMul (f (Multiplicative.ofAdd (e.symm (e w.toAdd)))) at hh
    rw [e.symm_apply_apply] at hh
    exact congrArg Additive.toMul hh

private theorem natural_rows_restrict_eq
    {B D W : Type*} [Group B] [Group D] [IsElementaryAbelian 2 D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (n : ℕ) (hn : 2 ≤ n) (e : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (row : B →* (Multiplicative W →* D)) (C : Subgroup B)
    (hdiff : ∀ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), ∀ b : B,
      ∃ c : C, ∀ w : W, row c (Multiplicative.ofAdd w) =
        row b (Multiplicative.ofAdd (e.symm (specialLinearNatural n g (e w)))) /
          row b (Multiplicative.ofAdd w)) :
    row.range = (row.comp C.subtype).range := by
  let r := natural_linear_rows e row
  let S : Submodule (ZMod 2) ((Fin n → ZMod 2) →ₗ[ZMod 2] Additive D) :=
    AddSubgroup.toZModSubmodule 2 r.range.toAddSubgroup
  let T : Submodule (ZMod 2) ((Fin n → ZMod 2) →ₗ[ZMod 2] Additive D) :=
    AddSubgroup.toZModSubmodule 2 (C.map r).toAddSubgroup
  have hTS : T ≤ S := by
    rintro f ⟨b,hb,rfl⟩
    exact ⟨b,rfl⟩
  have hST : S ≤ T := precomposition_differences_generate n hn S T hTS (by
    intro g f hf
    obtain ⟨b,hb⟩ := hf
    obtain ⟨c,hc⟩ := hdiff g b
    refine ⟨c,c.property,?_⟩
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    have hh := hc (e.symm v)
    rw [e.apply_symm_apply] at hh
    change Additive.ofMul (row c (Multiplicative.ofAdd (e.symm v))) =
      f (specialLinearNatural n g v) - f v
    rw [hh]
    change (r b).toAdd (specialLinearNatural n g v) - (r b).toAdd v = _
    exact congrArg (fun z => z.toAdd (specialLinearNatural n g v) - z.toAdd v) hb)
  apply le_antisymm
  · rintro f ⟨b,rfl⟩
    obtain ⟨c,hc,hce⟩ := hST (show (r b).toAdd ∈ S from ⟨b,rfl⟩)
    refine ⟨⟨c,hc⟩,?_⟩
    apply MonoidHom.ext
    intro w
    have hh := congrArg (fun z => z.toAdd (e w.toAdd)) hce
    change Additive.ofMul (row c (Multiplicative.ofAdd (e.symm (e w.toAdd)))) =
      Additive.ofMul (row b (Multiplicative.ofAdd (e.symm (e w.toAdd)))) at hh
    rw [e.symm_apply_apply] at hh
    exact congrArg Additive.toMul hh
  · rintro f ⟨c,rfl⟩
    exact ⟨c,rfl⟩

private theorem rows_comparison_of_natural_action
    {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (B C L D : Subgroup G) [IsElementaryAbelian 2 D]
    (hCB : C ≤ B) (hLB : L ≤ normalizer (B : Set G))
    (hcomm : ⁅L,B⁆ ≤ C)
    (ψ : Representation (ZMod 2) L W) (n : ℕ) (hn : 2 ≤ n)
    (q : L →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (hq : Function.Surjective q)
    (e : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (he : ∀ l : L, ∀ w : W, e (ψ l w) = specialLinearNatural n (q l) (e w))
    (row : B →* (Multiplicative W →* D))
    (heqv : ∀ (l : L) (b b' : B), (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
      ∀ w : W, row b' (Multiplicative.ofAdd w) =
        row b (Multiplicative.ofAdd (ψ l⁻¹ w))) :
    (∀ f : Multiplicative W →* D,
      f ∈ row.range ↔ f.range ≤ ⨆ b : B, (row b).range) ∧
      row.range = (row.comp (Subgroup.inclusion hCB)).range := by
  have hlift (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      ∃ l : L, ∀ w : W, ψ l⁻¹ w = e.symm (specialLinearNatural n g (e w)) := by
    obtain ⟨l,hl⟩ := hq g⁻¹
    refine ⟨l,fun w => e.injective ?_⟩
    rw [he,e.apply_symm_apply,map_inv,hl,inv_inv]
  have hstable (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (b : B) :
      ∃ b' : B, ∀ w : W, row b' (Multiplicative.ofAdd w) =
        row b (Multiplicative.ofAdd (e.symm (specialLinearNatural n g (e w)))) := by
    obtain ⟨l,hl⟩ := hlift g
    let b' : B := ⟨(l : G) * (b : G) * (l : G)⁻¹,
      le_normalizer_iff.mp hLB l l.property b b.property⟩
    refine ⟨b',fun w => ?_⟩
    rw [heqv l b b' rfl w,hl w]
  refine ⟨natural_rows_saturated n hn e row hstable,?_⟩
  have hr := natural_rows_restrict_eq n hn e row (C.subgroupOf B) (by
    intro g b
    obtain ⟨l,hl⟩ := hlift g
    let b' : B := ⟨(l : G) * (b : G) * (l : G)⁻¹,
      le_normalizer_iff.mp hLB l l.property b b.property⟩
    have hc : ((b' * b⁻¹ : B) : G) ∈ C :=
      hcomm (commutator_mem_commutator l.property b.property)
    refine ⟨⟨b' * b⁻¹,hc⟩,?_⟩
    intro w
    change row (b' * b⁻¹) (Multiplicative.ofAdd w) = _
    rw [map_mul,map_inv,MonoidHom.mul_apply,MonoidHom.inv_apply]
    rw [←div_eq_mul_inv]
    rw [heqv l b b' rfl w,hl w])
  have hc : (row.comp (C.subgroupOf B).subtype).range =
      (row.comp (Subgroup.inclusion hCB)).range := by
    rw [MonoidHom.range_comp,range_subtype,MonoidHom.range_comp,inclusion_range]
  exact hr.trans hc

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual canonical section-kernel rows are saturated, and their
restriction to the canonical perfect lift has exactly the same range. -/
theorem PreparedChosenModule.decomposable_five_partner_two_disjoint_saturated_rows
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          D ⊓ thompsonPlane T V (c.ambientFactor d s.first).space = ⊥ →
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          let K := commutatorPreimage Mc F D
          let B := K ⊓ N.map Mc.subtype
          let B₀ := K ⊓ L
          let hB₀B : B₀ ≤ B := inf_le_inf le_rfl
            (map_mono (map_subtype_le (solvableResidual N)))
          ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
            ∃ _e : ActionEquiv (Representation.BinaryOffender.imageRepresentation ρ)
              (linearNatural BinaryField.two n),
            actionSubgroup ρ (L.subgroupOf Mc) = ⊤ ∧
            Group.IsPerfect L ∧ Mc ≤ normalizer (L : Set G) ∧
            L ≤ centralizer (D : Set G) ∧ N.map Mc.subtype ≤ centralizer (D : Set G) ∧
            ⁅F,L⁆ = F ∧ F ≤ L ∧
            Mc ≤ normalizer (B : Set G) ∧ ⁅B,F⁆ ≤ D ∧
            ∃ heD : IsElementaryAbelian 2 D,
              letI := heD
              ∃ row : B →* (Multiplicative W →* D),
                (∀ (b : B) (f : F), (row b (dF.coordinates f) : G) = ⁅(b : G),(f : G)⁆) ∧
                row.ker = (centralizer (F : Set G)).subgroupOf B ∧
                (⨆ b : B, (row b).range).map D.subtype = ⁅B,F⁆ ∧
                (∀ f : Multiplicative W →* D,
                  f ∈ row.range ↔ f.range.map D.subtype ≤ ⁅B,F⁆) ∧
                row.range = (row.comp (Subgroup.inclusion hB₀B)).range := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hDZ
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  obtain ⟨_,_,_,_,_,_,J,hJc,_,hJN,_,_,_,_,n,hn,⟨eJ⟩⟩ :=
    ((h.decomposable_five_partner_two_support_component hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ) ρ dF hDZ
  have hJtop := DecomposableQuinticControl.subgroup_eq_top_of_binary_natural
    (Representation.BinaryOffender.imageRepresentation ρ) (imageRepresentation_injective ρ) J n eJ
  obtain ⟨e⟩ := DecomposableQuinticControl.whole_actor_natural_of_subgroup
    (Representation.BinaryOffender.imageRepresentation ρ) (imageRepresentation_injective ρ) J n eJ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  let R := normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ))
  have hA₁A : actionSubgroup ρ
      ((plane V (c.ambientFactor d s.first).space).subgroupOf Mc) ≤ A :=
    map_mono (comap_mono (plane_le _))
  have hRtop : R = ⊤ := by
    apply top_unique
    rw [←hJtop]
    exact hJN.trans (normalClosure_mono hA₁A)
  let : IsQuasisimple J := hJc.2
  let : Group.IsPerfect (Representation.BinaryOffender.actionImage ρ) :=
    Group.IsPerfect.ofSurjective (f := J.subtype) (fun g => ⟨⟨g,hJtop ▸ mem_top g⟩,rfl⟩)
  let : Group.IsPerfect R := hRtop.symm ▸ (inferInstance : Group.IsPerfect
    (⊤ : Subgroup (Representation.BinaryOffender.actionImage ρ)))
  let N := normalClosure (V.subgroupOf Mc : Set Mc)
  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let B := K ⊓ N.map Mc.subtype
  let B₀ := K ⊓ L
  have hLN : L ≤ N.map Mc.subtype := map_mono (map_subtype_le (solvableResidual N))
  have hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
  have hB₀B : B₀ ≤ B := inf_le_inf le_rfl hLN
  have hnon := (((h.decomposable_five_partner_two_disjoint_strong
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hDZ).2.2
  obtain ⟨hperfect,hMcL,_,hLD,hFL,hFLle,himage⟩ :=
    (h.decomposable_five_canonical_perfect_lift hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hVQ ρ dF).resolve_left hnon
  have hLtop : actionSubgroup ρ (L.subgroupOf Mc) = ⊤ := by
    rw [himage,solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype]
    exact hRtop
  obtain ⟨_,hLB,_,_,hND,_,hBF,heD,row,heval,hker,heqv,hgen⟩ :=
    ((h.decomposable_five_partner_two_disjoint_normal_kernel_rows
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hDZ
  let := heD
  obtain ⟨_,_,_,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hMcK : Mc ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized Mc F D Mc hnD Mc.le_normalizer dF.normalized hnD
  have hMcN : Mc ≤ normalizer (N.map Mc.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    rintro m hm _ ⟨a,ha,rfl⟩
    exact mem_map_of_mem Mc.subtype ((inferInstance : N.Normal).conj_mem a ha ⟨m,hm⟩)
  have hMcB : Mc ≤ normalizer (B : Set G) := by
    apply (le_inf hMcK hMcN).trans inf_normalizer_le_normalizer_inf
  have hBM : B ≤ Mc := inf_le_left.trans (commutatorPreimage_le Mc F D)
  have hcomm : ⁅L,B⁆ ≤ B₀ := by
    apply le_inf
    · exact (le_normalizer_iff_commutator_le_right.mp hLB).trans inf_le_left
    · exact le_normalizer_iff_commutator_le_left.mp (hBM.trans hMcL)
  let ψ := ρ.comp (Subgroup.inclusion hLMc)
  let q := e.groupEquiv.toMonoidHom.comp
    ((Representation.BinaryOffender.actionHom ρ).comp (Subgroup.inclusion hLMc))
  have hsurj : Function.Surjective q := by
    apply e.groupEquiv.surjective.comp
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,inclusion_range]
    exact hLtop
  have he (l : L) (w : W) : e.linearEquiv (ψ l w) =
      specialLinearNatural n (q l) (e.linearEquiv w) :=
    e.intertwines (Representation.BinaryOffender.actionHom ρ (Subgroup.inclusion hLMc l)) w
  have htwo : 2 ≤ n := by rcases hn with rfl | rfl | rfl <;> decide
  obtain ⟨hsat,hrows⟩ := DecomposableQuinticControl.rows_comparison_of_natural_action
    B B₀ L D hB₀B hLB hcomm ψ n htwo q hsurj e.linearEquiv he row heqv
  refine ⟨n,hn,e,hLtop,hperfect,hMcL,hLD,hND,hFL,hFLle,hMcB,hBF,heD,
    row,heval,hker,hgen,?_,hrows⟩
  intro f
  rw [hsat f,←hgen]
  constructor
  · exact map_mono
  · intro hh x hx
    obtain ⟨y,hy,he⟩ := hh (mem_map_of_mem D.subtype hx)
    exact D.subtype_injective he ▸ hy

/-- The saturated actual kernel comparison identifies the full-F images
and descends the unchanged normal-closure action through its canonical
natural actor on the literal quotient F/[K intersect N,F]. -/
theorem PreparedChosenModule.decomposable_five_partner_two_disjoint_shear_descent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          D ⊓ thompsonPlane T V (c.ambientFactor d s.first).space = ⊥ →
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let N₀ := N.map Mc.subtype
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          let K := commutatorPreimage Mc F D
          let B := K ⊓ N₀
          let B₀ := K ⊓ L
          let D₀ := ⁅B,F⁆
          let hBM : B ≤ Mc := inf_le_left.trans (commutatorPreimage_le Mc F D)
          let hB₀M : B₀ ≤ Mc := inf_le_left.trans (commutatorPreimage_le Mc F D)
          let φ := F.normalizerMonoidHom.comp (Subgroup.inclusion (hBM.trans dF.normalized))
          let φ₀ := F.normalizerMonoidHom.comp (Subgroup.inclusion (hB₀M.trans dF.normalized))
          D₀ ≤ D ∧ Mc ≤ normalizer (D₀ : Set G) ∧ φ.range = φ₀.range ∧
          ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
            ∃ e : ActionEquiv (Representation.BinaryOffender.imageRepresentation ρ)
              (linearNatural BinaryField.two n),
            let q : N₀ →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
              e.groupEquiv.toMonoidHom.comp ((Representation.BinaryOffender.actionHom ρ).comp
                (Subgroup.inclusion (map_subtype_le N)))
            Function.Surjective q ∧
            ∃ hD₀normal : (D₀.subgroupOf F).Normal,
              letI := hD₀normal
              ∃ heQ : IsElementaryAbelian 2 (F ⧸ D₀.subgroupOf F),
                letI := heQ
                ∃ τ : Representation (ZMod 2)
                    (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (Additive (F ⧸ D₀.subgroupOf F)),
                  ∃ d₀ : BinaryConjugationSection N₀ F D₀ (τ.comp q),
                    (∀ f : F, (d₀.coordinates f).toAdd =
                      Additive.ofMul (QuotientGroup.mk' (D₀.subgroupOf F) f)) ∧
                    ⁅N₀,D⁆ = ⊥ ∧ ⁅F,N₀⁆ = F := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hDZ
  let N := normalClosure (V.subgroupOf Mc : Set Mc)
  let N₀ := N.map Mc.subtype
  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let B := K ⊓ N₀
  let B₀ := K ⊓ L
  let D₀ := ⁅B,F⁆
  have hLN : L ≤ N₀ := map_mono (map_subtype_le (solvableResidual N))
  have hB₀B : B₀ ≤ B := inf_le_inf le_rfl hLN
  have hBM : B ≤ Mc := inf_le_left.trans (commutatorPreimage_le Mc F D)
  have hB₀M : B₀ ≤ Mc := inf_le_left.trans (commutatorPreimage_le Mc F D)
  let φ := F.normalizerMonoidHom.comp (Subgroup.inclusion (hBM.trans dF.normalized))
  let φ₀ := F.normalizerMonoidHom.comp (Subgroup.inclusion (hB₀M.trans dF.normalized))
  obtain ⟨n,hn,e,hLtop,_,_,hLD,hND,hFL,hFLle,hMcB,hD₀D,heD,
      row,heval,_,_,_,hrows⟩ :=
    ((h.decomposable_five_partner_two_disjoint_saturated_rows
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hDZ
  let := heD
  change Mc ≤ normalizer (B : Set G) at hMcB
  change ⁅F,L⁆ = F at hFL
  have hMcD₀ : Mc ≤ normalizer (D₀ : Set G) := by
    intro m hm
    rw [mem_normalizer_iff_map_conj_eq]
    change ⁅B,F⁆.map (MulAut.conj m).toMonoidHom = ⁅B,F⁆
    have hb : B.map (MulAut.conj m).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp (hMcB hm)
    have hf : F.map (MulAut.conj m).toMonoidHom = F :=
      mem_normalizer_iff_map_conj_eq.mp (dF.normalized hm)
    rw [map_commutator,hb,hf]
  have hφ : φ.range = φ₀.range := by
    apply le_antisymm
    · rintro a ⟨b,rfl⟩
      obtain ⟨b₀,hb₀⟩ := hrows ▸ (show row b ∈ row.range from ⟨b,rfl⟩)
      refine ⟨b₀,?_⟩
      apply MulEquiv.ext
      intro f
      apply Subtype.ext
      have hh := congrArg (fun r : Multiplicative W →* D => (r (dF.coordinates f) : G)) hb₀
      change (row (Subgroup.inclusion hB₀B b₀) (dF.coordinates f) : G) =
        (row b (dF.coordinates f) : G) at hh
      rw [heval,heval] at hh
      change (b₀ : G) * (f : G) * (b₀ : G)⁻¹ * (f : G)⁻¹ =
        (b : G) * (f : G) * (b : G)⁻¹ * (f : G)⁻¹ at hh
      exact mul_right_cancel hh
    · rintro a ⟨b,rfl⟩
      exact ⟨Subgroup.inclusion hB₀B b,rfl⟩
  let q : N₀ →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    e.groupEquiv.toMonoidHom.comp ((Representation.BinaryOffender.actionHom ρ).comp
      (Subgroup.inclusion (map_subtype_le N)))
  have hNtop : actionSubgroup ρ (N₀.subgroupOf Mc) = ⊤ := by
    apply top_unique
    rw [←hLtop]
    exact map_mono (comap_mono hLN)
  have hqsurj : Function.Surjective q := by
    apply e.groupEquiv.surjective.comp
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,inclusion_range]
    exact hNtop
  have hFN : F ≤ N₀ := hFLle.trans hLN
  have hD₀F : D₀ ≤ F := hD₀D.trans dF.kernel_le
  let heF : IsElementaryAbelian 2 F := (h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2.2.1
  let := heF
  let hD₀normal : (D₀.subgroupOf F).Normal := inferInstance
  let heQ : IsElementaryAbelian 2 (F ⧸ D₀.subgroupOf F) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.mk' (D₀.subgroupOf F))
      (QuotientGroup.mk'_surjective _)
  let := heQ
  have hqker (a : N₀) (ha : q a = 1) : ∀ f ∈ F, ⁅(a : G),f⁆ ∈ D₀ := by
    have haρ : Subgroup.inclusion (map_subtype_le N) a ∈
        (Representation.BinaryOffender.actionHom ρ).ker := by
      apply e.groupEquiv.injective
      exact ha.trans (map_one e.groupEquiv).symm
    rw [actionHom_ker_eq] at haρ
    have haK : (a : G) ∈ K := by
      have hh := mem_map_of_mem Mc.subtype haρ
      obtain ⟨_,_,_,hMcD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
        hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
      rw [dF.action_kernel_map hMcD] at hh
      exact hh
    intro f hf
    exact commutator_mem_commutator (show (a : G) ∈ B from ⟨haK,a.property⟩) hf
  obtain ⟨τ,d₀,hcoords⟩ := BinaryConjugationSection.exists_descended_actor
    N₀ F D₀ hFN hD₀F ((map_subtype_le N).trans dF.normalized)
    ((map_subtype_le N).trans hMcD₀) q hqsurj hqker
  have hFNmove : ⁅F,N₀⁆ = F := le_antisymm
    (le_normalizer_iff_commutator_le_left.mp ((map_subtype_le N).trans dF.normalized))
    (hFL.ge.trans (commutator_mono le_rfl hLN))
  exact ⟨hD₀D,hMcD₀,hφ,n,hn,e,hqsurj,hD₀normal,heQ,τ,d₀,hcoords,
    commutator_eq_bot_iff_le_centralizer.mpr hND,hFNmove⟩

end CFSG.Quasithin.Chapter15.Section01
