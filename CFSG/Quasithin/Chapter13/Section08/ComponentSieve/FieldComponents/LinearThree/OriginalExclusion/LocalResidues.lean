module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.C3System
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SixLetterPair
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.PlaneClosure

/-!
# The actual outer residues of the binary C₃ family

For the original abelian-span branch with H/O₂(H) ≃ L₃(2), the actual
intersections at LT are distinct proper Sylow overgroups. The A₆/S₆
maximal-overgroup calculation gives their full rank-two residue and
identifies the common chamber with the original T. Compatible natural
coordinates for H and its component identify the other edge with
N_H(V₂) = O²(C_K(V₂))T. Its S₃ quotient and the chamber identity then
give the full residue at H. Both possible left quotients are retained.

These are the literal subgroups used by the middle-residue construction
and terminal I.5 application, not merely abstract model identifications.
Source: Aschbacher–Smith 13.7.6(1), printed p.940, and 13.8.19, p.953.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open Subgroup Representation SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open Geometry.CoveredProduct.ResidualPlacement
open Section07.NaturalAction Section07.OrdinarySource.LinearThreeFamily
open Section07.OrdinarySource.LinearThreeC3Local Quasithin.I5
open Section05.PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem source_point_not_normalizes_plane
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ one L T V₁ ⊔ (T : Subgroup G) ≤ normalizer (V₂ : Set G) := by
  intro hn
  exact Section07.ModelExclusions.point_residual_not_normalizes_plane
    (localNaturalSetup c.localSetup) (le_sup_left.trans hn)

/-- The two literal intersections at LT exhaust its maximal Sylow overgroups. -/
theorem source_binary_point_parabolics
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    RankTwoParabolics (L ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)))
      ((middle T L K V₂).subgroupOf (L ⊔ (T : Subgroup G)))
      (H.subgroupOf (L ⊔ (T : Subgroup G))) := by
  let d := localNaturalSetup c.localSetup
  let A := L ⊔ (T : Subgroup G)
  let P := (middle T L K V₂).subgroupOf A
  let R := H.subgroupOf A
  let S : Sylow 2 A := T.subtype le_sup_right
  have h := c.f9 H c.component.local_overgroup
  have hSP : (S : Subgroup A) ≤ P := fun _ hx => sylow_le_middle hx
  have hSR : (S : Subgroup A) ≤ R := fun _ hx => h.T_le_H hx
  have hplane : planeActor (L := L) (V₂ := V₂) ≤ A :=
    (planeActor_le.trans inf_le_left).trans le_sup_left
  have hlocal : one L T V₁ ⊔ (T : Subgroup G) ≤ A :=
    (Section07.ModelExclusions.original_local_intersection_eq_one_sup_sylow d
      c.component.local_overgroup).symm.le.trans inf_le_right
  have hPplane : ∀ x : A, x ∈ P → x.val ∈ normalizer (V₂ : Set G) :=
    fun _ hx => middle_le_plane_normalizer d hx
  have hRline : ∀ x : A, x ∈ R → x.val ∈ normalizer (V₁ : Set G) :=
    fun _ hx => (c.component.local_overgroup.2.1.trans d.first_normalizer.le) hx
  have hP : P ≠ ⊤ := by
    intro he
    apply source_point_not_normalizes_plane c
    intro x hx
    exact hPplane ⟨x,hlocal hx⟩ (he.symm ▸ mem_top _)
  have hR : R ≠ ⊤ := by
    intro he
    apply Section05.PlaneGeometry.planeActor_not_normalizes_line d
    intro x hx
    exact hRline ⟨x,hplane hx⟩ (he.symm ▸ mem_top _)
  have hnP : (S : Subgroup A) ≠ P := by
    intro he
    apply Section05.PlaneGeometry.planeActor_not_normalizes_line d
    intro x hx
    have hxP : (⟨x,hplane hx⟩ : A) ∈ P :=
      (show planeActor (L := L) (V₂ := V₂) ≤ middle T L K V₂ from
        le_sup_right.trans le_sup_left) hx
    rw [←he] at hxP
    exact d.line_stable hxP
  have hnR : (S : Subgroup A) ≠ R := by
    intro he
    apply source_point_not_normalizes_plane c
    intro x hx
    have hxR : (⟨x,hlocal hx⟩ : A) ∈ R := c.component.local_overgroup.1.2 hx
    rw [←he] at hxR
    exact d.plane_stable hxR
  have hne : P ≠ R := by
    intro he
    apply source_point_not_normalizes_plane c
    intro x hx
    have hxR : (⟨x,hlocal hx⟩ : A) ∈ R := c.component.local_overgroup.1.2 hx
    exact hPplane _ (he.symm ▸ hxR)
  exact RankTwoParabolics.of_six_letter_two_quotient (pCore 2 A) pCore_isPGroup
    (source_binary_left_quotient c e₀) S P R
    (lt_of_le_of_ne hSP hnP) (lt_of_le_of_ne hSR hnR) hP hR hne

/-- The chamber is the original Sylow subgroup, with its original embedding. -/
theorem source_binary_chamber
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    chamberSubgroup (family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H) =
      (T : Subgroup G).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H) := by
  have hi := (source_binary_point_parabolics c e₀).borel_eq
  have h := c.f9 H c.component.local_overgroup
  ext x
  simp only [chamberSubgroup,mem_iInf]
  constructor
  · intro hx
    exact hi.le (show (⟨x.val,hx 0⟩ : (L ⊔ (T : Subgroup G) : Subgroup G)) ∈
      (middle T L K V₂).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
        H.subgroupOf (L ⊔ (T : Subgroup G)) from ⟨hx 1,hx 2⟩)
  · intro hx i
    fin_cases i
    · exact mem_sup_right hx
    · exact sylow_le_middle hx
    · exact h.T_le_H hx

/-- The actual first vertex has its full rank-two residue, in either left quotient. -/
theorem source_binary_family_point_parabolics
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    let F := family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
    RankTwoParabolics (F 0) ((chamberSubgroup F).subgroupOf (F 0))
      (localParabolic F 0 1) (localParabolic F 0 2) := by
  dsimp only
  rw [source_binary_chamber c e₀]
  let e : ((L ⊔ (T : Subgroup G)).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)) ≃*
      (L ⊔ (T : Subgroup G) : Subgroup G) := subgroupOfEquivOfLe le_sup_left
  exact (source_binary_point_parabolics c e₀).comap_surjective e.toMonoidHom e.surjective
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion

public noncomputable section

open Subgroup Representation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open TransvectionParabolic.Marking
open Geometry.CoveredProduct.ResidualPlacement
open Section07.OrdinarySource.LinearThreeC3Local
open Section07.ModelExclusions BinaryNaturalDual.VectorStabilizers
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem source_binary_component_coordinates
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL)
    (hKH : K ≤ H) :
    ∃ (eH : Source.Hstar H ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
      (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
      (eV : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      (∀ k : K, eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      ∀ a v, eV (act.representation a v) = eH a (eV v) := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup (Source.Hstar H) := e₀.isSimpleGroup
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have ht : Source.starImage H K = ⊤ :=
    (inferInstance : (Source.starImage H K).Normal).eq_bot_or_eq_top.resolve_left
      (Components.starImage_isCComponent H K c.component.component).ne_bot
  obtain ⟨e,⟨f⟩,_⟩ := source_binary_marked_natural c act e₀
  let eH := e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3)
  let eK := (Components.componentStarEquiv H K hKH c.component.component).trans
    ((MulEquiv.subgroupCongr ht).trans (topEquiv.trans eH))
  refine ⟨eH,eK,f.toLinearEquiv,?_,?_⟩
  · intro k
    rfl
  · intro a v
    have hh := LinearMap.congr_fun (f.isIntertwining' (e a)) v
    change f (act.representation (e.symm (e a)) v) = BinaryLinearThree.W (e a) (f v) at hh
    rw [e.symm_apply_apply] at hh
    exact hh

/-- The original middle-right edge is the point stabilizer in the natural action. -/
theorem source_binary_point_parabolic
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    pointResidual K V₂ ⊔ (T : Subgroup G) = H ⊓ normalizer (V₂ : Set G) ∧
      Nonempty (((pointResidual K V₂ ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (pointResidual K V₂ ⊔ (T : Subgroup G) : Subgroup G)) ≃*
          Equiv.Perm (Fin 3)) := by
  let d := localNaturalSetup c.localSetup
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hF9 := c.f9 H c.component.local_overgroup
  have hH := c.component.local_overgroup
  let ρ := act.representation
  have hρ : IsConjugation H V₃ V₁ ρ := act.conjugation
  let C := residual (K ⊓ centralizer (V₂ : Set G))
  have hCK : C ≤ K := (residual_le _).trans inf_le_left
  have hCH : C ≤ H := hCK.trans hKH
  have hTH : (T : Subgroup G) ≤ H := hF9.T_le_H
  have hHN : H ≤ normalizer (V₁ : Set G) := hH.2.1.trans d.first_normalizer.le
  obtain ⟨eH,eK,eV,heK,heV⟩ := source_binary_component_coordinates c act e₀ hKH
  have hP₂ : sectionImage H V₃ V₁ V₂ ≠ ⊥ := by
    intro hz
    have hh := plane_section_finrank d (H := H)
    rw [hz,finrank_bot] at hh
    omega
  obtain ⟨u,hu,hu0⟩ := (Submodule.ne_bot_iff _).mp hP₂
  have he : ∀ k : K, ∀ v,
      eV (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
        linearRepresentation 3 (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV v) := by
    intro k v
    rw [heV,heK]
    rfl
  let q := eH.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let qK := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let S := representationStabilizer (linearRepresentation 3) (eV u)
  have hq : Function.Surjective q := eH.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    have hker : q.ker = pCore 2 H := by
      dsimp only [q]
      rw [MonoidHom.ker_comp_of_injective _ _ eH.injective,QuotientGroup.ker_mk']
    rw [hker]
    exact pCore_isPGroup
  let R := T.subtype hTH
  have hRS : (R : Subgroup H).map q ≤ S := by
    rintro _ ⟨t,ht,rfl⟩
    change linearRepresentation 3 (eH (QuotientGroup.mk' (pCore 2 H) t)) (eV u) = eV u
    change eH (QuotientGroup.mk' (pCore 2 H) t) (eV u) = eV u
    rw [←heV,plane_vector_fixed d ρ hρ t ht u hu hu0]
  have hCmap : (C.subgroupOf H).map q = (C.subgroupOf K).map qK := by
    ext a
    constructor
    · rintro ⟨x,hx,rfl⟩
      let k : K := ⟨x,hCK hx⟩
      refine ⟨k,hx,?_⟩
      have heq : inclusion hKH k = x := Subtype.ext rfl
      exact (heK k).symm.trans (congrArg (fun t => eH (QuotientGroup.mk' (pCore 2 H) t)) heq)
    · rintro ⟨k,hk,rfl⟩
      exact ⟨inclusion hKH k,hk,heK k⟩
  have hCS : (C.subgroupOf H).map q = residual S := hCmap.trans
    (plane_centralizer_residual_model_image d hHN hKH ρ hρ (linearRepresentation 3) eK eV he u hu hu0)
  have hsup : C.subgroupOf H ⊔ (R : Subgroup H) = S.comap q :=
    sup_sylow_eq_comap_of_residual_image 2 q hq hk R _ S hRS hCS
  have hPH : (S.comap q).map H.subtype = H ⊓ normalizer (V₂ : Set G) := by
    apply point_stabilizer_preimage_eq_plane_normalizer d le_rfl ρ hρ
      (linearRepresentation 3) eH eV
    · intro h v
      exact heV _ _
    · exact hu
    · exact hu0
  have htotal : C ⊔ (T : Subgroup G) = H ⊓ normalizer (V₂ : Set G) := by
    have hh := congrArg (map H.subtype) hsup
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCH,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH,hPH] at hh
    exact hh
  refine ⟨htotal,?_⟩
  let A := C ⊔ (T : Subgroup G)
  have hA : A ≤ H := sup_le hCH hTH
  let eA : A ≃* S.comap q :=
    (subgroupOfEquivOfLe hA).symm.trans (MulEquiv.subgroupCongr (by
      apply map_injective H.subtype_injective
      rw [map_subgroupOf_eq_of_le hA,hPH]
      exact htotal))
  let : Finite (BinaryLinear.GL (Fin 3 → ZMod 2)) := Finite.of_injective (fun g : BinaryLinear.GL (Fin 3 → ZMod 2) => (g : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))) DFunLike.coe_injective
  let : Finite S := Finite.of_injective (fun x : S => (x : BinaryLinear.GL (Fin 3 → ZMod 2))) Subtype.val_injective
  let f := (q.subgroupComap S).comp eA.toMonoidHom
  have hf : Function.Surjective f :=
    (q.subgroupComap_surjective_of_surjective S hq).comp eA.surjective
  have hfker : IsPGroup 2 f.ker := by
    let i : f.ker →* q.ker := {
      toFun x := ⟨eA x, by
        have hh := congrArg Subtype.val x.property
        exact hh⟩
      map_one' := Subtype.ext (congrArg (fun z : S.comap q => (z : H)) (map_one eA))
      map_mul' x y := Subtype.ext (congrArg (fun z : S.comap q => (z : H)) (map_mul eA (x : A) (y : A))) }
    apply hk.of_injective i
    intro x y hxy
    apply Subtype.ext
    apply eA.injective
    exact Subtype.ext (congrArg (fun z : q.ker => (z : H)) hxy)
  have hv : eV u ≠ 0 := fun hz => hu0 (eV.injective (hz.trans (map_zero eV).symm))
  obtain ⟨eS⟩ := BinaryLinear.PointStabilizerRank.three_point_quotient (by simp) (eV u) hv
  have hSe : S = MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) (eV u) := by
    ext g
    rfl
  let eS' : S ≃* MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) (eV u) := MulEquiv.subgroupCongr hSe
  exact ⟨(f.pCoreQuotientEquiv hf hfker).trans
    ((QuotientGroup.congr _ _ eS' (pCore_map_iso 2 eS')).trans eS)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion

public noncomputable section
open Subgroup Representation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open TransvectionParabolic.Marking
open Geometry.CoveredProduct.ResidualPlacement
open Section07.OrdinarySource.LinearThreeC3Local
open Section07.OrdinarySource.LinearThreeFamily Quasithin.I5
open Section05.PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem source_binary_middle_inf_H
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    middle T L K V₂ ⊓ H = pointResidual K V₂ ⊔ (T : Subgroup G) := by
  have hp := (source_binary_point_parabolic c act e₀).1
  apply le_antisymm
  · rw [hp]
    exact le_inf inf_le_right
      (inf_le_left.trans (middle_le_plane_normalizer (localNaturalSetup c.localSetup)))
  · exact le_inf (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (hp.le.trans inf_le_left)

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
private theorem source_binary_chamber_ambient
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    (L ⊔ (T : Subgroup G)) ⊓ middle T L K V₂ ⊓ H = (T : Subgroup G) := by
  have hi := (source_binary_point_parabolics c e₀).borel_eq
  apply le_antisymm
  · intro x hx
    exact hi.le (show (⟨x,hx.1.1⟩ : (L ⊔ (T : Subgroup G) : Subgroup G)) ∈
      (middle T L K V₂).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
        H.subgroupOf (L ⊔ (T : Subgroup G)) from ⟨hx.1.2,hx.2⟩)
  · exact le_inf (le_inf le_sup_right sylow_le_middle)
      (c.f9 H c.component.local_overgroup).T_le_H

theorem source_binary_plane_parabolics
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    RankTwoParabolics H ((T : Subgroup G).subgroupOf H)
      ((L ⊔ (T : Subgroup G)).subgroupOf H)
      ((middle T L K V₂).subgroupOf H) := by
  let d := localNaturalSetup c.localSetup
  have hH := c.component.local_overgroup
  have h := c.f9 H hH
  let A := L ⊔ (T : Subgroup G)
  let J := middle T L K V₂
  let P := A.subgroupOf H
  let R := J.subgroupOf H
  let S : Sylow 2 H := T.subtype (show (T : Subgroup G) ≤ H from h.T_le_H)
  have hpt := source_binary_point_parabolics c e₀
  have hch := source_binary_chamber_ambient c e₀
  have hmeet : P ⊓ R = (S : Subgroup H) := by
    ext x
    exact ⟨fun hx => hch.le ⟨⟨hx.1,hx.2⟩,x.property⟩,
      fun hx => ⟨(hch.ge hx).1.1,(hch.ge hx).1.2⟩⟩
  have hnLeft : ¬ IsPGroup 2 (H.subgroupOf A) := by
    intro hn
    have he := (T.subtype (show (T : Subgroup G) ≤ A from le_sup_right)).is_maximal'
      hn (by
        change (T : Subgroup G).subgroupOf A ≤ H.subgroupOf A
        rw [←hpt.borel_eq]
        exact inf_le_right)
    have hle : H.subgroupOf A ≤ J.subgroupOf A := by
      rw [he]
      change (T : Subgroup G).subgroupOf A ≤ J.subgroupOf A
      rw [←hpt.borel_eq]
      exact inf_le_left
    have he' : H.subgroupOf A = J.subgroupOf A := by
      by_contra hne
      exact hpt.left_maximal.1 (hpt.right_maximal.2 _ (lt_of_le_of_ne hle hne))
    exact hpt.distinct he'.symm
  have hnP : ¬ IsPGroup 2 P := by
    intro hn
    have hp := (hn.map H.subtype).comap_subtype (K := A)
    have he : (P.map H.subtype).subgroupOf A = H.subgroupOf A := by
      rw [subgroupOf_map_subtype]
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
    exact hnLeft (he ▸ hp)
  have hnR : ¬ IsPGroup 2 R := by
    intro hn
    have he := source_binary_middle_inf_H c act e₀
    have hC : IsPGroup 2 ↥(pointResidual K V₂ ⊔ (T : Subgroup G)) := by
      have hh := hn.map H.subtype
      rw [subgroupOf_map_subtype,he] at hh
      exact hh
    obtain ⟨eC⟩ := (source_binary_point_parabolic c act e₀).2
    have hh := (hC.to_quotient (pCore 2 _)).of_equiv eC
    obtain ⟨n,hn⟩ := hh.exists_card_eq
    have hd : 3 ∣ 2 ^ n := by
      rw [←hn,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
      decide
    have hb := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at hb
  have hP : P ≠ ⊤ := by
    intro he
    apply hH.2.2
    intro x hx
    have hxA : x ∈ A := (show (⟨x,hx⟩ : H) ∈ P from he.symm ▸ mem_top _)
    rw [d.local_normalizer]
    exact (sup_le L.le_normalizer d.normalizes_L) hxA
  have hR : R ≠ ⊤ := by
    intro he
    have hPS : P = (S : Subgroup H) := by simpa only [he,inf_top_eq] using hmeet
    exact hnP (hPS ▸ S.isPGroup')
  exact RankTwoParabolics.of_psl_two_quotient (pCore 2 H) pCore_isPGroup e₀ S P R
    hP hR hnP hnR hmeet


theorem source_binary_family_plane_parabolics
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    let F := family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
    RankTwoParabolics (F 2) ((chamberSubgroup F).subgroupOf (F 2))
      (localParabolic F 2 0) (localParabolic F 2 1) := by
  dsimp only
  rw [source_binary_chamber c e₀]
  let e : (H.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)) ≃* H := subgroupOfEquivOfLe le_sup_right
  exact (source_binary_plane_parabolics c act e₀).comap_surjective e.toMonoidHom e.surjective

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
