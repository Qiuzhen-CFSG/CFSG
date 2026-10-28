module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearThreePoint
public import Theory.SpecificGroups.BinaryLinear.ThreePointQuotient
public import Theory.GroupTheory.PResidual.ResidualImageSylow
public import Theory.GroupTheory.PCoreFrattiniTransport
/-!
# The original K0T parabolic in the binary three-dimensional branch

The component quotient carries K0 onto the residual of the marked point
stabilizer. Its Sylow supplement is therefore that entire point stabilizer,
and the original two-core kernel lies in T. This identifies K0T with the
original H-normalizer of V2 and gives its intrinsic quotient S3.

Source: Aschbacher–Smith, 13.7.6(1), printed p.940.
-/
@[expose] public section
open Subgroup Representation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryNaturalDual.VectorStabilizers
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
omit [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)] in
/-- The original first and third vertices meet in L1T. -/
theorem original_local_intersection_eq_one_sup_sylow
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M) :
    H ⊓ (L ⊔ (T : Subgroup G)) = sourceOne L T V₁ ⊔ (T : Subgroup G) := by
  let P := (L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G)
  have hTP : (T : Subgroup G) ≤ P := le_inf le_sup_right d.line_stable
  have hs := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTP))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP,
    ← MonoidHom.range_eq_map,range_subtype] at hs
  have he : sourceOne L T V₁ ⊔ (T : Subgroup G) = P := hs
  apply le_antisymm
  · rw [he]
    exact le_inf inf_le_right (inf_le_left.trans (hH.2.1.trans d.first_normalizer.le))
  · exact le_inf hH.1.2 (he.le.trans inf_le_left)

/-- The actual K0T is the plane normalizer in H and has two-core quotient S3. -/
theorem linear_three_point_parabolic_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    let K₀ := residual (K ⊓ centralizer (V₂ : Set G))
    K₀ ⊔ (T : Subgroup G) = H ⊓ normalizer (V₂ : Set G) ∧
      Nonempty (((K₀ ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K₀ ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  dsimp only
  let C := residual (K ⊓ centralizer (V₂ : Set G))
  have hCK : C ≤ K := (residual_le _).trans inf_le_left
  have hCH : C ≤ H := hCK.trans hKH
  have hTH : (T : Subgroup G) ≤ H := hF9.T_le_H
  have hHN : H ≤ normalizer (V₁ : Set G) := hH.2.1.trans d.first_normalizer.le
  obtain ⟨eH,eV,heK,heV⟩ := linear_three_full_action_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
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
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
