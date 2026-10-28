module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetResidual
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairCentralizers
public import Theory.Representation.BinaryOffender.PerfectMoved
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Linear
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.NativeMiddle
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The sextet residual and its actual cocode commutators

The perfect sextet residual acts transitively on the 24 native coordinates.
Transitivity generates the augmentation core by displacements; perfectness
makes that displacement operation idempotent. Its Golay quotient is therefore
fully moved. In the original chosen module this proves [V,L_z]=V, and relative
normality then gives the previously missing containment V≤L_z.

Two prescribed hexacode coordinates isolate every pair within one tetrad as
a translation displacement. Thus the full translation group moves the cocode
onto the literal seven-dimensional pair space. Its displacements on that space
are exactly the common tetrad line, and a nonzero translation moves a suitable
pair to its complement, proving faithfulness on the seven-space. Its order
then identifies the image with the full centered-transvection group and
its common fixed space with the tetrad line. The marked conjugation lemma transports
these computations to the original subgroups without changing any kernel.

The actual consumer is NonFFSourceMathieuM24Commutator. These are the
containment and commutator calculations in source 8.2.11; normal-closure
geometry and ambient J4 recognition remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher–Smith H.15.3 and 8.2.11, printed pp.400,722,
refs/quasithin.pdf. Imported Golay and affine hexacode constructions are by
Gerald Höhn and ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, under the ATLAS Research and
Attribution License 1.0; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.SextetLayers.CoordinateTransport Atlas.Codes
open scoped BigOperators
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet

private theorem atlas_residual_preimage :
    solvableResidual SextetStabilizer = hexSign.ker.comap sextetQuotient := by
  let : Group.IsPerfect HexEvenAutomorphisms := Hexacode.even_isPerfect
  have hh : solvableResidual HexAutomorphisms = hexSign.ker := by
    apply le_antisymm
    · intro x hx
      have hm := map_solvableResidual_le hexSign (mem_map_of_mem hexSign hx)
      rw [solvableResidual_eq_bot] at hm
      exact hm
    · exact le_solvableResidual_of_isPerfect hexSign.ker
  have hm : (solvableResidual SextetStabilizer).map sextetQuotient = hexSign.ker := by
    rw [map_solvableResidual_eq sextetQuotient sextetQuotient_surjective, hh]
  have hk : sextetQuotient.ker ≤ solvableResidual SextetStabilizer :=
    SubnormalSextet.translations_le_of_scalar_mem _
      (inferInstance : (solvableResidual SextetStabilizer).Normal).isSubnormal
      (hm.symm ▸ hexSign_Z)
  rw [←hm,comap_map_eq_self hk]

/-- The perfect residual remains transitive on all 24 native coordinates. -/
theorem native_residual_transitive (S : Sextet) (i j : Fin 24) :
    ∃ g ∈ (solvableResidual (sextetStabilizer S)).map (sextetStabilizer S).subtype,
      g.val i = j := by
  let x := (nativePointEquiv S).symm i
  let y := (nativePointEquiv S).symm j
  let : MulAction.IsPretransitive (alternatingGroup (Fin 6)) (Fin 6) :=
    alternatingGroup.isPretransitive_of_three_le_card _ (by simp)
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6))
    (hexIndexEquiv x.1) (hexIndexEquiv y.1)
  obtain ⟨g,hg⟩ := hexEvenCoordinate_surjective b
  have hp : g.val.val.perm x.1 = y.1 := by
    apply hexIndexEquiv.injective
    have he := congrArg (fun b : alternatingGroup (Fin 6) => b.val (hexIndexEquiv x.1)) hg
    change hexIndexEquiv (g.val.val.perm (hexIndexEquiv.symm (hexIndexEquiv x.1))) = _ at he
    rw [hexIndexEquiv.symm_apply_apply] at he
    exact he.trans hb
  obtain ⟨t,ht⟩ := hexCoordinate_surjective y.1
    (rowLabel y.2 - g.val.val.localMap y.1 (rowLabel x.2))
  let s : SextetStabilizer := sextetAffineEquiv ⟨Multiplicative.ofAdd t,g.val⟩
  have hs : s ∈ solvableResidual SextetStabilizer := by
    rw [atlas_residual_preimage]
    change sextetQuotient s ∈ hexSign.ker
    change (sextetAffineEquiv.symm (sextetAffineEquiv _)).right ∈ hexSign.ker
    rw [sextetAffineEquiv.symm_apply_apply]
    exact g.property
  have hxy : s.val.val x = y := by
    rw [sextetAffineEquiv_coordinates]
    change (g.val.val.perm x.1,rowLabel.symm
      (g.val.val.localMap (g.val.val.perm x.1) (rowLabel x.2) + t.val (g.val.val.perm x.1))) = y
    rw [hp]
    change t.val y.1 = _ at ht
    rw [ht,add_sub_cancel,rowLabel.symm_apply_apply]
  have hm := mem_map_of_mem (nativeStabilizerEquiv S).toMonoidHom hs
  rw [map_solvableResidual_eq _ (nativeStabilizerEquiv S).surjective] at hm
  refine ⟨(nativeStabilizerEquiv S s).val,mem_map_of_mem _ hm,?_⟩
  have he := nativeStabilizer_coordinates S s x
  rw [hxy] at he
  simpa only [x,y,nativePointEquiv,Equiv.apply_symm_apply] using he

private theorem full_moved_eq_core {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (A : Subgroup (Equiv.Perm Ω))
    (ht : ∀ i j : Ω, ∃ g ∈ A, g i = j) :
    subspaceCommutator (BinaryPermutation.representation Ω) ⊤ A = BinaryPermutation.core Ω := by
  let ρ := BinaryPermutation.representation Ω
  let C := subspaceCommutator ρ ⊤ A
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    change BinaryPermutation.augmentation Ω (ρ g v - v) = 0
    rw [map_sub,BinaryPermutation.augmentation_permute,sub_self]
  · intro v hv
    let b : Ω := Classical.choice inferInstance
    have hgen (i : Ω) : Pi.single i (1 : ZMod 2) - Pi.single b 1 ∈ C := by
      obtain ⟨g,hg,hi⟩ := ht b i
      have he : ρ g (Pi.single b 1) = Pi.single i 1 := by
        ext k
        change (Pi.single b (1 : ZMod 2) : Ω → ZMod 2) (g.symm k) = (Pi.single i (1 : ZMod 2) : Ω → ZMod 2) k
        rw [←hi]
        simp only [Pi.single_apply, Equiv.symm_apply_eq]
      rw [←he]
      exact Submodule.subset_span ⟨g,hg,Pi.single b 1,Submodule.mem_top,rfl⟩
    have he : ∑ i, v i • (Pi.single i 1 - Pi.single b 1) = v := by
      simp only [smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul]
      rw [show ∑ i, v i = 0 from hv,zero_smul,sub_zero]
      ext i
      simp [Pi.single_apply]
    rw [←he]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hgen i))

/-- Full displacement on the original eleven-dimensional cocode. -/
theorem native_residual_cocode_moved (S : Sextet) :
    subspaceCommutator cocodeRepresentation ⊤
      ((solvableResidual (sextetStabilizer S)).map (sextetStabilizer S).subtype) = ⊤ := by
  let R := (solvableResidual (sextetStabilizer S)).map (sextetStabilizer S).subtype
  let A := R.map M24.subtype
  let ρ := BinaryPermutation.representation (Fin 24)
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let : Group.IsPerfect A := Group.IsPerfect.map _
  have hf : subspaceCommutator ρ ⊤ A = Core := by
    apply full_moved_eq_core
    intro i j
    obtain ⟨g,hg,hij⟩ := native_residual_transitive S i j
    exact ⟨g.val,mem_map_of_mem _ hg,hij⟩
  have hc : subspaceCommutator ρ Core A = Core := by
    rw [←hf]
    exact subspaceCommutator_idempotent_of_perfect ρ A
  have hfull : subspaceCommutator fullRepresentation Core R = Core := by
    change subspaceCommutator (ρ.comp M24.subtype) Core R = Core
    rw [subspaceCommutator_comp_map]
    exact hc
  have hm := subspaceCommutator_map_embedding fullRepresentation coreRepresentation
    (MonoidHom.id M24) Core.subtype (fun _ _ => rfl) R ⊤
  rw [Subgroup.map_id,Submodule.map_top,Submodule.range_subtype,hfull] at hm
  have hcm : subspaceCommutator coreRepresentation ⊤ R = ⊤ := by
    apply Submodule.map_injective_of_injective Core.injective_subtype
    rw [←hm,Submodule.map_top,Submodule.range_subtype]
  have hq := subspaceCommutator_map_embedding cocodeRepresentation coreRepresentation
    (MonoidHom.id M24) codeInCore.mkQ (fun _ _ => rfl) R ⊤
  rw [Subgroup.map_id,Submodule.map_top,
    LinearMap.range_eq_top.mpr codeInCore.mkQ_surjective,hcm,Submodule.map_top,
    LinearMap.range_eq_top.mpr codeInCore.mkQ_surjective] at hq
  exact hq

open MathieuCode.SextetLayers

private def pairCore (p q : Omega) : AtlasCore :=
  ⟨Pi.single p 1 - Pi.single q 1, by
    simp [BinaryPermutation.mem_core,Finset.sum_sub_distrib]⟩

private theorem pairCore_action (g : SextetStabilizer) (p q : Omega) :
    atlasCoreRepresentation g (pairCore p q) = pairCore (g.val.val p) (g.val.val q) := by
  apply Subtype.ext
  funext k
  change (Pi.single p (1 : ZMod 2) : Omega → ZMod 2) (g.val.val.symm k) -
    (Pi.single q (1 : ZMod 2) : Omega → ZMod 2) (g.val.val.symm k) =
    (Pi.single (g.val.val p) (1 : ZMod 2) : Omega → ZMod 2) k -
    (Pi.single (g.val.val q) (1 : ZMod 2) : Omega → ZMod 2) k
  simp only [Pi.single_apply,Equiv.symm_apply_eq]

private theorem pairCore_moved (i : HexIndex) (a b : Fin 4) :
    atlasCodeInCore.mkQ (pairCore (i,a) (i,b)) ∈
      subspaceCommutator atlasCocodeRepresentation ⊤ sextetTranslation.range := by
  obtain ⟨j,hji⟩ := exists_ne i
  obtain ⟨t,hti,htj⟩ := hex_two_values i j hji.symm (rowLabel a - rowLabel b) 0
  let s := sextetTranslation (Multiplicative.ofAdd t)
  have ha : s.val.val (i,b) = (i,a) := by
    rw [sextetTranslation_coordinates]
    change (i,rowLabel.symm (rowLabel b + t.val i)) = (i,a)
    rw [hti,add_sub_cancel,rowLabel.symm_apply_apply]
  have hj : s.val.val (j,0) = (j,0) := by
    rw [sextetTranslation_coordinates]
    change (j,rowLabel.symm (rowLabel 0 + t.val j)) = (j,0)
    rw [htj,add_zero,rowLabel.symm_apply_apply]
  have he : atlasCoreRepresentation s (pairCore (i,b) (j,0)) -
      pairCore (i,b) (j,0) = pairCore (i,a) (i,b) := by
    rw [pairCore_action,ha,hj]
    apply Subtype.ext
    change (_ - _) - (_ - _) = _ - _
    abel
  have hm : atlasCocodeRepresentation s (atlasCodeInCore.mkQ (pairCore (i,b) (j,0))) -
      atlasCodeInCore.mkQ (pairCore (i,b) (j,0)) ∈
      subspaceCommutator atlasCocodeRepresentation ⊤ sextetTranslation.range :=
    Submodule.subset_span ⟨s,⟨_,rfl⟩,_,Submodule.mem_top,rfl⟩
  rw [atlasCocodeRepresentation_mk,←map_sub,he] at hm
  exact hm

private theorem even_columns_decompose (w : AtlasCore)
    (hc : ∀ i : HexIndex, ∑ k : Fin 4, w.val (i,k) = 0) :
    (∑ i : HexIndex, ∑ k : Fin 4, w.val (i,k) • pairCore (i,k) (i,0)) = w := by
  apply Subtype.ext
  simp only [Submodule.coe_sum,Submodule.coe_smul]
  dsimp only [pairCore]
  simp only [smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hc,zero_smul,
    sub_zero]
  ext ⟨i,k⟩
  simp [Finset.sum_apply,Pi.single_apply,Prod.mk.injEq,ite_and]

/-- All 64 translations move the whole cocode onto its literal seven-space
of within-column pairs. Two prescribed hexacode coordinates isolate each pair. -/
theorem atlas_translation_moved :
    subspaceCommutator atlasCocodeRepresentation ⊤ sextetTranslation.range = atlasPairSpace := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨t,rfl⟩,v,_,rfl⟩
    obtain ⟨w,rfl⟩ := atlasCodeInCore.mkQ_surjective v
    rw [atlasCocodeRepresentation_mk,←map_sub]
    refine ⟨atlasCoreRepresentation (sextetTranslation t) w-w,?_,rfl⟩
    change atlasColumnParity (atlasFullRepresentation (sextetTranslation t) w.val-w.val)=0
    ext i
    rw [map_sub,Pi.sub_apply,atlasColumnParity_equivariant,sextetQuotient_translation,map_one]
    exact sub_self _
  · rintro v ⟨w,hw,rfl⟩
    have he := even_columns_decompose w (fun i => congrFun hw i)
    rw [←he,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_sum]
    apply Submodule.sum_mem
    intro k _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (pairCore_moved i k 0)

/-- The native two-core displacements are exactly the native pair span. -/
theorem native_translation_moved (S : Sextet) :
    subspaceCommutator cocodeRepresentation ⊤
      ((nativeTranslation S).range.map (sextetStabilizer S).subtype) =
        ⨆ B ∈ S.parts, supportedPairSpace B := by
  let ρ := cocodeRepresentation.comp (sextetStabilizer S).subtype
  let f := (nativeStabilizerEquiv S).symm.toMonoidHom
  have hact (g : sextetStabilizer S) (v : AtlasCocode) :
      ρ g (nativeCocodeEquiv S v) = nativeCocodeEquiv S (atlasCocodeRepresentation (f g) v) := by
    rw [nativeCocodeEquiv_equivariant]
    simp only [f,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply]
    rfl
  have hmap : (nativeTranslation S).range.map f = sextetTranslation.range := by
    rw [MonoidHom.map_range]
    have he : f.comp (nativeTranslation S) = sextetTranslation := by
      apply MonoidHom.ext
      intro t
      exact (nativeStabilizerEquiv S).symm_apply_apply _
    rw [he]
  have hm := subspaceCommutator_map_embedding ρ atlasCocodeRepresentation f
    (nativeCocodeEquiv S).toLinearMap hact (nativeTranslation S).range ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr (nativeCocodeEquiv S).surjective,
    hmap,atlas_translation_moved,nativePairSpace_map] at hm
  change subspaceCommutator (cocodeRepresentation.comp (sextetStabilizer S).subtype) ⊤
    (nativeTranslation S).range = _ at hm
  rwa [subspaceCommutator_comp_map] at hm


open scoped IsMulCommutative

/-- In a whole cocode marking, a literal subgroup commutator has precisely
its linear displacement image. The original subgroup embeddings are retained. -/
theorem marked_commutator_mem
    {G : Type*} [Group G] (W K : Subgroup G) [IsElementaryAbelian 2 W]
    (hWK : W ≤ K) (hKW : K ≤ normalizer (W : Set G))
    (q : K →* M24) (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (k : K) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨k,hKW k.property⟩ w)) =
        cocodeRepresentation (q k) (F (Additive.ofMul w)))
    (A B : Subgroup G) (hAK : A ≤ K) (hBW : B ≤ W) (w : W) :
    (w : G) ∈ ⁅B,A⁆ ↔ F (Additive.ofMul w) ∈
      subspaceCommutator cocodeRepresentation
        ((AddSubgroup.toZModSubmodule 2 (B.subgroupOf W).toAddSubgroup).map F.toLinearMap)
        ((A.subgroupOf K).map q) := by
  let c : BinaryConjugationSection K W ⊥ (cocodeRepresentation.comp q) := {
    section_le := hWK
    kernel_le := bot_le
    normalized := hKW
    coordinates := {
      toFun := fun x => Multiplicative.ofAdd (F (Additive.ofMul x))
      map_one' := F.map_zero
      map_mul' := fun x y => F.map_add (Additive.ofMul x) (Additive.ofMul y) }
    onto := fun v => by
      obtain ⟨x,hx⟩ := F.surjective v.toAdd
      exact ⟨x.toMul,congrArg Multiplicative.ofAdd hx⟩
    kernel_eq := by
      ext x
      change F (Additive.ofMul x) = 0 ↔ x.val = 1
      rw [F.map_eq_zero_iff]
      exact Subtype.ext_iff
    equivariant := fun k w => hF k w }
  have hI (H : Subgroup G) : c.imageSpace H =
      ((AddSubgroup.toZModSubmodule 2 (H.subgroupOf W).toAddSubgroup).map F.toLinearMap) := by
    ext v
    rw [c.mem_imageSpace_iff]
    constructor
    · rintro ⟨x,hx,he⟩
      exact ⟨Additive.ofMul x,hx,he⟩
    · rintro ⟨x,hx,he⟩
      exact ⟨x.toMul,hx,he⟩
  have hc := c.imageSpace_commutator A B hAK hBW
  rw [commutator_comm,subspaceCommutator_comp_map,hI B] at hc
  rw [←hc,c.mem_imageSpace_iff]
  constructor
  · intro hw
    exact ⟨w,hw,rfl⟩
  · rintro ⟨x,hx,he⟩
    have heq : x = w := congrArg Additive.toMul (F.injective he)
    exact heq ▸ hx


/-- The translations act nontrivially on the pair space precisely along
its common tetrad line. -/
theorem atlas_translation_pair_moved :
    subspaceCommutator atlasCocodeRepresentation atlasPairSpace sextetTranslation.range =
      atlasTetradLine := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨t,rfl⟩,v,hv,rfl⟩
    exact atlasTranslation_displacement t hv
  · apply Submodule.span_le.mpr
    rw [Set.singleton_subset_iff]
    obtain ⟨t,ht⟩ := hexCoordinate_surjective (0,0) (rowLabel 2-rowLabel 0)
    change t.val (0,0) = rowLabel 2-rowLabel 0 at ht
    let s := sextetTranslation (Multiplicative.ofAdd t)
    have ha : s.val.val ((0,0),0) = ((0,0),2) := by
      rw [sextetTranslation_coordinates]
      change ((0,0),rowLabel.symm (rowLabel 0 + t.val (0,0))) = _
      rw [ht,add_sub_cancel,rowLabel.symm_apply_apply]
    have hb : s.val.val ((0,0),1) = ((0,0),3) := by
      rw [sextetTranslation_coordinates]
      change ((0,0),rowLabel.symm (rowLabel 1 + t.val (0,0))) = _
      rw [ht]
      decide +kernel
    let w := pairCore ((0,0),0) ((0,0),1)
    have hw : atlasCodeInCore.mkQ w ∈ atlasPairSpace := by
      refine ⟨w,?_,rfl⟩
      change atlasColumnParity (pairCore ((0,0),0) ((0,0),1)).val = 0
      decide +kernel
    have he : atlasCoreRepresentation s w-w = atlasTetradCore (0,0) := by
      rw [pairCore_action,ha,hb]
      apply Subtype.ext
      decide +kernel
    have hm : atlasCocodeRepresentation s (atlasCodeInCore.mkQ w)-atlasCodeInCore.mkQ w ∈
        subspaceCommutator atlasCocodeRepresentation atlasPairSpace sextetTranslation.range :=
      Submodule.subset_span ⟨s,⟨_,rfl⟩,_,hw,rfl⟩
    rw [atlasCocodeRepresentation_mk,←map_sub,he] at hm
    exact hm

/-- On the native seven-space the entire translation image consists of
central displacements in the original tetrad line, and spans that line. -/
theorem native_translation_pair_moved (S : Sextet) :
    subspaceCommutator cocodeRepresentation (⨆ B ∈ S.parts, supportedPairSpace B)
      ((nativeTranslation S).range.map (sextetStabilizer S).subtype) = sextetTetradLine S := by
  let ρ := cocodeRepresentation.comp (sextetStabilizer S).subtype
  let f := (nativeStabilizerEquiv S).symm.toMonoidHom
  have hact (g : sextetStabilizer S) (v : AtlasCocode) :
      ρ g (nativeCocodeEquiv S v) = nativeCocodeEquiv S (atlasCocodeRepresentation (f g) v) := by
    rw [nativeCocodeEquiv_equivariant]
    simp only [f,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply]
    rfl
  have hmap : (nativeTranslation S).range.map f = sextetTranslation.range := by
    rw [MonoidHom.map_range]
    have he : f.comp (nativeTranslation S) = sextetTranslation := by
      apply MonoidHom.ext
      intro t
      exact (nativeStabilizerEquiv S).symm_apply_apply _
    rw [he]
  have hm := subspaceCommutator_map_embedding ρ atlasCocodeRepresentation f
    (nativeCocodeEquiv S).toLinearMap hact (nativeTranslation S).range atlasPairSpace
  rw [nativePairSpace_map,hmap,atlas_translation_pair_moved,nativeTetradLine_map] at hm
  change subspaceCommutator (cocodeRepresentation.comp (sextetStabilizer S).subtype) _
    (nativeTranslation S).range = _ at hm
  rwa [subspaceCommutator_comp_map] at hm


private theorem pairCore_mem_pair (i : HexIndex) (a b : Fin 4) :
    atlasCodeInCore.mkQ (pairCore (i,a) (i,b)) ∈ atlasPairSpace := by
  refine ⟨pairCore (i,a) (i,b),?_,rfl⟩
  change atlasColumnParity (pairCore (i,a) (i,b)).val = 0
  ext j
  by_cases hj : j = i
  · subst j
    simp [atlasColumnParity,pairCore,Pi.single_apply,Finset.sum_sub_distrib]
  · simp [atlasColumnParity,pairCore,Prod.mk.injEq,hj]

private theorem nonzero_row_moves_pair : ∀ u : Atlas.Codes.K, u ≠ 0 → ∃ b : Fin 4,
    ∀ k : Fin 4,
      ((if rowLabel.symm (rowLabel k-u) = 0 then (1 : ZMod 2) else 0) -
        (if rowLabel.symm (rowLabel k-u) = b then 1 else 0)) -
      ((if k = 0 then 1 else 0) - (if k = b then 1 else 0)) = 1 := by
  decide +kernel

/-- No nonidentity affine translation fixes the entire actual pair space.
A moving column carries a suitable two-set to its complement in that tetrad. -/
theorem atlas_translation_pair_faithful (t : Multiplicative hexacode)
    (hfix : ∀ v ∈ atlasPairSpace, atlasCocodeRepresentation (sextetTranslation t) v = v) :
    t = 1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext i
  by_contra hi
  obtain ⟨b,hb⟩ := nonzero_row_moves_pair (t.toAdd.val i) hi
  let w := pairCore (i,0) (i,b)
  have he : atlasCoreRepresentation (sextetTranslation t) w-w = atlasTetradCore i := by
    apply Subtype.ext
    funext p
    rcases p with ⟨j,k⟩
    change ((Pi.single (i,0) (1 : ZMod 2) - Pi.single (i,b) 1 : Omega → ZMod 2)
      (j,rowLabel.symm (rowLabel k-t.toAdd.val j))) -
      ((Pi.single (i,0) 1-Pi.single (i,b) 1 : Omega → ZMod 2) (j,k)) =
        if j=i then 1 else 0
    by_cases hj : j=i
    · subst j
      simpa only [Pi.sub_apply,Pi.single_apply,Prod.mk.injEq,true_and,if_true] using hb k
    · simp [Prod.mk.injEq,hj]
  have hz := sub_eq_zero.mpr (hfix (atlasCodeInCore.mkQ w) (pairCore_mem_pair i 0 b))
  rw [atlasCocodeRepresentation_mk,←map_sub,he] at hz
  have hn := congrArg (nativeCocodeEquiv standardSextet) hz
  rw [nativeCocodeEquiv_tetrad,map_zero] at hn
  exact sextetVector_ne_zero standardSextet hn

/-- Faithfulness of every native translation on the literal native seven-space. -/
theorem native_translation_pair_faithful (S : Sextet) (t : Multiplicative hexacode)
    (hfix : ∀ v ∈ ⨆ B ∈ S.parts, supportedPairSpace B,
      cocodeRepresentation (nativeTranslation S t).val v = v) : t = 1 := by
  apply atlas_translation_pair_faithful t
  intro v hv
  apply (nativeCocodeEquiv S).injective
  rw [nativeCocodeEquiv_equivariant]
  apply hfix
  rw [←nativePairSpace_map]
  exact Submodule.mem_map_of_mem hv


/-- The actual translation action on the seven-dimensional pair space. -/
@[expose] def atlasTranslationPairAction : Multiplicative hexacode →* BinaryLinear.GL atlasPairSpace :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) atlasPairSpace).toMonoidHom.comp
    (Representation.asGroupHom (atlasPairRepresentation.comp sextetTranslation))

/-- Every translation fixes the tetrad line and has displacement in it. -/
theorem atlasTranslationPairAction_mem_radical (t : Multiplicative hexacode) :
    atlasTranslationPairAction t ∈ BinaryLinear.radical atlasLineInPair := by
  constructor
  · intro v hv
    apply Subtype.ext
    exact atlasTetradLine_fixed (sextetTranslation t) hv
  · intro v
    exact atlasTranslation_displacement t v.property

/-- This is the full group of transvections with the prescribed center. -/
theorem atlasTranslationPairAction_full :
    atlasTranslationPairAction.range = BinaryLinear.radical atlasLineInPair := by
  have hi : Function.Injective atlasTranslationPairAction := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply _root_.eq_bot_iff.mpr
    intro t ht
    apply atlas_translation_pair_faithful t
    intro v hv
    exact congrArg (fun f : BinaryLinear.GL atlasPairSpace => (f ⟨v,hv⟩).val) ht
  have hle : atlasTranslationPairAction.range ≤ BinaryLinear.radical atlasLineInPair := by
    rintro g ⟨t,rfl⟩
    exact atlasTranslationPairAction_mem_radical t
  have hpair : Module.finrank (ZMod 2) atlasPairSpace = 7 :=
    (nativePairEquiv standardSextet).finrank_eq.trans (sextetPairSpan_finrank standardSextet)
  have hline : Module.finrank (ZMod 2) atlasLineInPair = 1 := by
    exact (Submodule.comapSubtypeEquivOfLe atlasTetradLine_le_pairSpace).finrank_eq.trans
      (((nativeCocodeEquiv standardSextet).ofSubmodules _ _
        (nativeTetradLine_map standardSextet)).finrank_eq.trans
          (sextetTetradLine_finrank standardSextet))
  let : Finite Cocode := Module.finite_iff_finite.mp (inferInstance : Module.Finite (ZMod 2) Cocode)
  let : Finite atlasPairSpace := Finite.of_equiv _ (nativePairEquiv standardSextet).symm.toEquiv
  apply Subgroup.eq_of_le_of_card_ge hle
  have hb := BinaryTransvectionGroups.LineAction.card_radical_le atlasLineInPair
  rw [hpair,hline] at hb
  have hc : Nat.card atlasTranslationPairAction.range = 64 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans
      ((Nat.card_congr Multiplicative.toAdd).trans hexacode_card)
  rw [hc]
  exact hb

/-- The common fixed vectors on the pair space are exactly the tetrad line. -/
theorem atlas_translation_pair_fixed (v : AtlasCocode) (hv : v ∈ atlasPairSpace) :
    (∀ t : Multiplicative hexacode, atlasCocodeRepresentation (sextetTranslation t) v = v) ↔
      v ∈ atlasTetradLine := by
  have hn : atlasLineInPair ≠ ⊥ := by
    intro hz
    have hmem : atlasCodeInCore.mkQ (atlasTetradCore (0,0)) ∈ atlasTetradLine :=
      Submodule.subset_span (Set.mem_singleton _)
    have hm : (⟨_,atlasTetradLine_le_pairSpace hmem⟩ : atlasPairSpace) ∈ atlasLineInPair := hmem
    rw [hz,Submodule.mem_bot] at hm
    have he := congrArg (fun w : atlasPairSpace => nativeCocodeEquiv standardSextet w.val) hm
    rw [nativeCocodeEquiv_tetrad] at he
    change sextetVector standardSextet = nativeCocodeEquiv standardSextet 0 at he
    rw [map_zero] at he
    exact sextetVector_ne_zero standardSextet he
  change _ ↔ (⟨v,hv⟩ : atlasPairSpace) ∈ atlasLineInPair
  rw [BinaryLinear.mem_iff_fixed_radical hn,←atlasTranslationPairAction_full]
  constructor
  · rintro h g ⟨t,rfl⟩
    exact Subtype.ext (h t)
  · intro h t
    exact congrArg Subtype.val (h (atlasTranslationPairAction t) ⟨t,rfl⟩)

/-- The same fixed-line statement holds in every native sextet marking. -/
theorem native_translation_pair_fixed (S : Sextet) (v : Cocode)
    (hv : v ∈ ⨆ B ∈ S.parts, supportedPairSpace B) :
    (∀ t : Multiplicative hexacode, cocodeRepresentation (nativeTranslation S t).val v = v) ↔
      v ∈ sextetTetradLine S := by
  rw [←nativePairSpace_map] at hv
  obtain ⟨w,hw,rfl⟩ := hv
  rw [←nativeTetradLine_map,Submodule.mem_map_equiv]
  change _ ↔ (nativeCocodeEquiv S).symm (nativeCocodeEquiv S w) ∈ atlasTetradLine
  rw [(nativeCocodeEquiv S).symm_apply_apply]
  rw [←atlas_translation_pair_fixed w hw]
  constructor
  · intro h t
    apply (nativeCocodeEquiv S).injective
    rw [nativeCocodeEquiv_equivariant]
    exact h t
  · intro h t
    change cocodeRepresentation (nativeStabilizerEquiv S (sextetTranslation t)).val _ = _
    exact (nativeCocodeEquiv_equivariant S (sextetTranslation t) w).symm.trans
      (congrArg (nativeCocodeEquiv S) (h t))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
