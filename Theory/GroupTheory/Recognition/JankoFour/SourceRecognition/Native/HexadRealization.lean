module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.HexadCoordinates
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadFixedSpace
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.Mathieu.M22.Properties.OuterHexadRadical
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient

/-!
# The checked translations are the whole native hexad two-core

The design projection has its exact cubic scalar kernel. Its restriction
to a full hexad stabilizer is surjective; the known pointwise design kernel
bounds the two-core by sixteen. The checked elementary translation subgroup
has order sixteen. Every full hexad stabilizer element preserves it, since
it preserves the pointwise kernel and each projected involution has a unique
involution lift through the central cubic cover. Thus it is precisely O₂ of
the full matrix stabilizer, including the outer action.

Its fixed space is consequently the checked six-coordinate singular space.
Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), proof of (4.6), p.598, DOI 10.1007/BF01232280.
The coordinate certificates and native ATLAS attribution are retained in
Native.HexadCoordinates; HexadFixedStructure applies this to the original Q.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu M22TripleCover M22TripleCover.Ambient InvariantPoint M22ValueBound.Concrete
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
namespace NativeHexadRealization
open NativeHexadCoordinates

private def designProjection : actionGroup →* m22DesignAut :=
  designAutEquiv.symm.toMonoidHom.comp quotientConjugation

private theorem designProjection_perm (g : actionGroup) :
    (designProjection g).val = pointAction g := by
  have he : designProjection g = ⟨pointAction g,pointAction_mem_design g⟩ := by
    apply designAutEquiv.injective
    change designAutEquiv (designAutEquiv.symm (quotientConjugation g)) = _
    rw [MulEquiv.apply_symm_apply]
    exact (pointAction_projection g).symm
  exact congrArg Subtype.val he

private theorem designProjection_surjective : Function.Surjective designProjection :=
  designAutEquiv.symm.surjective.comp quotientConjugation_surjective

private theorem designProjection_ker : designProjection.ker = scalarSubgroup := by
  rw [designProjection,MonoidHom.ker_comp_of_injective _ _ designAutEquiv.symm.injective,
    quotientConjugation_ker]

private def hexadProjection (B : Finset (Fin 22)) :
    nativeHexadStabilizer B →* MulAction.stabilizer m22DesignAut B where
  toFun g := ⟨designProjection g.val,by
    change (designProjection g.val).val • B = B
    rw [designProjection_perm]
    exact g.property⟩
  map_one' := Subtype.ext (map_one designProjection)
  map_mul' a b := Subtype.ext (map_mul designProjection a.val b.val)

private theorem hexadProjection_surjective (B : Finset (Fin 22)) :
    Function.Surjective (hexadProjection B) := by
  intro b
  obtain ⟨a,ha⟩ := designProjection_surjective b.val
  have hm : a ∈ nativeHexadStabilizer B := by
    change pointAction a • B = B
    rw [←designProjection_perm,ha]
    exact b.property
  exact ⟨⟨a,hm⟩,Subtype.ext ha⟩

/-- The full native hexad two-core has at most sixteen elements: its
faithful design image lies in the pointwise kernel. -/
theorem twoCore_card_le {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card ((nativeHexadStabilizer B).pCoreIn 2) ≤ 16 := by
  let L := nativeHexadStabilizer B
  let S := MulAction.stabilizer m22DesignAut B
  let R := L.pCoreIn 2
  let K := (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion
  have hm : (pCore 2 L).map (hexadProjection B) ≤ pCore 2 S :=
    le_sSup ⟨Normal.map inferInstance _ (hexadProjection_surjective B),pCore_isPGroup.map _⟩
  have hr : S.pCoreIn 2 = K := M22OuterHexad.radical_eq hB S
    (by rintro _ ⟨g,hg,rfl⟩; exact hg) le_rfl
  have hbound : R.map designProjection ≤ K := by
    rw [←hr]
    have hh := map_mono (f := S.subtype) hm
    change ((pCore 2 L).map L.subtype).map designProjection ≤ _
    rw [map_map]
    rw [map_map] at hh
    exact hh
  have hk : IsPGroup 3 designProjection.ker := by
    rw [designProjection_ker]
    exact IsPGroup.of_card (n := 1) scalarSubgroup_card
  have hd : Disjoint R designProjection.ker :=
    (isPGroup_pCoreIn 2 L).disjoint_of_coprime hk (by decide)
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map R designProjection
  rw [hd.eq_bot,card_bot,one_mul] at hc
  rw [←hc]
  have hK : Nat.card K = 16 := by
    rw [card_map_of_injective inclusion_injective,m22HexadPointwiseKernel_card hB]
  exact (Nat.card_le_card_of_injective (Subgroup.inclusion hbound)
    (Subgroup.inclusion_injective hbound)).trans_eq hK

private def P : Subgroup actionGroup := translations.map coverInclusion

private theorem P_le : P ≤ nativeHexadStabilizer m22Hexad123 := by
  rintro _ ⟨g,hg,rfl⟩
  change pointAction (coverInclusion g) • m22Hexad123 = m22Hexad123
  rw [pointAction_cover]
  exact m22HexadPointwiseKernel_le _ (translations_image.le (mem_map_of_mem _ hg))

private theorem P_normalized : nativeHexadStabilizer m22Hexad123 ≤
    normalizer (P : Set actionGroup) := by
  apply le_normalizer_iff.mpr
  rintro g hg _ ⟨x,hx,rfl⟩
  have hxi : x^2=1 := by
    let := translations_elementary
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hfix := (mem_m22HexadPointwiseKernel m22Hexad123 _).mp
    (translations_image.le (mem_map_of_mem Uniqueness.quotientMap hx))
  have hq : Uniqueness.quotientMap (derivedConjugation g x) ∈
      m22HexadPointwiseKernel m22Hexad123 := by
    apply (mem_m22HexadPointwiseKernel _ _).mpr
    intro p hp
    have hi : (pointAction g)⁻¹ p ∈ m22Hexad123 := by
      have hh := (MulAction.mem_stabilizer_finset'.mp
        (show pointAction g⁻¹ ∈ MulAction.stabilizer (Equiv.Perm (Fin 22)) m22Hexad123 from
          (nativeHexadStabilizer m22Hexad123).inv_mem hg)) hp
      rwa [map_inv] at hh
    change corePermutationAction (derivedConjugation g x) p = p
    rw [pointAction_conjugation]
    change pointAction g (corePermutationAction x ((pointAction g)⁻¹ p))=p
    rw [show corePermutationAction x ((pointAction g)⁻¹ p) = (pointAction g)⁻¹ p from hfix _ hi]
    exact (pointAction g).apply_symm_apply p
  obtain ⟨y,hy,he⟩ := translations_image.ge hq
  have hcop : (Nat.card Uniqueness.quotientMap.ker).Coprime 2 := by
    rw [Uniqueness.quotientMap_ker,center_card]
    decide
  have hye : y^2=1 := by
    let := translations_elementary
    exact elemPow_eq_one_of_isElementaryAbelian y hy
  have hxy : derivedConjugation g x = y :=
    Uniqueness.quotientMap.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
      Uniqueness.quotientMap_ker.le hcop he.symm
      (by rw [←map_pow,hxi]; exact map_one _) hye
  exact ⟨derivedConjugation g x,hxy.symm ▸ hy,rfl⟩

/-- The checked matrix translations are the WHOLE full hexad two-core. -/
theorem translations_eq_twoCore : translations.map coverInclusion =
    (nativeHexadStabilizer m22Hexad123).pCoreIn 2 := by
  let := translations_elementary
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map coverInclusion
  have hle : P ≤ (nativeHexadStabilizer m22Hexad123).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 P) P_le P_normalized
  apply eq_of_le_of_card_ge hle
  have hinj : Function.Injective coverInclusion := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : actionGroup => x.val) he)
  have hc : Nat.card P = 16 := by
    rw [P,card_map_of_injective hinj,translations_card]
  rw [hc]
  exact twoCore_card_le m22Hexad123_mem

/-- The standard full-two-core fixed space is the checked six-coordinate space. -/
theorem fixedSpace_eq : nativeHexadFixedSpace m22Hexad123 = fixedSpace := by
  ext v
  rw [fixedSpace_iff_translations]
  change (∀ g ∈ (nativeHexadStabilizer m22Hexad123).pCoreIn 2, binaryAction g v=v) ↔ _
  rw [←translations_eq_twoCore]
  constructor
  · intro hv g hg
    have hh := hv _ (mem_map_of_mem coverInclusion hg)
    simpa only [VectorOrbits.binaryAction_cover] using hh
  · rintro hv _ ⟨g,hg,rfl⟩
    rw [VectorOrbits.binaryAction_cover]
    exact hv g hg

theorem standard_card : Nat.card (nativeHexadFixedSpace m22Hexad123)=64 := by
  rw [fixedSpace_eq,fixedSpace_card]

theorem standard_singular (v : BinarySpace) (hv : v ∈ nativeHexadFixedSpace m22Hexad123) :
    Unitary.quadraticForm v=0 :=
  fixedSpace_singular v (fixedSpace_eq ▸ hv)

end NativeHexadRealization
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
