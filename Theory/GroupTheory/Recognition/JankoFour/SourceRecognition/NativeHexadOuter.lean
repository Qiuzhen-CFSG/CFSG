module
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates
public import Theory.Mathieu.M22.Properties.OuterCentralizers.DesignAction

/-!
# An outer involution preserving the marked native hexad section

The native A6 section fixes a specified point outside the hexad. Transport
an odd design involution fixing the standard hexad and point 4 to this exact
flag, using the regular pointwise-kernel action for the point adjustment.
The resulting involution preserves the published A6 section, since that
section is exactly the inner stabilizer of the same flag.

This is the native input for extending the original marker-free subgroup
in HexadOuterComplement, with its literal Mathieu application.
Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.8), p.599, DOI 10.1007/BF01232280.
-/
@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu
noncomputable section

def hexadSectionImage {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) : Subgroup M22 :=
  ((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range

private theorem section_recovers {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MulAction.stabilizer M22 B)
    (hg : g.val • Classical.choose (exists_m22Hexad_complementary_point hB) =
      Classical.choose (exists_m22Hexad_complementary_point hB)) :
    m22HexadSection hB ((m22HexadMarking hB).symm (m22HexadSixMap hB g)) = g := by
  let E := MulEquiv.ofBijective _ (m22HexadSixMap_pointStabilizer_bijective hB
    (Classical.choose_spec (exists_m22Hexad_complementary_point hB)))
  change m22HexadPointSection hB (Classical.choose_spec (exists_m22Hexad_complementary_point hB))
    (m22HexadMarking hB ((m22HexadMarking hB).symm (m22HexadSixMap hB g))) = g
  rw [MulEquiv.apply_symm_apply]
  exact congrArg Subtype.val (E.symm_apply_apply ⟨g,hg⟩)

theorem hexadSectionImage_mem_iff {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (a : M22) :
    a ∈ hexadSectionImage hB ↔ a • B = B ∧
      a • Classical.choose (exists_m22Hexad_complementary_point hB) =
        Classical.choose (exists_m22Hexad_complementary_point hB) := by
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨(m22HexadSection hB b).property,
      m22HexadPointSection_fixes hB (Classical.choose_spec (exists_m22Hexad_complementary_point hB)) (m22HexadMarking hB b)⟩
  · rintro ⟨hB',hp⟩
    let b : MulAction.stabilizer M22 B := ⟨a,hB'⟩
    exact ⟨(m22HexadMarking hB).symm (m22HexadSixMap hB b),
      congrArg Subtype.val (section_recovers hB b hp)⟩

private theorem flag_conjugator {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    {p : Fin 22} (hp : p ∉ B) :
    ∃ g : M22, g • m22Hexad123 = B ∧ g • (4 : Fin 22) = p := by
  obtain ⟨g,hg⟩ := exists_smul_m22Hexad123_eq hB
  have h4 : g • (4 : Fin 22) ∉ B := by
    rw [←hg]
    simpa using (show (4 : Fin 22) ∉ m22Hexad123 by decide +kernel)
  obtain ⟨u,hu⟩ := (m22HexadKernel_regular hB h4).surjective ⟨p,hp⟩
  refine ⟨u.val.val*g,?_,?_⟩
  · rw [mul_smul,hg]
    exact u.val.property
  · rw [mul_smul]
    exact congrArg Subtype.val hu

/-- An outer involution preserving both the hexad and its chosen complementary point. -/
theorem exists_hexad_outer_involution {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ t : m22DesignAut, orderOf t=2 ∧ t.val ∉ M22 ∧ t • B=B ∧
      t • Classical.choose (exists_m22Hexad_complementary_point hB) =
        Classical.choose (exists_m22Hexad_complementary_point hB) := by
  obtain ⟨g,hg,hgp⟩ := flag_conjugator hB
    (Classical.choose_spec (exists_m22Hexad_complementary_point hB))
  let v : m22DesignAut := ⟨g.val,M22_le_m22DesignAut g.property⟩
  let t := MulAut.conj v m22OuterDesignAut
  have ht : orderOf t=2 := ((MulAut.conj v).orderOf_eq _).trans m22OuterDesignAut_order
  have hout : t.val ∉ M22 := by
    intro hi
    have he : m22OuterDesignAut = v⁻¹*t*v := by dsimp [t]; group
    apply m22OddPairSwap_not_mem_M22
    change m22OuterDesignAut.val ∈ M22
    rw [he]
    exact M22.mul_mem (M22.mul_mem (M22.inv_mem g.property) hi) g.property
  have hB0 : m22OuterDesignAut • m22Hexad123=m22Hexad123 := by decide +kernel
  have hp0 : m22OuterDesignAut • (4 : Fin 22)=4 := by decide +kernel
  refine ⟨t,ht,hout,?_,?_⟩
  · rw [←hg]
    change (v*m22OuterDesignAut*v⁻¹) • (v • m22Hexad123)=v • m22Hexad123
    simp only [mul_smul,inv_smul_smul,hB0]
  · rw [←hgp]
    change (v*m22OuterDesignAut*v⁻¹) • (v • (4 : Fin 22))=v • (4 : Fin 22)
    simp only [mul_smul,inv_smul_smul,hp0]

/-- The actual outer design involution normalizes the published native A6 section. -/
theorem hexadSectionImage_stable {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (t : m22DesignAut) (hB' : t • B=B)
    (hp : t • Classical.choose (exists_m22Hexad_complementary_point hB) =
      Classical.choose (exists_m22Hexad_complementary_point hB)) :
    (hexadSectionImage hB).map (m22DesignAutToAut t).toMonoidHom = hexadSectionImage hB := by
  have stable (t : m22DesignAut) (hB' : t • B=B)
      (hp : t • Classical.choose (exists_m22Hexad_complementary_point hB) =
        Classical.choose (exists_m22Hexad_complementary_point hB))
      (a : M22) (ha : a ∈ hexadSectionImage hB) :
      m22DesignAutToAut t a ∈ hexadSectionImage hB := by
    obtain ⟨haB,hap⟩ := (hexadSectionImage_mem_iff hB a).mp ha
    have hperm : (m22DesignAutToAut t a).val = t.val*a.val*t.val⁻¹ := m22DesignAutToAut_apply_perm t a
    apply (hexadSectionImage_mem_iff hB _).mpr
    constructor
    · change (m22DesignAutToAut t a).val • B=B
      rw [hperm,mul_smul,mul_smul]
      change t • (a • (t⁻¹ • B))=B
      rw [inv_smul_eq_iff.mpr hB'.symm,haB,hB']
    · change (m22DesignAutToAut t a).val • Classical.choose (exists_m22Hexad_complementary_point hB) = Classical.choose (exists_m22Hexad_complementary_point hB)
      rw [hperm,mul_smul,mul_smul]
      change t • (a • (t⁻¹ • Classical.choose (exists_m22Hexad_complementary_point hB))) = Classical.choose (exists_m22Hexad_complementary_point hB)
      rw [inv_smul_eq_iff.mpr hp.symm,hap,hp]
  apply le_antisymm
  · rintro a ⟨b,hb,rfl⟩
    exact stable t hB' hp b hb
  · intro a ha
    refine ⟨m22DesignAutToAut t⁻¹ a,stable t⁻¹
      (inv_smul_eq_iff.mpr hB'.symm) (inv_smul_eq_iff.mpr hp.symm) a ha,?_⟩
    rw [map_inv]
    exact (m22DesignAutToAut t).apply_symm_apply a
end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
