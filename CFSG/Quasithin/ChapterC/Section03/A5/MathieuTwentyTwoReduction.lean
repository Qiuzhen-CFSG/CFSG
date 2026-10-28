module
public import CFSG.Quasithin.ChapterC.Section03.A5.MathieuTwentyThree
public import Theory.Mathieu.M22.ChapterHLocalClassification
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates.Coordinates

/-!
# The hexad obstruction for the original alternating-five block in M22

The intrinsic Sylow catalogue places every elementary sixteen-group in a
conjugate of the hexad or quintet core. In the hexad case, full normalizer
control makes the original block normal in the actual hexad stabilizer.
Its simple A6 quotient cannot have the normal A5 quotient of that block.
Thus the source block's literal U is a conjugate of the intrinsic quintet
core. `MathieuTwentyTwo` applies its natural actor to exclude that remaining core.

Source: Aschbacher--Smith H.14.3, printed p.397, and the deleted-five
branch of 13.5.15 on printed p.921. All conjugators and core maps are retained.
-/

public section
open Subgroup Sporadic.Mathieu MathieuCode
namespace CFSG.Quasithin.ChapterC

/-- Global form of the native inner-Sylow catalogue. -/
private theorem m22_card16_conjugate_intrinsic_core (A : Subgroup M22)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    ∃ g : M22,
      A = (m22InnerHexadKernel m22SourceOctad).map (MulAut.conj g).toMonoidHom ∨
      A = (m22InnerQuintetKernel m22SourceSextet).map (MulAut.conj g).toMonoidHom := by
  let := hA
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 M22ChapterH.CompatibleSylow.inner P
  have hP : (P : Subgroup M22) =
      M22ChapterH.CompatibleSylow.inner.toSubgroup.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBc : Nat.card B = 16 :=
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans hc
  have hBS : B ≤ M22ChapterH.CompatibleSylow.inner.toSubgroup := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx, hxa⟩ := (hP ▸ hAP ha)
    have he : (MulAut.conj g⁻¹) a = x := by
      rw [← hxa]
      simp [MulAut.conj_apply, mul_assoc]
    exact he ▸ hx
  have hback : B.map (MulAut.conj g).toMonoidHom = A := by
    rw [map_map]
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id M22 := by
      ext a
      simp [MulAut.conj_apply, mul_assoc]
    rw [he, map_id]
  refine ⟨g, ?_⟩
  rcases (M22ChapterH.intrinsic_sylow_catalogue.2.1 B).mp ⟨hB,hBc,hBS⟩ with hb | hb
  · exact Or.inl (hback.symm.trans (congrArg (fun C : Subgroup M22 =>
      C.map (MulAut.conj g).toMonoidHom) hb))
  · exact Or.inr (hback.symm.trans (congrArg (fun C : Subgroup M22 =>
      C.map (MulAut.conj g).toMonoidHom) hb))

private theorem m22_hexad_core_normalizer :
    normalizer (m22InnerHexadKernel m22SourceOctad : Set M22) =
      m22InnerHexadStabilizer m22SourceOctad := by
  rw [← M22HexadCoordinates.base_kernel,
    m22HexadPointwiseKernel_normalizer m22Hexad24Ten_mem,
    M22HexadCoordinates.base_stabilizer]

private theorem m22_hexad_no_normal_alternatingFive
    (A : Subgroup (m22InnerHexadStabilizer m22SourceOctad)) [A.Normal] :
    ¬ IsAlternatingBlock A 5 := by
  let H := MathieuCode.Hexad.CocodeAction.SixPointModel.H
  have hH : Nat.card H = 6 := by
    rw [Nat.card_eq_fintype_card]
    exact MathieuCode.Hexad.CocodeAction.SixPointModel.card_H
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; decide)
  let : IsSimpleGroup (alternatingGroup H) := alternatingGroup.isSimpleGroup (by
    simpa only [hH] using (show 5 ≤ (6 : ℕ) by decide))
  apply not_alternatingFive_of_simple_core_quotient M22ChapterH.Hexad.innerQuotientEquiv
  rw [nat_card_alternatingGroup, hH]
  norm_num

/-- Source normalizer control excludes the entire hexad conjugacy branch. -/
theorem native_m22_normalized_alternatingFive_quintet_core
    (A : Subgroup M22) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (hctrl : normalizer ((blockU A).map A.subtype : Set M22) ≤
      normalizer (A : Set M22)) :
    ∃ g : M22, (blockU A).map A.subtype =
      (m22InnerQuintetKernel m22SourceSextet).map (MulAut.conj g).toMonoidHom := by
  let := hA.2.1.elementary
  have hU : IsElementaryAbelian 2 ((blockU A).map A.subtype) := IsElementaryAbelian.map _
  obtain ⟨g,hg⟩ := m22_card16_conjugate_intrinsic_core _ hU hc
  rcases hg with hh | hq
  · exact (no_normalized_alternatingFive_of_conjugate_core A
      (m22InnerHexadStabilizer m22SourceOctad) hA hctrl (MulAut.conj g) hh
      m22_hexad_core_normalizer (fun B hB => by
        let := hB
        exact m22_hexad_no_normal_alternatingFive B)).elim
  · exact ⟨g,hq⟩

end CFSG.Quasithin.ChapterC
