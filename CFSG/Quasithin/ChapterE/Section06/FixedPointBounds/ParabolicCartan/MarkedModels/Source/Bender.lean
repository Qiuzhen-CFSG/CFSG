module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.StarCoordinates
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSourceCases
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Full Bender Borel markings on the original normal component

The actual maximal overlap in H/J is the normalizer of the prescribed
component Sylow subgroup. Transport that same Sylow through the concrete
linear, Suzuki, or unitary model. Sylow conjugacy and the genuine matrix
normalizer calculations then supply one component equivalence carrying
the original overlap to the named Borel. The unitary case keeps the same
coefficient involution while changing to an actual antidiagonal basis.

Every Bender family now has the complete marked source row, including
the exact field parameter and fixed field. There is no Borel or normalizer
premise and no assertion about the ambient generation parameter.
Source: Aschbacher–Smith E.2.2(2a), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
variable {H : Type*} [Group H] [Finite H]

private theorem unmark_conjugate {X Y : Type*} [Group X] [Group Y]
    (A:Subgroup X) (B:Subgroup Y) (e:X≃*Y) (g:Y)
    (h:A.map e.toMonoidHom=B.map (MulAut.conj g).toMonoidHom) :
    ∃ d:X≃*Y, A.map d.toMonoidHom=B := by
  refine ⟨e.trans (MulAut.conj g⁻¹),?_⟩
  change A.map ((MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom) = B
  rw [←map_map,h,map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Y := by
    ext x
    simp [mul_assoc]
  rw [he,map_id]

theorem source_bender_sylow_normalizer (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤)
    (hm:ClassificationModels.IsBenderModel (sourceImage (ChapterB.minimalParabolicMax T hP) K)) :
    ∃ S:Sylow 2 (sourceImage (ChapterB.minimalParabolicMax T hP) K),
      componentOverlap (ChapterB.minimalParabolicMax T hP) K = normalizer (S:Set _) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := sourceKernel M
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := sourceImage M K
  let : D.Normal := (Structure.source_normal_simple_image T hP hs K hK hgen).2.2.1
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal D
  have hc := Structure.source_original_star_bender T hP hs K hK hgen hm
  refine ⟨R,?_⟩
  rw [source_overlap_coordinate]
  change ((M.map (QuotientGroup.mk' J)).subgroupOf D) = normalizer (R:Set D)
  rw [show (R:Set D) = ((S:Subgroup (H⧸J)).subgroupOf D:Set D) from congrArg SetLike.coe hR]
  exact hc.1

theorem source_linear_borel_model (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {n:ℕ} (hn:2≤n)
    (hm:ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^n)) :
    ExchangedModel (ChapterB.minimalParabolicMax T hP) K n := by
  let D := sourceImage (ChapterB.minimalParabolicMax T hP) K
  obtain ⟨S,hS⟩ := source_bender_sylow_normalizer T hP hs K hK hgen (.linear n hn hm)
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let Q := S.mapSurjective (f:=e.toMonoidHom) e.surjective
  let P := ChapterF.Source.Linear.projectiveSylow F
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) P Q
  have hP : (P:Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).map
      (MulAut.conj g).toMonoidHom = (Q:Subgroup _) := congrArg Sylow.toSubgroup hg
  have hN : (normalizer (S:Set _)).map e.toMonoidHom =
      (BenderSuzuki.Converse.PBorel F).map (MulAut.conj g).toMonoidHom := by
    change (normalizer ((S:Subgroup D):Set D)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    change normalizer ((Q:Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)):Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = _
    rw [← ChapterF.Source.Linear.projectiveSylow_normalizer F]
    change normalizer ((Q:Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)):Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = (normalizer ((P:Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)):Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))).map _
    rw [map_equiv_normalizer_eq,hP]
  obtain ⟨d,hd⟩ := unmark_conjugate _ (BenderSuzuki.Converse.PBorel F) e g (hS.symm ▸ hN)
  exact Or.inl ⟨F,hF,hfin,inferInstance,hn,hcard,d,hd⟩

theorem source_suzuki_borel_model (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {m:ℕ} (hm:1≤m)
    (he:Nonempty (sourceImage (ChapterB.minimalParabolicMax T hP) K ≃* SuzukiMatrixGroup m)) :
    ExchangedModel (ChapterB.minimalParabolicMax T hP) K (2*m+1) := by
  let D := sourceImage (ChapterB.minimalParabolicMax T hP) K
  obtain ⟨S,hS⟩ := source_bender_sylow_normalizer T hP hs K hK hgen (.suzuki m hm he)
  obtain ⟨e⟩ := he
  let Q := S.mapSurjective (f:=e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := ChapterF.Source.suzuki_sylow_normalizer_eq_conjugate_borel m Q
  have hN : (normalizer (S:Set D)).map e.toMonoidHom =
      (SuzukiBorelSubgroup m).map (MulAut.conj g).toMonoidHom := by
    change (normalizer ((S:Subgroup D):Set D)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact hg
  obtain ⟨d,hd⟩ := unmark_conjugate _ (SuzukiBorelSubgroup m) e g (hS.symm ▸ hN)
  exact Or.inr ⟨m,hm,rfl,d,hd⟩

theorem source_unitary_borel_model (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {n:ℕ} (hn:2≤n)
    (hm:ClassicalGroup.IsPSU (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2^n)) :
    UnitaryModel (ChapterB.minimalParabolicMax T hP) K n := by
  let D := sourceImage (ChapterB.minimalParabolicMax T hP) K
  obtain ⟨S,hS⟩ := source_bender_sylow_normalizer T hP hs K hK hgen (.unitary n hn hm)
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := ChapterF.Source.Unitary.charP_two n (by omega) hcard
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective e e.surjective
  let Q := S.mapSurjective (f:=e.toMonoidHom) e.surjective
  obtain ⟨C,hC,g,hg⟩ := ChapterF.Source.Unitary.psu_sylow_normalizer_eq_matrix_borel
    J n (by omega) hcard hconj Q
  let J0 := ChapterF.Source.Unitary.FormTransport.standardForm J
  let d := e.trans (ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC)
  have hN : (componentOverlap (ChapterB.minimalParabolicMax T hP) K).map d.toMonoidHom =
      (unitaryBorel J0 rfl).map (MulAut.conj g).toMonoidHom := by
    change (componentOverlap (ChapterB.minimalParabolicMax T hP) K).map
      ((ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC).toMonoidHom.comp e.toMonoidHom) = _
    rw [←map_map,hS]
    change ((normalizer ((S:Subgroup D):Set D)).map e.toMonoidHom).map _ = _
    rw [map_equiv_normalizer_eq]
    change (normalizer (Q:Set (ProjectiveSpecialUnitaryMatrixGroup J))).map _ = _
    rw [hg,map_comap_eq_self_of_surjective (ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC).surjective]
  obtain ⟨d',hd⟩ := unmark_conjugate _ (unitaryBorel J0 rfl) d g hN
  exact ⟨F,hF,hfin,inferInstance,J0,rfl,hn,hcard,hconj,
    ChapterF.Source.Unitary.fixed_card J0 n (by omega) hcard hconj,d',hd⟩

theorem source_bender_model (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤)
    (hm:ClassificationModels.IsBenderModel (sourceImage (ChapterB.minimalParabolicMax T hP) K)) :
    ∃n:ℕ, BenderModel (ChapterB.minimalParabolicMax T hP) K n := by
  cases hm with
  | linear n hn hm => exact ⟨n,Or.inl (source_linear_borel_model T hP hs K hK hgen hn hm)⟩
  | suzuki m hm he => exact ⟨2*m+1,Or.inl (source_suzuki_borel_model T hP hs K hK hgen hm he)⟩
  | unitary n hn hm => exact ⟨n,Or.inr (source_unitary_borel_model T hP hs K hK hgen hn hm)⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
