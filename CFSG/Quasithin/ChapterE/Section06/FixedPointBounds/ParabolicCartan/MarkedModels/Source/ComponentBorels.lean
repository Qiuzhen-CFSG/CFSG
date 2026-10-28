module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.Bender
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Placement
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Rank-one Borel markings for every original component

Normality of the selected component is unnecessary for the source Borel
intersection. Its actual star image is a simple ordinary component; its
prescribed Sylow normalizer is an invariant seed in the unique maximal
subgroup. The genuine rank-one geometry then identifies the whole
component overlap with that normalizer. Sylow conjugacy supplies the
literal binary PSL2 or Suzuki Borel marking.

These theorems apply to exchanged original C-components without a Borel,
normalizer or placement premise. The exponent remains independent of the
original generation parameter. Source: Aschbacher–Smith E.2.2(1a) and
E.2.7, printed pp.215–216,218–219.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}
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

theorem source_component_borel_normalizer
    (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H) (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent) (hgen:K⊔(T:Subgroup H)=⊤)
    (hm:ChapterF.Source.IsRankOneModel (sourceImage (ChapterB.minimalParabolicMax T hP) K)) :
    ∃S:Sylow 2 (sourceImage (ChapterB.minimalParabolicMax T hP) K),
      componentOverlap (ChapterB.minimalParabolicMax T hP) K=normalizer (S:Set _) := by
  let M:=ChapterB.minimalParabolicMax T hP
  let J:=sourceKernel M
  let q:=QuotientGroup.mk' J
  let S:=T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D:=sourceImage M K
  have hi:=Structure.source_component_simple_image T hP hs K hK hgen
  let : IsSimpleGroup D:=hi.1
  let : IsQuasisimple D := hi.2.1.2
  have hmin:=(Structure.source_star_minimal_core_free T hP).1
  have hmax:ChapterB.minimalParabolicMax S hmin=M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'];exact le_rfl)).symm
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_subnormal D hi.2.1.1
  have heven:2∣Nat.card D := by
    by_contra hh
    exact Group.IsPerfect.not_isSolvable D (odd_order_theorem D
      (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hh)))
  have ho:=Structure.generating_component_orbit_eq_residual
    (Structure.source_star_sqtk hA hH T hP hs).stronglyQuasithin S hi.2.1 hi.2.2.2
  have hb:=Witnesses.PairedBender.component_borel_intersection S hmin D hi.2.1 heven ho hm
  refine ⟨R,?_⟩
  rw [source_overlap_coordinate]
  change (M.map q).subgroupOf D=normalizer (R:Set D)
  rw [←hmax]
  rw [show (R:Set D)=((S:Subgroup (H⧸J)).subgroupOf D:Set D) from congrArg SetLike.coe hR]
  exact hb

theorem source_component_linear_borel_model (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H) (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent)
    (hgen:K⊔(T:Subgroup H)=⊤) {n:ℕ} (hn:2≤n)
    (hm:ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^n)) :
    ExchangedModel (ChapterB.minimalParabolicMax T hP) K n := by
  let D := sourceImage (ChapterB.minimalParabolicMax T hP) K
  obtain ⟨S,hS⟩ := source_component_borel_normalizer hA hH T hP hs K hK hgen (.linear n (by omega) hm)
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

theorem source_component_suzuki_borel_model (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H) (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent)
    (hgen:K⊔(T:Subgroup H)=⊤) {m:ℕ} (hm:1≤m)
    (he:Nonempty (sourceImage (ChapterB.minimalParabolicMax T hP) K ≃* SuzukiMatrixGroup m)) :
    ExchangedModel (ChapterB.minimalParabolicMax T hP) K (2*m+1) := by
  let D := sourceImage (ChapterB.minimalParabolicMax T hP) K
  obtain ⟨S,hS⟩ := source_component_borel_normalizer hA hH T hP hs K hK hgen (.suzuki m he)
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

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
