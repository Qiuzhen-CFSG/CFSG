module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import Theory.GroupTheory.CComponent.ResidualLifting
public import Theory.GroupTheory.CentralizerModulo

/-!
# A literal component fixing the original core section

A normal section centralizer with nontrivial simple image has full image.
Residual generation lifts a component inside that very centralizer. Distinct
components commute modulo the ambient two-core, so simplicity of the common
image makes this component normal. The full original action kernel remains
unrestricted throughout.

Source: Aschbacher--Smith 1.2.1 and 12.7.16, printed pp.504 and844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03
open ChapterA.Section02
variable {G F : Type*} [Group G] [Finite G] [Group F] [Finite F]

private theorem sqtk_quotient (hG : IsSQTK KnownSimple.IsKnownSimple G) :
    IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
  refine ⟨?_,hG.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hG.stronglyQuasithin p hp ho)

omit [Finite F] in
private theorem component_lift [IsQuasisimple F]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (f : G →* F) (hf : Function.Surjective f) :
    ∃ B : Subgroup G, B.IsCComponent ∧ B.map f=⊤ := by
  let : IsQuasisimple (⊤ : Subgroup F) := IsQuasisimple.of_mulEquiv topEquiv.symm
  apply exists_cComponent_map_eq_of_preimage_layer f hf
    (show IsComponent F ⊤ from ⟨.top,inferInstance⟩).isCComponent
  exact Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
    (fun X _ _ hX hO => SourceComponents.generation
      (fun Y _ _ => theoremA_knownSimple (G:=Y))
      (SourceComponents.source_model_inputs_of_theoremC (fun Y _ _=>theoremC_knownSimple (G:=Y))) hX hO)
    (sqtk_quotient (hG.subgroup ((⊤ : Subgroup F).comap f)))

/-- The actual simple image is carried by a normal original C-component
that centralizes the same original two-core section. -/
theorem cComponent_full_image_centralizes_core_section
    [IsSimpleGroup F] [IsQuasisimple F]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (f : G →* F) (hf : Function.Surjective f)
    (W J : Subgroup G) [W.Normal]
    (hJ : J.map f≠⊥) (hcomm : ⁅pCore 2 G,J⁆≤W) :
    ∃ B : Subgroup G, B.IsCComponent ∧ B.Normal ∧ B.map f=⊤ ∧ ⁅pCore 2 G,B⁆≤W := by
  let Q := pCore 2 G
  have hQker : Q≤f.ker := by
    let N := Q.map f
    let : N.Normal := Normal.map inferInstance f hf
    have hp : IsPGroup 2 N := pCore_isPGroup.map f
    have hz : N=⊥ := by
      rcases (inferInstance : N.Normal).eq_bot_or_eq_top with hz | ht
      · exact hz
      · let : Group.IsNilpotent N := hp.isNilpotent
        let : Group.IsSolvable F := Group.isSolvable_of_surjective
          (f:=N.subtype) (by intro x; exact ⟨⟨x,ht ▸ mem_top x⟩,rfl⟩)
        exact (Group.IsPerfect.not_isSolvable F inferInstance).elim
    exact (map_eq_bot_iff Q).mp hz
  let C := centralizerModulo ⊤ Q W
  let : (Q.map (QuotientGroup.mk' W)).Normal := Normal.map inferInstance _
    (QuotientGroup.mk'_surjective W)
  let : C.Normal := by dsimp only [C,centralizerModulo]; infer_instance
  have hJC : J≤C := fun j hj=>mem_centralizerModulo_iff.mpr
    ⟨mem_top _,fun q hq=>hcomm (commutator_mem_commutator hq hj)⟩
  have hCf : C.map f=⊤ := by
    let : (C.map f).Normal := Normal.map inferInstance f hf
    rcases (inferInstance : (C.map f).Normal).eq_bot_or_eq_top with hz | ht
    · exact (hJ (le_bot_iff.mp ((map_mono hJC).trans_eq hz))).elim
    · exact ht
  let c := f.comp C.subtype
  have hc : Function.Surjective c := by
    intro y
    obtain ⟨g,hg,hgy⟩ := (show y∈C.map f from hCf.symm ▸ mem_top y)
    exact ⟨⟨g,hg⟩,hgy⟩
  obtain ⟨B0,hB0,hB0f⟩ := component_lift (hG.subgroup C) c hc
  let B := B0.map C.subtype
  have hB : B.IsCComponent := hB0.map_subtype (inferInstance : C.Normal).isSubnormal
  have hBf : B.map f=⊤ := by rw [show B=B0.map C.subtype from rfl,map_map]; exact hB0f
  have hBC : B≤C := map_subtype_le _
  have hnB : B.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    let D := B.map (MulAut.conj g).toMonoidHom
    have hD : D.IsCComponent := hB.map_equiv (MulAut.conj g)
    have hDf : D.map f=⊤ := by
      have he : f.comp (MulAut.conj g).toMonoidHom=(MulAut.conj (f g)).toMonoidHom.comp f := by
        ext x
        change f (g*x*g⁻¹)=f g*f x*(f g)⁻¹
        simp only [map_mul,map_inv]
      rw [show D=B.map (MulAut.conj g).toMonoidHom from rfl,map_map,he,←map_map,hBf]
      exact map_top_of_surjective _ (MulAut.conj (f g)).surjective
    have he : D=B := by
      by_contra hne
      have hbd := CComponentCommutation.proposition_1_2_1_two (sqtk_quotient hG) hB hD (Ne.symm hne)
      have hz : (⁅B,D⁆).map f=⊥ := (Subgroup.map_eq_bot_iff _).mpr
        (hbd.1.trans (hbd.2.trans hQker))
      rw [map_commutator,hBf,hDf] at hz
      have ht : ⁅(⊤ : Subgroup F),⊤⁆=⊤ := Group.IsPerfect.commutator_eq_top
      exact bot_ne_top (hz.symm.trans ht)
    exact mem_normalizer_iff_map_conj_eq.mpr he
  refine ⟨B,hB,hnB,hBf,?_⟩
  apply commutator_le.mpr
  intro q hq b hb
  exact (mem_centralizerModulo_iff.mp (hBC hb)).2 q hq

end CFSG.Quasithin.ChapterA.Section03
