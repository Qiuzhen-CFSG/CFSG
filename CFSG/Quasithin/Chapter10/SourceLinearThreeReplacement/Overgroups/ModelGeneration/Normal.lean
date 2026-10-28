module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Binary
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.Complete

/-!
# Normal component quotients and the odd-prime generation branch

The image of the original component in H/O₂(H) is its literal own
two-core quotient. When this quotient is simple, it equals F*(H/O₂(H)):
normality and the full Sylow supplement give a two-group outer quotient.
The completed odd PSL₂ theorem therefore applies, and E-generation lifts
through the original two-core. This discharges the invariant odd-prime
row and supplies the identical quotient transport for Held.

Source: Aschbacher--Smith E.1.11--14, pp.212--214, used in 10.3.3, pp.756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
open ChapterE
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem normal_component_quotient_structure
    (S : Sylow 2 H) (K : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hgen : K ⊔ (S : Subgroup H) = ⊤) :
    IsSimpleGroup (generalizedFitting (H ⧸ pCore 2 H)) ∧
      Nonempty (generalizedFitting (H ⧸ pCore 2 H) ≃* (K ⧸ pCore 2 K)) ∧
      generalizedFitting (H ⧸ pCore 2 H) ⊔
        (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)) :
          Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.map q
  let b := cComponentTwoCoreQuotientEquiv hK
  let : B.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup B := b.symm.isSimpleGroup
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  have hBS : B ⊔ (S : Subgroup H).map q = ⊤ := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hF := (simple_two_quotient_structure B (Group.IsPerfect.not_isMulCommutative B)
    (isPGroup_quotient_of_sup_eq_top B ((S : Subgroup H).map q) (S.isPGroup'.map q) hBS)
    (pCore_quotient_pCore_eq_bot 2)).1
  let e := (MulEquiv.subgroupCongr hF).trans b.symm
  refine ⟨e.isSimpleGroup, ⟨e⟩, ?_⟩
  change generalizedFitting (H ⧸ pCore 2 H) ⊔ (S : Subgroup H).map q = ⊤
  rw [hF]
  exact hBS

theorem isEGenerated_of_normal_odd_component (hH : IsSQTK κ H)
    (S : Sylow 2 H) (K : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] (hgen : K ⊔ (S : Subgroup H) = ⊤)
    {p : ℕ} (ho : Odd p) (hp : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) : IsEGenerated 1 H := by
  have hs : IsSimpleGroup (K ⧸ pCore 2 K) := by
    obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact e.isSimpleGroup
  let := hs
  obtain ⟨hsF, ⟨e⟩, hFS⟩ := normal_component_quotient_structure S K hK hgen
  let := hsF
  apply IsEGenerated.of_normal_two_subgroup (pCore 2 H) pCore_isPGroup
  exact ValuesOdd.PSLTwoGeneration.isEGenerated_one_of_model
    (sqtk_quotient_of_two_kernel hH _ pCore_isPGroup)
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) hFS ho (by omega) (hm.of_mulEquiv e)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
