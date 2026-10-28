module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.PointImages
public import CFSG.Quasithin.ChapterB.Section02.Baumann.TwoConjugates
public import Theory.Representation.G2BinaryPointGeneration
/-!
# Baumann decomposition for the full binary G₂ point action

The actual coordinate action identifies its kernel with the module
centralizer. The two explicit root eights generate the full model and
have fixed codimensions three and three, while the residual has
codimension six. Lift the odd-order conjugator through the original
action map and apply B.2.18. This proves the alpha decomposition and
centralizer saturation on the literal original subgroups.
Source: Aschbacher–Smith C.1.37 and 13.3.10(2), pp.143,887–888.
The ambient source application is CoreContainment.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterB ChapterB.BaumannArgument Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
variable (q : G →* Atlas.G2.Model F) (hq : Function.Surjective q)
variable (E : Additive V ≃ₗ[F] W)
variable (he : ∀ g v, E (Additive.ofMul (MulAut.conjNormal g v)) =
  Atlas.G2.Restricted.NaturalCoordinates.action F (q g) (E (Additive.ofMul v)))

include hq he

private theorem unitary_codimension (A : Subgroup G) :
    BaumannArgument.fixedCodim V A = BinaryOffender.fixedCodim
      (Atlas.G2.Restricted.NaturalCoordinates.action F) (A.map q) := by
  have hk := unitary_coordinate_kernel V q E he
  let τ := NormalElementaryQuotient.representation V q hq hk
  have he' (g : Atlas.G2.Model F) (v : Additive V) :
      E (τ g v) = Atlas.G2.Restricted.NaturalCoordinates.action F g (E v) := by
    obtain ⟨g,rfl⟩ := hq g
    have hr := NormalElementaryQuotient.representation_apply V q hq hk g v
    have hh : (τ (q g) v).toMul = MulAut.conjNormal g v.toMul := Subtype.ext hr
    exact (congrArg (fun w : V => E (Additive.ofMul w)) hh).trans (he g v.toMul)
  rw [fixedCodim_eq_centralizer_quotient V q hq hk]
  have ht := fixedCodim_map_equivariant τ
    (Atlas.G2.Restricted.NaturalCoordinates.action F)
    (MonoidHom.id (Atlas.G2.Model F)) E he' (A.map q)
  simpa only [Subgroup.map_id] using ht

/-- The genuine full natural action discharges all generation and dimension
hypotheses of Baumann's argument for the marked point Thompson image. -/
theorem unitary_point_baumann_decomposition
    (R : Subgroup G) (hR : IsPGroup 2 R) (hVR : V ≤ R) (hQR : pCore 2 G ≤ R)
    (hC : centralizer (V : Set G) = pCore 2 G)
    (hJ : (elementaryAbelianMaxJ R).map q = Atlas.G2.BinaryCore.elementary) :
    (pResidual 2 G).pCoreIn 2 ≤ baumann R ∧
      thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) ∧
      baumann R ⊓ centralizer (V : Set G) =
        (pResidual 2 G ⊔ baumann R) ⊓ centralizer (V : Set G) := by
  have hk := unitary_coordinate_kernel V q E he
  have hm : (pResidual 2 G).map q = pResidual 2 (Atlas.G2.Model F) :=
    map_pResidual_of_surjective 2 q hq
  obtain ⟨a,ha,hgen⟩ := Atlas.G2.Natural.BinaryPointGeneration.exists_residual_conjugate_generating
  obtain ⟨g,hg,hqg⟩ := (show a ∈ (pResidual 2 G).map q from hm.symm ▸ ha)
  have hmap : ((elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom).map q =
      ((elementaryAbelianMaxJ R).map q).map (MulAut.conj a).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,hqg]
  have hgenerates : (pResidual 2 G).map q ≤ (elementaryAbelianMaxJ R).map q ⊔
      ((elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom).map q := by
    rw [hmap,hJ,hgen]
    exact le_top
  have hthree : BinaryOffender.fixedCodim (Atlas.G2.Restricted.NaturalCoordinates.action F)
      (Atlas.G2.EvenTwoRank.elementary F) = 3 := by
    exact Atlas.G2.NaturalOffenders.fixedCodim_elementary (F := ZMod 2) (n := 1) (by norm_num)
  have hcod : 2 * BaumannArgument.fixedCodim V (elementaryAbelianMaxJ R) ≤
      BaumannArgument.fixedCodim V (pResidual 2 G) := by
    rw [unitary_codimension V q hq E he,unitary_codimension V q hq E he,hJ,hm,
      Atlas.G2.Natural.BinaryModelOffenders.elementary_eq,
      hthree,
      Atlas.G2.Natural.BinaryPointGeneration.fixedCodim_residual]
  exact two_conjugate_baumann_of_core_kernel R hR hQR V hVR hC q hk
    (unitary_no_strong_and_le_baumann V q E hk he R hVR).1 g hg hgenerates hcod
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
