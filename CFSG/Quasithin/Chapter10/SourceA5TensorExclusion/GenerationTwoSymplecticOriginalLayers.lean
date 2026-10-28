module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSecondary

/-!
# The original natural layer before critical-distance reduction

The four-field source module is fully moved by the residual. Its original
omega-center orbit therefore equals the graph layer U at every M-vertex,
without a distance-two assumption. Original center-freeness eliminates the
fixed kernel of the natural cover, giving order 256.

Source: Aschbacher--Smith 9.3.6--7, p.734; MS93 (3.2)(vi), pp.863--866.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.CoreReconstruction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}
namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

theorem omegaOrbit_residual_commutator :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ⁅omegaOrbit R,pResidual 2 c.M⁆ = omegaOrbit R := by
  intro R
  obtain ⟨_,_,_,_,hr,_,hKN,hm,_⟩ := c.fourField_models c.hasMaximalOutside
  let := hr.normal
  let := hr.elementary
  rw [ChapterB.QuasisimpleSource.moved_comp_map,map_subgroupOf_eq_of_le hKN] at hm
  have he := NormalElementaryQuotient.commutatorSpace_eq (omegaOrbit R)
    (actionMk (omegaOrbit R)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (pResidual 2 c.M)
  have htop : NormalElementaryQuotient.commutatorSpace (omegaOrbit R) (pResidual 2 c.M) = ⊤ :=
    he.trans hm
  apply le_antisymm (commutator_le_left _ _)
  intro x hx
  exact (show Additive.ofMul (⟨x,hx⟩ : omegaOrbit R) ∈
    NormalElementaryQuotient.commutatorSpace (omegaOrbit R) (pResidual 2 c.M) from
      htop ▸ Submodule.mem_top)

theorem original_Z_eq_U :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ a : Vertex R, color R a = false → Z R a = U R a := by
  intro R a ha
  have he : Z R (alpha R) = U R (alpha R) := by
    rw [U,Z_alpha_eq_omegaOrbit,Ltilde_alpha,←map_commutator,c.omegaOrbit_residual_commutator]
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have hz := Z_act R g (alpha R)
  have hu := U_act R g (alpha R)
  simp only [alpha,act_mVertex,one_mul] at hz hu he
  rw [hz,hu,he]

end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.CoreReconstruction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

theorem original_Z_card
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Theory.SpecificGroups.SymplecticFour.Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ a : Vertex R, color R a = false → Nat.card (Z R a) = 256 := by
  intro R a ha
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hc,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
      c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1
    ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
    c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  obtain ⟨geometry,hpos,_⟩ := c.exists_positive_even_geometry eK
  let := geometry.Z_elementary hpos a ha
  let : IsElementaryAbelian 2 (U R a) := c.original_Z_eq_U a ha ▸ inferInstance
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    rw [←c.graph_X_fixed_eq_bot a ha]
    exact inf_le_inf ((U_le_Z a).trans (geometry.omega_bound a ha (by rwa [geometry.distance_constant a ha]))) le_rfl
  rw [c.original_Z_eq_U a ha]
  exact original_initial_card_of_fixed_eq_bot R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hc hBC hsq ha hfixed
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
