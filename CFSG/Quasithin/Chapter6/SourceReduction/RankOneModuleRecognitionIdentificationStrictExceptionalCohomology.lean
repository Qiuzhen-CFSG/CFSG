module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCentralCover
public import CFSG.Quasithin.ChapterG.Section11.FullLinearFourModel
public import Theory.Representation.BinaryNaturalDual.NormalFirstCohomology

/-!
# Vanishing dual cohomology for the actual exceptional layer closure

The literal image of the layer closure is a nontrivial normal subgroup of
the strict actor. Transporting through the exceptional whole-action model
puts inner GL₄(2) inside that image and gives vanishing dual H¹. The actual
central cover U/⟨z⟩ → U/Z(U) then forces the center to have order two.
The source crossed-center order identity consequently makes its image trivial.

Source: Aschbacher--Smith 6.2.15--17, printed pp.688--690, and I.1.5--6,
printed p.408. StrictExceptionalExclusion contradicts this with the marked
geometry of the same whole action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
open ChapterG.Section11.FullLinearFour
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

 theorem LocalAnalysis.strict_layerClosure_image_ne_bot
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    (equalityLayerClosure L R z).map
      (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker) ≠ ⊥ := by
  intro hh
  have hle : strictLayerImage (T : Subgroup G) L R z ≤
      (equalityLayerClosure L R z).map
        (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker) :=
    map_mono (fun _ hx => le_normalClosure hx)
  have hc := card_le_of_le hle
  rw [hh,card_bot] at hc
  have hcard : Nat.card (strictLayerImage (T : Subgroup G) L R z) = 2 :=
    A.strict_layer_actor_image_card h611 hnatural hz horder hstrict
  omega

variable [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
variable [IsElementaryAbelian 2 (EqualityVectorQuotient (T : Subgroup G) L R z)]

omit [IsElementaryAbelian 2 (EqualityVectorQuotient (T : Subgroup G) L R z)] in
 theorem LocalAnalysis.strict_dual_H1_zero_of_full_four
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {D : Subgroup (StrictActor (T : Subgroup G) L R z)}
    {I J : Submodule (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z))}
    (m : WholeActionModel (strictRepresentation (T : Subgroup G) L R z) D I J) :
    Module.finrank (ZMod 2) (H1
      (strictLayerRepresentation A h611 hnatural hz horder hstrict).dual) = 0 := by
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  let K := (equalityLayerClosure L R z).map q
  let N := K.map m.groupEquiv.toMonoidHom
  let : K.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : N.Normal := Subgroup.Normal.map inferInstance _ m.groupEquiv.surjective
  have hN : N ≠ ⊥ := by
    intro hh
    apply A.strict_layerClosure_image_ne_bot h611 hnatural hz horder hstrict
    apply le_bot_iff.mp
    intro g hg
    have he : m.groupEquiv g = 1 := mem_bot.mp (hh ▸ mem_map_of_mem _ hg)
    exact mem_bot.mpr (m.groupEquiv.map_eq_one_iff.mp he)
  let e : StrictLayerActor L R z ≃* N := (A.strict_layerClosure_equiv_image h611 hnatural hz horder hstrict).trans
    (m.groupEquiv.subgroupMap K)
  let d := BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inl (rfl : 4 = 4))
  let σ : Representation (ZMod 2) N (BinaryNaturalDual.CoordinateSpace 4) :=
    d.representation.comp N.subtype
  let ρ := strictLayerRepresentation A h611 hnatural hz horder hstrict
  have he (g : StrictLayerActor L R z)
      (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) :
      m.spaceEquiv (ρ g v) = σ (e g) (m.spaceEquiv v) :=
    m.equivariant _ v
  have hedual (g : StrictLayerActor L R z) (f : Module.Dual (ZMod 2)
      (Additive (StrictVectorQuotient (T : Subgroup G) L R z))) :
      m.spaceEquiv.symm.dualMap (ρ.dual g f) =
        σ.dual (e g) (m.spaceEquiv.symm.dualMap f) := by
    apply LinearMap.ext
    intro v
    change f (ρ g⁻¹ (m.spaceEquiv.symm v)) =
      f (m.spaceEquiv.symm (σ (e g)⁻¹ v))
    congr 1
    apply m.spaceEquiv.injective
    rw [he,m.spaceEquiv.apply_symm_apply,m.spaceEquiv.apply_symm_apply]
    exact congrArg (fun a : N => σ a v) (e.map_inv g)
  let eH := H1Congr ρ.dual σ.dual e m.spaceEquiv.symm.dualMap hedual
  let := BinaryNaturalDual.coordinateAction_normal_dual_H1_subsingleton d N hN
  rw [eH.finrank_eq]
  exact Module.finrank_zero_of_subsingleton

 theorem LocalAnalysis.strict_center_card_of_full_four
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {D : Subgroup (StrictActor (T : Subgroup G) L R z)}
    {I J : Submodule (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z))}
    (m : WholeActionModel (strictRepresentation (T : Subgroup G) L R z) D I J) :
    Nat.card (center (sourceClosure (T : Subgroup G) L R z)) = 2 :=
  A.strict_center_card_of_dual_H1_zero h611 hnatural hz horder hstrict
    (A.strict_dual_H1_zero_of_full_four h611 hnatural hz horder hstrict m)
 theorem LocalAnalysis.strict_crossing_center_image_eq_bot_of_full_four
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {D : Subgroup (StrictActor (T : Subgroup G) L R z)}
    {I J : Submodule (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z))}
    (m : WholeActionModel (strictRepresentation (T : Subgroup G) L R z) D I J)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G)) :
    strictCrossingCenterImage (T : Subgroup G) L R z d = ⊥ := by
  have hC := A.strict_center_card_of_full_four h611 hnatural hz horder hstrict m
  have hc := A.strict_crossing_center_image_card h611 hnatural hz horder hTH hstrict hdres hdH
  rw [hC] at hc
  exact Subgroup.card_eq_one.mp (by omega)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
