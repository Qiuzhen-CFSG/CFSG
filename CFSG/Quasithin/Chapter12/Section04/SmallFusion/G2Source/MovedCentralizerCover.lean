module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.PointGeometry
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.MovedOffenderImage
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.MovedCore
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2SharpFixedIndex

/-!
# The original moving G₂ centralizer cover

The full normalizer actor sends the actual moving module to an elementary
eight in a natural point stabilizer. Its self-centralization restricts to
the original residual core, whose actor kernel is exactly O₂(LT).
Lifting through that kernel proves the literal source centralizer cover.
The sharp fixed-index theorem gives the first core factorization. Its
whole-core continuation supplies the original product with the component
centralizer, elementarity, and the trivial Frattini subgroup.

Source: Aschbacher--Smith 3.3.28, printed p.601; B.4.6(13), printed p.90.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource Atlas.G2.Natural
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2
local notation "W" => TraceZero F

/-- The full actor's point geometry gives the centralizer cover inside the
literal residual core. The marked restriction supplies its derived range. -/
theorem moved_chosen_centralizer_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    omegaResidualCore T L ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) ≤
      V.map (MulAut.conj d).toMonoidHom ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨b, ψ, hψ, hψL⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  have hrange : commutator (Atlas.G2.Model F) ≤ ψ.range := by
    intro g hg
    obtain ⟨l, hl⟩ :=
      (e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) ⟨g, hg⟩
    refine ⟨⟨l, L.le_normalizer l.property⟩, ?_⟩
    rw [hψL]
    exact congrArg Subtype.val hl
  have hcard := (moved_full_actor_offender_image h D structural e hne b ψ hψ hd hmove).2
  have hfull := full_actor_moved_image_selfcentralizing h D structural e hne hescape
    hd b ψ hψ hrange hcard
  let R := omegaResidualCore T L
  let B := V.map (MulAut.conj d).toMonoidHom
  let N := normalizer (L : Set G)
  have hRN : R ≤ N := local_core_containments.2.trans D.sylow_normalizes_component
  have hBR : B ≤ R := conjugate_chosen_le_local_core h D structural e hne hd
  let φ := ψ.comp (inclusion hRN)
  have hφ (r : R) (x : W) := hψ (inclusion hRN r) x
  have hker : φ.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf R := by
    rw [full_g2_actor_ker_eq_centralizer R b φ hφ,
      ← local_centralizer_chosen_eq_core h D structural, inf_subgroupOf_left]
  have himage : (B.subgroupOf R).map φ = (B.subgroupOf N).map ψ := by
    change (B.subgroupOf R).map (ψ.comp (inclusion hRN)) = _
    rw [← map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x.val, hBR hx⟩, hx, rfl⟩
  have hsub : φ.range ≤ ψ.range := by
    rintro x ⟨r, rfl⟩
    exact ⟨inclusion hRN r, rfl⟩
  apply local_centralizer_conjugate_le_of_actor_image h D structural e hne hd φ hker.le
  change φ.range ⊓ centralizer ((B.subgroupOf R).map φ : Set _) ≤ _
  rw [himage]
  exact (inf_le_inf_right _ hsub).trans hfull

/-- The first core factorization for the actual moving chosen module, with
the centralizer-cover and sharp fixed-index premises both discharged. -/
theorem core_eq_chosen_sup_moved_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = V ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G)) := by
  have hb := g2Two_block_of_weyl_model h D hescape e
  have hcover := moved_chosen_centralizer_cover h D structural e hne hescape hd hmove
  have hcover' : blockLocalCore T L ⊓ centralizer
      (((ChapterC.blockU L).map L.subtype).map (MulAut.conj (d⁻¹)⁻¹).toMonoidHom : Set G) ≤
      ((ChapterC.blockU L).map L.subtype).map (MulAut.conj (d⁻¹)⁻¹).toMonoidHom ⊔
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    simpa only [inv_inv, ← chosen_eq_blockU D hb.short, blockLocalCore,
      omegaResidualCore, blockLocalResidual, omegaLocalResidual] using hcover
  have hf := g2Two_local_core_factorization_of_moved_cover h D hne hb
    ((normalizer (T : Set G)).inv_mem hd) hcover'
  simpa only [inv_inv, ← chosen_eq_blockU D hb.short] using hf

/-- The source odd moving conjugator satisfies the centralizer cover and
core factorization, retaining both original centralizer clauses and the
source inverse-conjugation convention. -/
theorem exists_odd_moving_chosen_core_factorization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    IsElementaryAbelian 2 C ∧
      ∃ A : Subgroup G, A ≤ normalizer (T : Set G) ∧ Odd (Nat.card A) ∧
        ∃ d ∈ A, d ∉ normalizer (L : Set G) ∧
          ¬ V.map (MulAut.conj d⁻¹).toMonoidHom ≤ Q ∧
          C ⊓ C.map (MulAut.conj d⁻¹).toMonoidHom = ⊥ ∧
          C.map (MulAut.conj d⁻¹).toMonoidHom ≤ Q ∧
          omegaResidualCore T L ⊓ centralizer
            (V.map (MulAut.conj d⁻¹).toMonoidHom : Set G) ≤
              V.map (MulAut.conj d⁻¹).toMonoidHom ⊔ Q ∧
          Q = V ⊔ (Q ⊓ centralizer (V.map (MulAut.conj d⁻¹).toMonoidHom : Set G)) := by
  obtain ⟨b, ψ, hψ, _⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  obtain ⟨hC, A, hAN, ho, d, hd, hout, hmove, hdis, hCQ, _, _⟩ :=
    exists_odd_moving_full_actor_offender_image h D structural e hne hescape b ψ hψ
  have hdN := (normalizer (T : Set G)).inv_mem (hAN hd)
  exact ⟨hC, A, hAN, ho, d, hd, hout, hmove, hdis, hCQ,
    moved_chosen_centralizer_cover h D structural e hne hescape hdN hmove,
    core_eq_chosen_sup_moved_centralizer h D structural e hne hescape hdN hmove⟩

/-- The actual moving module supplies every geometric input for the
whole-core product and elementarity conclusion. -/
theorem core_product_and_elementary_of_moved_chosen
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
      IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⊥ :=
  core_product_and_elementary_of_moved_chosen_cover h D structural e hne hescape hd hmove
    (moved_chosen_centralizer_cover h D structural e hne hescape hd hmove)

/-- Source escape alone supplies the moving conjugator and hence the
original core product, elementarity and trivial Frattini subgroup. -/
theorem core_product_and_elementary_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
      IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⊥ := by
  obtain ⟨_, A, hAN, _, d, hd, _, hmove, _, _, _, _⟩ :=
    exists_odd_moving_chosen_core_factorization h D structural e hne hescape
  exact core_product_and_elementary_of_moved_chosen h D structural e hne hescape
    ((normalizer (T : Set G)).inv_mem (hAN hd)) hmove

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
