module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.MovedGeneration
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.NormalizerResidual
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2SharpFixedIndex
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The original G₂ whole-core index and product

The actual moving Weyl offender has fixed codimension three, hence
[V:C_V(Vᵈ)]=8. The moved-centralizer cover and the sharp intrinsic
factorization give Q=V C_Q(Vᵈ), so the same index holds on all of Q.
The verified two-conjugate generation theorem then yields Q=V C_T(L)
and makes Q elementary abelian. The cover remains the sole geometric
input of this source continuation.

Source: Aschbacher--Smith 3.3.28, printed p.601.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource Atlas.G2.Natural
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2
local notation "W" => TraceZero F
local notation "σ" => traceZeroAction F

/-- The actual noncentral moving module has centralizer index eight on V. -/
theorem moved_chosen_fixed_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (centralizer (V.map (MulAut.conj d).toMonoidHom : Set G)).relIndex V = 8 := by
  obtain ⟨b, ψ, hψ, _⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  obtain ⟨_, _, _, _, hMV, _, _⟩ := exists_fixed_involution_setup h D structural e hne
  let B := V.map (MulAut.conj d).toMonoidHom
  have hBT : B ≤ (T : Subgroup G) :=
    (map_mono D.le_sylow).trans (mem_normalizer_iff_map_conj_eq.mp hd).le
  have hBN : B ≤ normalizer (L : Set G) := hBT.trans D.sylow_normalizes_component
  let φ := ψ.comp (inclusion hBN)
  have he (a : B) (v : V) :
      (b (V.normalizerMonoidHom ⟨a.val, hMV.le (hBN a.property)⟩ v)).toAdd =
        σ (ψ (inclusion hBN a)) (b v).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    change (b.symm (b (V.normalizerMonoidHom
      ⟨a.val, hMV.le (hBN a.property)⟩ v)) : G) = _
    rw [b.symm_apply_apply, hψ]
    change _ = (a : G) * (b.symm (b v) : G) * (a : G)⁻¹
    rw [b.symm_apply_apply]
    rfl
  have hoff : IsOffender σ φ.range := by
    rw [show φ = ψ.comp (inclusion hBN) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range]
    exact (moved_full_actor_offender_image h D structural e hne b ψ hψ hd hmove).1
  rw [BinaryConjugationCoordinates.model_fixed_index B V (hBN.trans hMV.le) σ φ b he,
    OrthogonalCover.BinaryOffenders.offender_fixedCodim _ hoff]
  rfl

/-- The intrinsic sharp factorization applies to the actual chosen module
and the forward-conjugation convention of the point-geometry cover. -/
theorem core_factorization_of_moved_chosen_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hcover : omegaResidualCore T L ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) ≤
      V.map (MulAut.conj d).toMonoidHom ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = V ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G)) := by
  have hb := g2Two_block_of_weyl_model h D hescape e
  have hV := chosen_eq_blockU D hb.short
  have hc : blockLocalCore T L ⊓ centralizer
      (((ChapterC.blockU L).map L.subtype).map (MulAut.conj (d⁻¹)⁻¹).toMonoidHom : Set G) ≤
      ((ChapterC.blockU L).map L.subtype).map (MulAut.conj (d⁻¹)⁻¹).toMonoidHom ⊔
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    simpa only [inv_inv, ← hV, blockLocalCore, omegaResidualCore,
      blockLocalResidual, omegaLocalResidual] using hcover
  have hh := g2Two_local_core_factorization_of_moved_cover h D hne hb
    ((normalizer (T : Set G)).inv_mem hd) hc
  simpa only [inv_inv, ← hV] using hh

/-- The moved-cover factorization transfers the exact index eight from V
to the entire original Q, including its central kernel. -/
theorem whole_core_fixed_index_of_moved_chosen_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcover : omegaResidualCore T L ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) ≤
      V.map (MulAut.conj d).toMonoidHom ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (centralizer (V.map (MulAut.conj d).toMonoidHom : Set G)).relIndex
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) = 8 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C := centralizer (V.map (MulAut.conj d).toMonoidHom : Set G)
  have hprod : Q = V ⊔ (Q ⊓ C) :=
    core_factorization_of_moved_chosen_cover h D e hne hescape hd hcover
  have hQN : Q ≤ normalizer (V : Set G) :=
    ((chosen_sylow_centralizer_eq_core_at h D structural).symm.le.trans inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _)
  calc
    C.relIndex Q = (Q ⊓ C).relIndex Q := (inf_relIndex_left Q C).symm
    _ = (Q ⊓ C).relIndex (V ⊔ (Q ⊓ C)) := congrArg ((Q ⊓ C).relIndex) hprod
    _ = (Q ⊓ C).relIndex V := relIndex_sup_of_normalizes V (Q ⊓ C)
      (inf_le_left.trans hQN)
    _ = C.relIndex V := by
      rw [← inf_relIndex_left V (Q ⊓ C), ← inf_assoc,
        inf_eq_left.mpr D.le_core, inf_relIndex_left]
    _ = 8 := moved_chosen_fixed_index h D structural e hne hd hmove

/-- The literal source cover now gives the full product Q=V C_T(L),
elementarity of Q, and its trivial Frattini subgroup without any numerical,
offender, actor-marking, or generation callback. -/
theorem core_product_and_elementary_of_moved_chosen_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcover : omegaResidualCore T L ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) ≤
      V.map (MulAut.conj d).toMonoidHom ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
      IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⊥ := by
  have hi := (whole_core_fixed_index_of_moved_chosen_cover h D structural e hne
    hescape hd hmove hcover).le
  have hb := g2Two_block_of_weyl_model h D hescape e
  obtain ⟨g, hg, hgen⟩ := moved_chosen_two_conjugate_generation h D structural e hne hd hmove
  refine ⟨?_, g2Two_core_elementary_of_conjugate_index h D hne hescape hb _ g hg hgen hi⟩
  have hp := g2Two_core_product_of_conjugate_index h D hescape hb _ g hg hgen hi
  rwa [← chosen_eq_blockU D hb.short] at hp

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
