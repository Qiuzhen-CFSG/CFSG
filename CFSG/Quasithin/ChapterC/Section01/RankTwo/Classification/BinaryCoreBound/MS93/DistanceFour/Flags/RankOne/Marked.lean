module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.EdgeRadius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Residual
public import Theory.GroupTheory.SylowKernelCore

/-!
# The marked parabolic actors for the distance-four flag argument

Both parabolics use the supplied projection and flag. Their two-cores and
source-ordered residuals are embedded through the original amalgam map.
Faithful-image transport identifies these with the intrinsic cores and
residuals of the image parabolics. Their relative normalization and residual
generation reduce core containment to two local commutator bounds.
When the parabolic core is the actual edge kernel, its normalizer acts on
V_beta through the characteristic pullback to R. The constructed action has
the literal ambient conjugation formula.

`FlagControl` records exactly the additional flag output still required:
selection of T_beta as a marked parabolic core, and the triple commutator
[U_delta1, Ltilde_delta1, V_alpha] in Z(G_alpha), with U_delta1 = V_beta.
Its existence is not asserted here. The two residual operations retain
source order; normalization is relative to the corresponding parabolic.

Source: Meierfrankenfeld--Stellmacher (1993), notation on pp.832 and 859,
and (4.6.8), printed pp.905--908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The image of one of the two parabolics under the original amalgam embedding. -/
def flagParabolic (source : LocalSource L R) (i : Bool) : Subgroup (FreeAmalgam R) :=
  (parabolic source.projection source.flag i).map (embedM R)

/-- The intrinsic parabolic two-core, with both subgroup inclusions retained. -/
def flagKernel (source : LocalSource L R) (i : Bool) : Subgroup (FreeAmalgam R) :=
  ((pCore 2 (parabolic source.projection source.flag i)).map
    (parabolic source.projection source.flag i).subtype).map (embedM R)

/-- The source O²(O^{2′}(P)) actor, through the same amalgam embedding. -/
def flagResidual (source : LocalSource L R) (i : Bool) : Subgroup (FreeAmalgam R) :=
  (rankOne (parabolic source.projection source.flag i)).map (embedM R)

/-- The marked parabolic is a subgroup of the actual M-vertex stabilizer. -/
theorem flagParabolic_le (source : LocalSource L R) (i : Bool) :
    flagParabolic source i ≤ stabilizer R (alpha R) := by
  rw [alpha, stabilizer_m_base]
  exact map_le_range (embedM R) (parabolic source.projection source.flag i)

/-- The embedded two-core lies in its own parabolic. -/
theorem flagKernel_le (source : LocalSource L R) (i : Bool) :
    flagKernel source i ≤ flagParabolic source i :=
  map_mono (map_subtype_le _)

/-- The source-ordered residual lies in its own parabolic. -/
theorem flagResidual_le (source : LocalSource L R) (i : Bool) :
    flagResidual source i ≤ flagParabolic source i :=
  map_mono (map_subtype_le _)

/-- Faithfulness identifies the two-core with that of the actual image parabolic. -/
theorem flagKernel_eq (source : LocalSource L R) (i : Bool) :
    flagKernel source i =
      (pCore 2 (flagParabolic source i)).map (flagParabolic source i).subtype := by
  exact map_pCoreIn_of_injective 2 (parabolic source.projection source.flag i)
    (embedM R) (embedM_injective R)

/-- In the binary extension the source-ordered actor is the image parabolic two-residual. -/
theorem flagResidual_eq [Finite M] (source : LocalSource L R) (i : Bool) :
    flagResidual source i =
      (pResidual 2 (flagParabolic source i)).map (flagParabolic source i).subtype := by
  rw [flagResidual, rankOne_parabolic_eq source.projection source.projection_surjective
    (by rw [source.projection_kernel]; exact pCore_isPGroup)]
  exact map_embedded_pResidual 2 (parabolic source.projection source.flag i) (embedM R)

/-- The two marked residuals generate the actual local component. -/
theorem flagResidual_sup [Finite M] (source : LocalSource L R) :
    flagResidual source false ⊔ flagResidual source true = Ltilde R (alpha R) := by
  rw [flagResidual, flagResidual, ← Subgroup.map_sup, source.rank_one_generation,
    Ltilde_alpha, source.residual]

/-- Parabolic two-core normality is relative to its own marked parabolic. -/
theorem flagKernel_normalized (source : LocalSource L R) (i : Bool) :
    flagParabolic source i ≤ normalizer (flagKernel source i : Set (FreeAmalgam R)) := by
  rw [flagKernel_eq]
  exact (flagParabolic source i).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ _)

/-- The source residual is normalized by its own marked parabolic. -/
theorem flagResidual_normalized [Finite M] (source : LocalSource L R) (i : Bool) :
    flagParabolic source i ≤ normalizer (flagResidual source i : Set (FreeAmalgam R)) := by
  rw [flagResidual_eq]
  exact (flagParabolic source i).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ _)

/-- Identifying the parabolic core with T_beta gives the actual parabolic action on V_beta. -/
theorem flagParabolic_normalizes_edgeRadius [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    flagParabolic source i ≤ normalizer (V R (beta R) : Set (FreeAmalgam R)) := by
  have hk : (pCore 2 (parabolic source.projection source.flag i)).map
      (parabolic source.projection source.flag i).subtype = R := by
    apply Subgroup.map_injective (f := embedM R) (embedM_injective R)
    exact hkernel.trans (Q_beta R)
  have hn : parabolic source.projection source.flag i ≤ normalizer (R : Set M) := by
    conv_rhs => rw [← hk]
    exact (parabolic source.projection source.flag i).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _)
  exact (map_mono hn).trans (edgeRadius_normalized_by_edgeNormalizer geometry hlarge)

/-- The source rank-one residual acts on U_delta1 = V_beta by normalization. -/
theorem flagResidual_normalizes_edgeRadius [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    flagResidual source i ≤ normalizer (V R (beta R) : Set (FreeAmalgam R)) :=
  (flagResidual_le source i).trans
    (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel)

/-- The actual parabolic action, constructed through the normalizer of the edge-radius layer. -/
noncomputable def edgeRadiusAction [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    flagParabolic source i →* MulAut (V R (beta R)) :=
  (V R (beta R)).normalizerMonoidHom.comp
    (inclusion (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel))

/-- The constructed action is ambient conjugation by the original parabolic element. -/
theorem edgeRadiusAction_apply [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : flagParabolic source i) (x : V R (beta R)) :
    (edgeRadiusAction source geometry hlarge i hkernel p x : FreeAmalgam R) =
      (p : FreeAmalgam R) * (x : FreeAmalgam R) * (p : FreeAmalgam R)⁻¹ := rfl

/-- The first rank-one commutator stays in the genuine elementary edge layer. -/
theorem flag_commutator_le_edgeRadius [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    ⁅V R (beta R), flagResidual source i⁆ ≤ V R (beta R) :=
  le_normalizer_iff_commutator_le_left.mp
    (flagResidual_normalizes_edgeRadius source geometry hlarge i hkernel)

/-- Transport the literal left-normed rank-one triple commutator by the graph action. -/
theorem flag_triple_act (source : LocalSource L R) (i : Bool)
    (htriple : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (g : FreeAmalgam R) :
    ⁅⁅V R (act R g (beta R)),
      (flagResidual source i).map (MulAut.conj g⁻¹).toMonoidHom⁆,
      V R (act R g (alpha R))⁆ ≤
        (center (stabilizer R (act R g (alpha R)))).map
          (stabilizer R (act R g (alpha R))).subtype := by
  rw [V_act, V_act, ← map_commutator, ← map_commutator, stabilizer_act,
    ← centerImage_map]
  exact map_mono htriple

/-- Bounds for both rank-one actors give containment of the whole commutator core. -/
theorem core_le_radius_of_flag_commutators [Finite M] (source : LocalSource L R)
    (h : ∀ i, ⁅Q R (alpha R), flagResidual source i⁆ ≤ V R (alpha R)) :
    core R (alpha R) ≤ V R (alpha R) := by
  have hpre : Ltilde R (alpha R) ≤
      commutatorPreimage (stabilizer R (alpha R)) (Q R (alpha R)) (V R (alpha R)) := by
    rw [← flagResidual_sup source]
    apply sup_le
    · exact le_commutatorPreimage ((flagResidual_le source false).trans
        (flagParabolic_le source false)) (by rw [commutator_comm]; exact h false)
    · exact le_commutatorPreimage ((flagResidual_le source true).trans
        (flagParabolic_le source true)) (by rw [commutator_comm]; exact h true)
  rw [core, commutator_comm]
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (DistanceEight.V_normalized R _))

/-- The source flag selection and (4.6.8) output, still to be constructed. -/
def FlagControl (source : LocalSource L R) : Prop :=
  ∃ i, flagKernel source i = Q R (beta R) ∧
    ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
