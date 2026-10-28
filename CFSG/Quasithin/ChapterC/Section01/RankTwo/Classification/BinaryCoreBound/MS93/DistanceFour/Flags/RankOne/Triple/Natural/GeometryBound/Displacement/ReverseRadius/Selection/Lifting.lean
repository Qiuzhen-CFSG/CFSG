module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage
public import Theory.GroupTheory.QuotientIntersection

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Selection.Model

/-!
# Lifting the reverse parabolic join

A subgroup filling the first core modulo the original projection kernel
has the same intersection image in any parabolic preimage. The second core
retains that kernel, so joining and taking the relative index commute with
the original quotient and the injective amalgam embedding.

Equality of two conjugated source parabolics identifies their intrinsic
cores. The conjugator then normalizes R and its characteristic edge layer.
This detects distinct parabolics from an actual escaping layer, without
identifying flags merely by their representatives.

The index calculation is conditional on the finite `ModelJoin` obligation.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (1), printed p.905.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.ReverseSelection


private theorem lift_join {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (A : Subgroup G)
    (K P C : Subgroup H)
    (hA : A ⊔ f.ker = K.comap f)
    (hindex : ((K ⊓ P) ⊔ C).relIndex P = 3) :
    ((A ⊓ P.comap f) ⊔ C.comap f).relIndex (P.comap f) = 3 := by
  have hmapA : A.map f = K := by
    have hh := congrArg (Subgroup.map f) hA
    rwa [Subgroup.map_sup, map_ker_self, sup_bot_eq,
      map_comap_eq_self_of_surjective hf] at hh
  have hkerC : f.ker ≤ C.comap f := MonoidHom.ker_le_comap _ _
  have hmap := relIndex_map_map f ((A ⊓ P.comap f) ⊔ C.comap f) (P.comap f)
  rw [sup_eq_left.mpr (hkerC.trans le_sup_right),
    sup_eq_left.mpr (MonoidHom.ker_le_comap _ _)] at hmap
  rw [← hmap, Subgroup.map_sup, map_inf_of_ker_le _ _ _ (MonoidHom.ker_le_comap _ _),
    hmapA, map_comap_eq_self_of_surjective hf, map_comap_eq_self_of_surjective hf]
  exact hindex

private theorem map_conj_comap {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A : Subgroup H) (g : G) :
    (A.comap f).map (MulAut.conj g).toMonoidHom =
      (A.map (MulAut.conj (f g)).toMonoidHom).comap f := by
  ext x
  simp only [mem_map_equiv, mem_comap]
  change f (g⁻¹ * x * g) ∈ A ↔ (f g)⁻¹ * f x * f g ∈ A
  simp only [map_mul, map_inv]

private theorem map_conj_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A : Subgroup G) (g : G) :
    (A.map f).map (MulAut.conj (f g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map f := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Lift the finite join through the original quotient and amalgam embedding.
The subgroup A need only fill the original core modulo Q_alpha. -/
theorem join_index_of_model (source : LocalSource L R) (i : Bool)
    (hmodel : ModelJoin source.flag i)
    (A : Subgroup (FreeAmalgam R)) (hA : A ⊔ Q R (alpha R) = flagKernel source i)
    (g : M) (hne : localFlagActor source i g ≠ flagParabolic source i) :
    ((A ⊓ localFlagActor source i g) ⊔ localFlagKernel source i g).relIndex
      (localFlagActor source i g) = 3 := by
  let P := modelParabolic source.flag i
  let P' := P.map (MulAut.conj (source.projection g)).toMonoidHom
  have hP' : localFlagActor source i g = (P'.comap source.projection).map (embedM R) := by
    change ((P.comap source.projection).map (embedM R)).map _ = _
    rw [map_conj_map, map_conj_comap]
  have hK' : localFlagKernel source i g = ((P'.pCoreIn 2).comap source.projection).map
      (embedM R) := by
    change (((parabolic source.projection source.flag i).pCoreIn 2).map (embedM R)).map _ = _
    rw [map_conj_map, Incident.parabolic_core_eq_comap, map_conj_comap,
      map_pCoreIn_of_injective _ _ _ (MulAut.conj (source.projection g)).injective]
  have hmodelne : P' ≠ P := by
    intro he
    apply hne
    rw [hP', he]
    rfl
  let A₀ := A.comap (embedM R)
  have hAm : A₀.map (embedM R) = A := by
    apply map_comap_eq_self
    exact (le_sup_left.trans hA.le).trans
      ((flagKernel_le source i).trans (map_le_range _ _))
  have hA₀ : A₀ ⊔ source.projection.ker = (P.pCoreIn 2).comap source.projection := by
    apply map_injective (embedM_injective R)
    rw [Subgroup.map_sup, hAm, source.projection_kernel,
      ← Q_alpha R source.two_group source.core_le, hA,
      ← Incident.parabolic_core_eq_comap]
    rfl
  have hi := lift_join source.projection source.projection_surjective A₀ (P.pCoreIn 2) P'
    (P'.pCoreIn 2) hA₀ (hmodel (source.projection g) hmodelne)
  rw [hP', hK', ← hAm, ← map_inf _ _ _ (embedM_injective R),
    ← Subgroup.map_sup, relIndex_map_map_of_injective _ _ (embedM_injective R)]
  exact hi

/-- Equal conjugate actors fix the edge layer, since equality of their
intrinsic cores makes the conjugator normalize the original R. -/
theorem firstLayer_eq_of_actor_eq (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (g : M)
    (he : localFlagActor source i g = flagParabolic source i) :
    firstFlagLayer (R := R) g = V R (beta R) := by
  have hcore : localFlagKernel source i g = flagKernel source i := by
    rw [localFlagKernel, localConjugate, flagKernel_eq]
    change ((flagParabolic source i).pCoreIn 2).map _ = (flagParabolic source i).pCoreIn 2
    rw [map_pCoreIn_of_injective _ _ _ (MulAut.conj (embedM R g)).injective]
    exact congrArg (fun P : Subgroup (FreeAmalgam R) => P.pCoreIn 2) he
  have hRg : R.map (MulAut.conj g).toMonoidHom = R := by
    apply map_injective (embedM_injective R)
    rw [← map_conj_map, ← Q_beta R]
    simpa only [localFlagKernel, localConjugate, hkernel] using hcore
  have hg : g ∈ normalizer (R : Set M) := mem_normalizer_iff_map_conj_eq.mpr hRg
  exact mem_normalizer_iff_map_conj_eq.mp
    (edgeRadius_normalized_by_edgeNormalizer geometry hlarge (mem_map_of_mem (embedM R) hg))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.ReverseSelection
