module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.FixedSpaces.Model
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage

/-!
# Lifting the incident binary pencil

The actual local cores are the full inverse images of their marked matrix
cores. Thus the three matrix neighbors lift through the original projection:
two distinct cores generate the full parabolic and intersect in Q_alpha.
Every incident core occurs in this pencil. No choice of a new quotient marking
or generation hypothesis is introduced.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.906.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

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

private theorem core_preimage (source : LocalSource L R) (i : Bool) (g : M) :
    localFlagKernel source i g =
      ((FixedSpaceModel.core source.flag i (source.projection g)).comap source.projection).map
        (embedM R) := by
  change (((parabolic source.projection source.flag i).pCoreIn 2).map (embedM R)).map
    (MulAut.conj (embedM R g)).toMonoidHom = _
  rw [map_conj_map, parabolic_core_eq_comap, map_conj_comap]
  rfl

/-- Three actual neighbors, with full-actor generation, kernel intersection,
and coverage of every incident core through the supplied quotient marking. -/
theorem exists_incident_core_pencil (source : LocalSource L R) (i : Bool) :
    ∃ d : Fin 3 → M,
      (∀ j, flagIncident source i 1 (d j)) ∧
      (∀ j k, j ≠ k → localFlagKernel source (!i) (d j) ⊔
        localFlagKernel source (!i) (d k) = flagParabolic source i) ∧
      (∀ j k, j ≠ k → localFlagKernel source (!i) (d j) ⊓
        localFlagKernel source (!i) (d k) = Q R (alpha R)) ∧
      (∀ a, flagIncident source i 1 a → ∃ j,
        localFlagKernel source (!i) a = localFlagKernel source (!i) (d j)) := by
  classical
  obtain ⟨a,ha,hjoin,hmeet,hcover⟩ := FixedSpaceModel.pencil source.flag i
  choose d hd using fun j => source.projection_surjective (a j)
  have hmem (j : Fin 3) : d j ∈ parabolic source.projection source.flag i := by
    change source.projection (d j) ∈ modelParabolic source.flag i
    rw [hd]
    exact ha j
  have hc (j : Fin 3) : localFlagKernel source (!i) (d j) =
      ((FixedSpaceModel.core source.flag (!i) (a j)).comap source.projection).map
        (embedM R) := by rw [core_preimage, hd]
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨d j, by simpa only [inv_one, one_mul] using hmem j,
      by simp only [inv_mul_cancel]; exact one_mem _⟩
  · intro j k hjk
    rw [hc, hc, ← Subgroup.map_sup, comap_sup_eq source.projection _ _ source.projection_surjective,
      hjoin j k hjk]
    rfl
  · intro j k hjk
    rw [hc, hc, ← map_inf _ _ _ (embedM_injective R), ← comap_inf,
      hmeet j k hjk, MonoidHom.comap_bot, source.projection_kernel]
    exact (Q_alpha R source.two_group source.core_le).symm
  · intro b hb
    obtain ⟨m,hm,hbm⟩ := (flagIncident_one_iff source i b).mp hb
    obtain ⟨j,hj⟩ := hcover (source.projection m) hm
    have hdm : (d j)⁻¹ * m ∈ parabolic source.projection source.flag (!i) := by
      change source.projection ((d j)⁻¹ * m) ∈ modelParabolic source.flag (!i)
      simpa only [map_mul, map_inv, hd] using hj
    have he (b : M) (h : b⁻¹ * m ∈ parabolic source.projection source.flag (!i)) :
        localFlagKernel source (!i) m = localFlagKernel source (!i) b := by
      simpa only [mul_inv_cancel_left] using
        localFlagKernel_right_mul source (!i) b (b⁻¹*m) h
    exact ⟨j, (he b hbm).symm.trans (he (d j) hdm)⟩

/-- Distinct fixed Z-layers at incident neighbors force generation of the
full first parabolic by their actual local cores. -/
theorem distinct_incident_cores_generate (source : LocalSource L R) (i : Bool)
    (d e : M) (hd : flagIncident source i 1 d) (he : flagIncident source i 1 e)
    (hne : localFlagZ source (!i) d ≠ localFlagZ source (!i) e) :
    localFlagKernel source (!i) d ⊔ localFlagKernel source (!i) e =
      flagParabolic source i := by
  obtain ⟨a,_,hjoin,_,hcover⟩ := exists_incident_core_pencil source i
  obtain ⟨j,hj⟩ := hcover d hd
  obtain ⟨k,hk⟩ := hcover e he
  have hjk : j ≠ k := by
    intro h
    apply hne
    unfold localFlagZ
    rw [hj, hk, h]
  rw [hj, hk, hjoin j k hjk]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident
