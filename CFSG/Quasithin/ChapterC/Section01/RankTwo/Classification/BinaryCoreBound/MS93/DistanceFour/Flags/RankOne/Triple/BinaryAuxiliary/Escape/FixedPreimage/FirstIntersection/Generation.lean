module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Locality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Algebra
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore

/-!
# Normal generation by the intersection of incident cores

The shared transvection in the two standard parabolic cores, together with
its conjugate by the line reflection, generates the line four-group core.
The diagram automorphism gives the point case, and the supplied flag marking
gives every marked pair. Lifting through the original source projection
retains its entire kernel in the intersection. A common representative of
two incident parabolic cosets transports this generation into the amalgam.

The exported normal closure is taken inside the full opposite parabolic.
No ambient normality in the free amalgam is required.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the binary auxiliary calculation in (4.6.8), printed pp.907--908.
-/

public section
open Subgroup Matrix Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.FirstIntersection

private theorem generation_map {G H : Type*} [Group G] [Group H]
    (P K A : Subgroup G)
    (hgen : ∀ N : Subgroup G, P ≤ normalizer N → K ⊓ A ≤ N → K ≤ N)
    (f : G →* H) (N : Subgroup H)
    (hn : P.map f ≤ normalizer N) (hx : K.map f ⊓ A.map f ≤ N) :
    K.map f ≤ N := by
  apply map_le_iff_le_comap.mpr
  apply hgen
  · apply le_normalizer_iff.mpr
    intro p hp x hx
    change f (p * x * p⁻¹) ∈ N
    simpa only [map_mul, map_inv] using
      le_normalizer_iff.mp hn (f p) (mem_map_of_mem f hp) (f x) hx
  · exact map_le_iff_le_comap.mp ((map_inf_le K A f).trans hx)

private theorem generation_comap {G H : Type*} [Group G] [Group H]
    (P K A : Subgroup H)
    (hgen : ∀ N : Subgroup H, P ≤ normalizer N → K ⊓ A ≤ N → K ≤ N)
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G)
    (hn : P.comap f ≤ normalizer N) (hx : K.comap f ⊓ A.comap f ≤ N) :
    K.comap f ≤ N := by
  have hk : f.ker ≤ N := by
    intro x hxker
    apply hx
    change f x ∈ K ∧ f x ∈ A
    rw [show f x = 1 from hxker]
    exact ⟨K.one_mem, A.one_mem⟩
  have hm : K ≤ N.map f := by
    apply hgen
    · have h := (map_mono (f := f) hn).trans (N.le_normalizer_map f)
      rwa [map_comap_eq_self_of_surjective hf] at h
    · have h := map_mono (f := f) hx
      rwa [← comap_inf, map_comap_eq_self_of_surjective hf] at h
  have h := comap_mono (f := f) hm
  rwa [comap_map_eq_self hk] at h

private theorem line_map_diagram : lineParabolicSL.map diagram.toMonoidHom =
    pointParabolicSL := by
  apply Subgroup.map_injective (f := diagram.toMonoidHom) diagram.injective
  rw [pointParabolic_map_diagram, Subgroup.map_map]
  have he : diagram.toMonoidHom.comp diagram.toMonoidHom = MonoidHom.id SL := by
    apply MonoidHom.ext
    intro x
    exact diagram_involutive x
  rw [he, Subgroup.map_id]

private def u (v : ZMod 2 × ZMod 2) : Matrix.PSL3Two.SL :=
  BinaryLinearThree.shear (Multiplicative.ofAdd v)
private def s : Matrix.PSL3Two.SL := ⟨!![0,1,0;1,0,0;0,0,1], by decide⟩

private theorem line_generation (N : Subgroup SL)
    (hn : lineParabolicSL ≤ normalizer N)
    (hx : lineParabolicSL.pCoreIn 2 ⊓ pointParabolicSL.pCoreIn 2 ≤ N) :
    lineParabolicSL.pCoreIn 2 ≤ N := by
  have hu : u (1,0) ∈ lineParabolicSL.pCoreIn 2 := by
    rw [lineParabolicSL_pCoreIn_two_eq_R]
    exact ⟨Multiplicative.ofAdd (1,0), rfl⟩
  have hu' : u (1,0) ∈ pointParabolicSL.pCoreIn 2 := by
    rw [← line_map_diagram, ← map_pCoreIn_of_injective 2 _ _ diagram.injective]
    exact ⟨u (1,0), hu, by decide +kernel⟩
  have h1 : u (1,0) ∈ N := hx ⟨hu,hu'⟩
  have hs : s ∈ lineParabolicSL := by decide +kernel
  have h2 : u (0,1) ∈ N := by
    have he : s * u (1,0) * s⁻¹ = u (0,1) := by decide +kernel
    rw [← he]
    exact le_normalizer_iff.mp hn s hs _ h1
  have words : ∀ v : ZMod 2 × ZMod 2,
      u v = u (1,0) ^ v.1.val * u (0,1) ^ v.2.val := by decide +kernel
  rw [lineParabolicSL_pCoreIn_two_eq_R]
  rintro x ⟨v,rfl⟩
  change u v.toAdd ∈ N
  rw [words]
  exact N.mul_mem (N.pow_mem h1 _) (N.pow_mem h2 _)

private theorem point_generation (N : Subgroup SL)
    (hn : pointParabolicSL ≤ normalizer N)
    (hx : pointParabolicSL.pCoreIn 2 ⊓ lineParabolicSL.pCoreIn 2 ≤ N) :
    pointParabolicSL.pCoreIn 2 ≤ N := by
  have h := generation_map lineParabolicSL (lineParabolicSL.pCoreIn 2)
    (pointParabolicSL.pCoreIn 2) line_generation diagram.toMonoidHom
  rw [map_pCoreIn_of_injective 2 lineParabolicSL diagram.toMonoidHom diagram.injective,
    map_pCoreIn_of_injective 2 pointParabolicSL diagram.toMonoidHom diagram.injective,
    line_map_diagram, pointParabolic_map_diagram] at h
  exact h N hn hx

private theorem model_generation (t : SL) (i : Bool) (N : Subgroup SL)
    (hn : modelParabolic t i ≤ normalizer N)
    (hx : (modelParabolic t i).pCoreIn 2 ⊓ (modelParabolic t (!i)).pCoreIn 2 ≤ N) :
    (modelParabolic t i).pCoreIn 2 ≤ N := by
  cases i
  · have h := generation_map pointParabolicSL (pointParabolicSL.pCoreIn 2)
      (lineParabolicSL.pCoreIn 2) point_generation (MulAut.conj t).toMonoidHom
    simp only [map_pCoreIn_of_injective 2 pointParabolicSL (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective,
      map_pCoreIn_of_injective 2 lineParabolicSL (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective] at h
    exact h N hn hx
  · have h := generation_map lineParabolicSL (lineParabolicSL.pCoreIn 2)
      (pointParabolicSL.pCoreIn 2) line_generation (MulAut.conj t).toMonoidHom
    simp only [map_pCoreIn_of_injective 2 pointParabolicSL (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective,
      map_pCoreIn_of_injective 2 lineParabolicSL (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective] at h
    exact h N hn hx

open Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem flag_generation (source : LocalSource L R) (i : Bool)
    (N : Subgroup (FreeAmalgam R))
    (hn : flagParabolic source i ≤ normalizer N)
    (hx : flagKernel source i ⊓ flagKernel source (!i) ≤ N) :
    flagKernel source i ≤ N := by
  have hgen (S : Subgroup M)
      (hS : parabolic source.projection source.flag i ≤ normalizer S)
      (hx : (parabolic source.projection source.flag i).pCoreIn 2 ⊓
        (parabolic source.projection source.flag (!i)).pCoreIn 2 ≤ S) :
      (parabolic source.projection source.flag i).pCoreIn 2 ≤ S := by
    rw [Incident.parabolic_core_eq_comap source i,
      Incident.parabolic_core_eq_comap source (!i)] at hx
    rw [Incident.parabolic_core_eq_comap source i]
    exact generation_comap _ _ _ (model_generation source.flag i)
      source.projection source.projection_surjective S hS hx
  exact generation_map _ _ _ hgen (embedM R) N hn hx

/-- Normalized subgroups containing the incident core intersection contain the
whole opposite core. The intersection retains the original projection kernel. -/
theorem incident_core_le_of_intersection (source : LocalSource L R) (i : Bool)
    (d : M) (hd : flagIncident source i 1 d) (N : Subgroup (FreeAmalgam R))
    (hn : localFlagActor source (!i) d ≤ normalizer N)
    (hx : localFlagKernel source (!i) d ⊓ flagKernel source i ≤ N) :
    localFlagKernel source (!i) d ≤ N := by
  obtain ⟨m, hm, hdm⟩ := (flagIncident_one_iff source i d).mp hd
  have hP : localFlagActor source (!i) m = localFlagActor source (!i) d := by
    simpa only [mul_inv_cancel_left] using
      localFlagActor_right_mul source (!i) d (d⁻¹ * m) hdm
  have hK : localFlagKernel source (!i) m = localFlagKernel source (!i) d := by
    simpa only [mul_inv_cancel_left] using
      localFlagKernel_right_mul source (!i) d (d⁻¹ * m) hdm
  have hA : localConjugate (flagKernel source i) m = flagKernel source i :=
    mem_normalizer_iff_map_conj_eq.mp
      (flagKernel_normalized source i (mem_map_of_mem (embedM R) hm))
  have h := generation_map _ _ _ (flag_generation source (!i))
    (MulAut.conj (embedM R m)).toMonoidHom N
  simp only [Bool.not_not] at h
  change localFlagActor source (!i) m ≤ normalizer N →
    localFlagKernel source (!i) m ⊓ localConjugate (flagKernel source i) m ≤ N →
    localFlagKernel source (!i) m ≤ N at h
  rw [hP, hK, hA] at h
  exact h hn hx

/-- The incident opposite core is the relative normal closure of its
intersection with the first core inside its own full parabolic. -/
theorem incident_core_normalClosure (source : LocalSource L R) (i : Bool)
    (d : M) (hd : flagIncident source i 1 d) :
    RankOnePairing.localGenerated (localFlagActor source (!i) d)
      (localFlagKernel source (!i) d ⊓ flagKernel source i) =
        localFlagKernel source (!i) d := by
  have hPK : localFlagActor source (!i) d ≤ normalizer (localFlagKernel source (!i) d) :=
    (map_mono (f := (MulAut.conj (embedM R d)).toMonoidHom)
      (flagKernel_normalized source (!i))).trans
        ((flagKernel source (!i)).le_normalizer_map _)
  apply le_antisymm
  · exact RankOnePairing.Incidence.localGenerated_le_of_normalizes _ _ _ hPK inf_le_left
  · apply incident_core_le_of_intersection source i d hd
    · exact RankOnePairing.Incidence.localGenerated_normalized _ _
    · exact RankOnePairing.le_localGenerated _ _
        (inf_le_left.trans (map_mono (flagKernel_le source (!i))))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.FirstIntersection
