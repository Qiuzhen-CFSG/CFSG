module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Escape
public import Theory.GroupTheory.CComponent.OrbitCorrespondence
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Transporting the recognized component orbit

A C-component of the centralizer remains a C-component in its join with T.
The p-group conjugacy theorem inside that join shows that every C-component
has the same T-orbit. Mapping back to G retains the original embeddings.
The seed already lies in M, so an escaping orbit also makes X<K_z strict.

Source: Aschbacher--Smith 10.3.3 and the paragraph following it, printed
p.756; the conjugacy step uses the genuine C-component correspondence A.3.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem orbit_eq_of_conjugate (I K S : Subgroup G) (s : S)
    (he : K = I.map (MulAut.conj (s : G)).toMonoidHom) :
    componentOrbit K S = componentOrbit I S := by
  have hKI : K ≤ componentOrbit I S := by
    rw [he]
    exact le_iSup (fun t : S => I.map (MulAut.conj (t : G)).toMonoidHom) s
  have hIK : I ≤ componentOrbit K S := by
    intro i hi
    have hm : (MulAut.conj (s : G)) i ∈ componentOrbit K S := by
      apply le_componentOrbit K S
      rw [he]
      exact mem_map_of_mem _ hi
    exact (mem_normalizer_iff.mp (le_normalizer_componentOrbit K S s.property) i).mpr hm
  exact le_antisymm
    (iSup_conjugates_le_of_le_normalizer K S _ hKI (le_normalizer_componentOrbit I S))
    (iSup_conjugates_le_of_le_normalizer I S _ hIK (le_normalizer_componentOrbit K S))

private theorem component_orbits_eq_of_pGroup_join {p : ℕ} [Fact p.Prime]
    {I K C S : Subgroup G} (hI : I ∈ Chapter1.cComponentsIn C)
    (hK : K ∈ Chapter1.cComponentsIn (I ⊔ S)) (hJC : I ⊔ S ≤ C)
    (hS : IsPGroup p S) : componentOrbit K S = componentOrbit I S := by
  let J := I ⊔ S
  have hIJ : I ≤ J := le_sup_left
  have hSJ : S ≤ J := le_sup_right
  have hKJ : K ≤ J := hK.1
  have hcomp := hI.2.subgroupOf_of_le hIJ hJC
  have hgen : I.subgroupOf J ⊔ S.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup hIJ hSJ]
    exact subgroupOf_self _
  obtain ⟨s, hs⟩ := hcomp.conjugate_of_pGroup_generated hK.2
    (hS.comap_subtype (K := J)) hgen
  have horbit := orbit_eq_of_conjugate (I.subgroupOf J) (K.subgroupOf J)
    (S.subgroupOf J) s hs
  have hm := congrArg (fun U : Subgroup J => U.map J.subtype) horbit
  simpa only [map_componentOrbit, map_subgroupOf_eq_of_le hIJ,
    map_subgroupOf_eq_of_le hSJ, map_subgroupOf_eq_of_le hKJ] using hm

open Chapter3.Section02
variable {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- Recognition of one actual escaping orbit identifies every component orbit. -/
theorem CentralizerData.all_component_orbits (d : CentralizerData T D s)
    {I : Subgroup G}
    (hI : I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)))
    (horbit : componentOrbit I (T : Subgroup G) = componentSpan T L (d.first * d.second)) :
    ∀ K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)),
      componentOrbit K (T : Subgroup G) = componentSpan T L (d.first * d.second) := by
  intro K hK
  have he : componentJoin T L (d.first * d.second) = I ⊔ (T : Subgroup G) := by
    rw [componentJoin, ← horbit, componentOrbit_sup]
  have hJC : I ⊔ (T : Subgroup G) ≤ centralizer ({d.first * d.second} : Set G) :=
    he ▸ d.join_le_centralizer
  rw [he] at hK
  exact (component_orbits_eq_of_pGroup_join hI hK hJC T.isPGroup').trans horbit

/-- The two-residual seed is contained in the original maximal local subgroup. -/
theorem centralizerSeed_le_maximalLocal (z : G) :
    centralizerSeed T L z ≤ D.maximalLocal :=
  (map_subtype_le _).trans (inf_le_left.trans (localOrbit T L).le_normalizer)

/-- Escape of the recognized component forces both remaining order clauses. -/
theorem CentralizerData.strict_and_escape_of_orbit (d : CentralizerData T D s)
    {I : Subgroup G} (hout : ¬ I ≤ D.maximalLocal)
    (horbit : componentOrbit I (T : Subgroup G) = componentSpan T L (d.first * d.second)) :
    centralizerSeed T L (d.first * d.second) < componentSpan T L (d.first * d.second) ∧
      ¬ componentSpan T L (d.first * d.second) ≤ D.maximalLocal := by
  have hescape : ¬ componentSpan T L (d.first * d.second) ≤ D.maximalLocal := by
    intro hm
    exact hout ((le_componentOrbit I (T : Subgroup G)).trans (horbit.symm ▸ hm))
  refine ⟨lt_of_le_of_ne (le_conjugateSpanBy _ _) ?_, hescape⟩
  intro he
  exact hescape (he ▸ centralizerSeed_le_maximalLocal (D := D) _)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
