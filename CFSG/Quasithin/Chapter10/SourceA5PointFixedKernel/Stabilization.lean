module
public import CFSG.Quasithin.Chapter10.SourceA5CoveringUniqueness
public import CFSG.Quasithin.Chapter10.SourceElementCentralizerComponent
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
/-!
# Sylow stabilization for all original A₅ point centralizers

Let v be a nonidentity vector of the original Sylow subgroup centralizing L.
If its centralizer escapes M, then C_T(v) normalizes L even when L₀ fixes v.
Otherwise an element of C_T(v) exchanges the original two components, and
J=L₀C_T(v) covers L₀ and normally generates it from L. The nonidentity central
vector gives O₂(J)≠1, so the completed covering-uniqueness theorem puts the
whole centralizer back in M. This contradiction supplies the missing
stabilization without requiring the fixed kernel to vanish.

The literal containing-component construction then works for every such
point. This is an alternative to the initial fixed-vector exclusion in
Aschbacher–Smith 10.2.9(1), printed p.750, using 4.2.12–13 and specialized C.4.8.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Every escaping original point centralizer has its Sylow intersection
inside the component stabilizer, including points fixed by L₀. -/
theorem source_a5_escaping_element_sylow_stabilizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hout : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal) :
    (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  by_cases hv0 : v ∈ centralizer (localOrbit T L : Set G)
  swap
  · exact (inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
      (source_nonnormal_element_centralizer_stabilizes D hn hvL hv0)
  by_contra hnot
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hnot
  let R := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let J := localOrbit T L ⊔ R
  have hJM : J ≤ D.maximalLocal := sup_le (localOrbit T L).le_normalizer
    (inf_le_left.trans (le_normalizer_componentOrbit L T))
  have hJC : J ≤ centralizer ({v} : Set G) := sup_le
    (fun l hl => mem_centralizer_singleton_iff.mpr (hv0 l hl)) inf_le_right
  have hvC : v ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hvJ : v ∈ J := mem_sup_right ⟨hvT,hvC⟩
  have hp : IsPGroup 2 (zpowers v) := T.isPGroup'.to_le (zpowers_le.mpr hvT)
  have hzn : J ≤ normalizer (zpowers v : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rwa [zpowers_eq_closure,centralizer_closure]
  have hcore : J.pCoreIn 2 ≠ ⊥ := by
    have hz := le_pCoreIn_of_normalizes hp (zpowers_le.mpr hvJ) hzn
    intro he
    exact hv1 (mem_bot.mp (he ▸ hz (mem_zpowers v)))
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht.1 htn
  have hgen : componentOrbit L J = localOrbit T L := by
    apply le_antisymm
    · exact iSup_conjugates_le_of_le_normalizer L J (localOrbit T L)
        (le_componentOrbit L T) hJM
    · rw [hpair]
      exact sup_le (le_componentOrbit L J)
        (le_iSup (fun s : J => L.map (MulAut.conj (s : G)).toMonoidHom)
          ⟨t,mem_sup_right ht⟩)
  have hcover : (localOrbit T L : Set G) ⊆
      (J : Set G) * ((localOrbit T L).pCoreIn 2 : Set G) := by
    intro x hx
    exact Set.mem_mul.mpr ⟨x,mem_sup_left hx,1,one_mem _,mul_one x⟩
  have hu := source_a5_covering_uniqueness D e hn hJM hcover hcore hgen
  have hzne : zpowers v ≠ ⊥ := by
    intro he
    exact hv1 (mem_bot.mp (he ▸ mem_zpowers v))
  apply hout
  have hc : centralizer ({v} : Set G) = centralizer (zpowers v : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
  rw [hc]
  exact (Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_of_unique_maximalTwoLocal hu.2.2 hp hzne hzn)
/-- The actual enlarged normal component for any nonidentity source point,
with the former noncentralization assumption discharged by covering uniqueness. -/
theorem source_a5_escaping_element_component_all_points
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hescape : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal) :
    ∃ I : Subgroup G, L < I ∧ I ≤ centralizer ({v} : Set G) ∧
      (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent ∧
      centralizer ({v} : Set G) ≤ normalizer (I : Set G) ∧
      ¬ I ≤ D.maximalLocal ∧ componentOrbit L I = I := by
  have hstab := source_a5_escaping_element_sylow_stabilizes D e hn hvT hv1 hvL hescape
  obtain ⟨I,hLI,hIX,hI,hIn⟩ :=
    source_element_containing_component_of_sylow D hvT hv1 hvL hs hstab
  obtain ⟨hlt,hout⟩ := source_element_containing_component_escape D hNL hescape hLI hIX hI hIn
  exact ⟨I,hlt,hIX,hI,hIn,hout,source_containing_component_normal_generation D hLI hIX hI⟩

end CFSG.Quasithin.Chapter10
