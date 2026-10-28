module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Reduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.ConjugatePairInternalLift
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOrdinary.Source

/-!
# The literal exchanged orbit in original 13.1.12(3)

The Sylow subgroup used here is T intersect C_G(u). The source component
orbit bound and the full centralizer Sylow conclusion make its orbit normal
in C_G(u). If this Sylow subgroup normalized K, the index-two alternative
would be impossible, so K would be normal in C_G(u). The component-normalizer
action would then be the whole irreducible local-centralizer action.

Consequently the reducible branch has a genuine exchanging element and a
two-factor orbit, fully moved by the canonical radical. These facts do not
yet place the radical inside the orbit or identify either component model.

Source: Aschbacher--Smith, 13.1.12(3), printed p.874.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 SourceNonquasisimple
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {p : ℕ} {u : G}

/-- The actual T_u-orbit is relatively normal in the involution centralizer. -/
theorem Escape.orbit_normal (e : Escape T L p u K)
    (hH : IsSQTK KnownSimple.IsKnownSimple (centralizer ({u} : Set G))) :
    ((componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))).subgroupOf
      (centralizer ({u} : Set G))).Normal := by
  let H := centralizer ({u} : Set G)
  obtain ⟨S,hS⟩ := e.full_sylow
  have hn := componentOrbit_normal_of_normal_or_index_two (K.subgroupOf H) S
    (component_normal_or_index_two_source hH e.component.2)
  have he : (componentOrbit (K.subgroupOf H) (S : Subgroup H)).map H.subtype =
      componentOrbit K ((T : Subgroup G) ⊓ H) := by
    rw [map_componentOrbit,map_subgroupOf_eq_of_le e.component.1,hS]
  have hd : ((componentOrbit (K.subgroupOf H) (S : Subgroup H)).map H.subtype).subgroupOf H =
      componentOrbit (K.subgroupOf H) (S : Subgroup H) :=
    comap_map_eq_self_of_injective H.subtype_injective _
  rw [← he,hd]
  exact hn

/-- Relative normality would identify the component-normalizer actor with M_u. -/
theorem Context.component_not_normal_of_reducible [Fact p.Prime]
    (h : Context T L p) (o : OrbitFacts T L p) (s : Selected T L u)
    (e : Escape T L p u K) (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    ¬ (K.subgroupOf (centralizer ({u} : Set G))).Normal := by
  intro hn
  have hHK := (normal_subgroupOf_iff_le_normalizer e.component.1).mp hn
  apply hr
  intro A hA
  apply h.selected_irreducible o s A
  intro g a ha
  exact hA ⟨g,g.property,hHK g.property.2⟩ a ha

/-- The full centralizer Sylow subgroup really moves K in the reducible branch. -/
theorem Context.component_moved_of_reducible [Fact p.Prime]
    (h : Context T L p) (o : OrbitFacts T L p) (s : Selected T L u)
    (e : Escape T L p u K)
    (hH : IsSQTK KnownSimple.IsKnownSimple (centralizer ({u} : Set G)))
    (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    ¬ ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ≤ normalizer (K : Set G) := by
  intro ht
  let H := centralizer ({u} : Set G)
  have hi := (component_normal_or_index_two_source hH e.component.2).resolve_left
    (h.component_not_normal_of_reducible o s e hr)
  obtain ⟨S,hS⟩ := e.full_sylow
  have hSN : (S : Subgroup H) ≤ normalizer (K.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq e.component.1]
    intro x hx
    exact ht (hS ▸ mem_map_of_mem H.subtype hx)
  have hd := index_dvd_of_le hSN
  rw [hi] at hd
  exact S.not_dvd_index hd

/-- There are exactly the two displayed component factors, exchanged by an
actual element of T_u. No normality of K itself is assumed. -/
theorem Context.exists_component_exchange [Fact p.Prime]
    (h : Context T L p) (o : OrbitFacts T L p) (s : Selected T L u)
    (e : Escape T L p u K)
    (hH : IsSQTK KnownSimple.IsKnownSimple (centralizer ({u} : Set G)))
    (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    ∃ t ∈ (T : Subgroup G) ⊓ centralizer ({u} : Set G),
      t ∉ normalizer (K : Set G) ∧ K.conjBy t ≠ K ∧
      componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) =
        K ⊔ K.conjBy t ∧
      ∀ g ∈ centralizer ({u} : Set G), K.conjBy g = K ∨ K.conjBy g = K.conjBy t := by
  let H := centralizer ({u} : Set G)
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp (h.component_moved_of_reducible o s e hH hr)
  have hi := (component_normal_or_index_two_source hH e.component.2).resolve_left
    (h.component_not_normal_of_reducible o s e hr)
  have htn' : (⟨t,ht.2⟩ : H) ∉ normalizer (K.subgroupOf H : Set H) := by
    intro hn
    rw [← subgroupOf_normalizer_eq (show K ≤ H from e.component.1)] at hn
    exact htn hn
  have hp : ∀ g ∈ H, K.conjBy g = K ∨ K.conjBy g = K.conjBy t := by
    intro g hg
    have hm : (K.subgroupOf H).conjBy (⟨t,ht.2⟩ : H) ≠ K.subgroupOf H :=
      fun he => htn' (mem_normalizer_iff_map_conj_eq.mpr he)
    have hh := NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm (⟨g,hg⟩ : H)
    rcases hh with hh | hh
    · left
      have hh' := congrArg (map H.subtype) hh
      change ((K.subgroupOf H).conjBy (⟨g,hg⟩ : H)).map H.subtype =
        (K.subgroupOf H).map H.subtype at hh'
      rw [map_conjBy_hom,map_subgroupOf_eq_of_le (show K ≤ H from e.component.1)] at hh'
      exact hh'
    · right
      have hh' := congrArg (map H.subtype) hh
      change ((K.subgroupOf H).conjBy (⟨g,hg⟩ : H)).map H.subtype =
        ((K.subgroupOf H).conjBy (⟨t,ht.2⟩ : H)).map H.subtype at hh'
      rw [map_conjBy_hom,map_conjBy_hom,
        map_subgroupOf_eq_of_le (show K ≤ H from e.component.1)] at hh'
      exact hh'
  refine ⟨t,ht,htn,fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he),?_,hp⟩
  apply le_antisymm
  · apply iSup_le
    intro g
    rcases hp g g.property.2 with hg | hg
    · exact hg.le.trans le_sup_left
    · exact hg.le.trans le_sup_right
  · exact sup_le (le_componentOrbit _ _)
      (le_iSup (fun g : ((T : Subgroup G) ⊓ H : Subgroup G) =>
        K.conjBy (g : G)) ⟨t,ht⟩)

/-- Movement of K propagates across its actual Sylow orbit. -/
theorem Context.component_orbit_commutator [Fact p.Prime] (h : Context T L p)
    (s : Selected T L u)
    (e : Escape T L p u K)
    (hH : IsSQTK KnownSimple.IsKnownSimple (centralizer ({u} : Set G))) :
    ⁅componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)),XiP p L⁆ =
      componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
  let S := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let D := componentOrbit K S
  have hDH : D ≤ centralizer ({u} : Set G) :=
    (componentOrbit_le_sup K S).trans (sup_le e.component.1 inf_le_right)
  have hHD := (normal_subgroupOf_iff_le_normalizer hDH).mp (e.orbit_normal hH)
  have hXD : XiP p L ≤ normalizer (D : Set G) := by
    exact (XiP_le_moved_centralizer h.hypothesis h.many h.maximal.1
      h.nonquasisimple p s.mem).trans (inf_le_right.trans hHD)
  have hSD : S ≤ normalizer (D : Set G) := le_normalizer_componentOrbit K S
  have hSX : S ≤ normalizer (XiP p L : Set G) :=
    inf_le_left.trans (XiP_invariant p h.sylow_normalizes)
  have hSC : S ≤ normalizer ((⁅D,XiP p L⁆ : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hSD ht),
      mem_normalizer_iff_map_conj_eq.mp (hSX ht)]
  exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hXD)
    (iSup_conjugates_le_of_le_normalizer K S _
      (e.moved.symm.le.trans (commutator_mono (le_componentOrbit K S) le_rfl)) hSC)

/-- The source four-model sieve applies to the intrinsic two-core quotient,
without identifying K itself with that quotient. -/
theorem Context.reducible_component_model [Fact p.Prime]
    (h : Context T L p) (o : OrbitFacts T L p) (s : Selected T L u)
    (e : Escape T L p u K)
    (hH : IsSQTK KnownSimple.IsKnownSimple (centralizer ({u} : Set G)))
    (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    NonnormalCComponentModel (XiQuotient K) := by
  let H := centralizer ({u} : Set G)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (XiQuotient H) :=
    ⟨XiEmbedding.quotient_stronglyQuasithin hH.stronglyQuasithin,hH.isKGroup.quotient _⟩
  have hm := (proposition_1_2_1_three_index_of_A_3_8
    (fun _ _ _ hD hcore B hB =>
      ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple hD hcore B hB)
    hQ e.component.2).resolve_left (h.component_not_normal_of_reducible o s e hr)
  let eK := subgroupOfEquivOfLe e.component.1
  let eQ : XiQuotient (K.subgroupOf H) ≃* XiQuotient K :=
    QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  exact hm.2.of_mulEquiv eQ.symm

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
