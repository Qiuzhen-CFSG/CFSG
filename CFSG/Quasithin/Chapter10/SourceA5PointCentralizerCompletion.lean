module
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerTorus
public import CFSG.Quasithin.Chapter10.SourceElementCentralizerComponent
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerReduced
/-!
# The original A5 point-centralizer endgame

For W=[V,L] and its prescribed conjugate U=W^t, every escaped point
centralizer yields a normal containing component. The quasisimple and
constrained source inspections feed five alternatives: a common centralizer,
a moving cubic scalar, an orbit equal to W, a deleted A7 action, or a
nontrivial characteristic subgroup of Baum(T). Each is eliminated here
using the original vectors, quotient maps, and containing component.
Local Sylow saturation and conjugation then transfer the result to every
nonzero vector of W. The constrained inspection receives the already
proved characteristic-two overgroup and literal reduced orbit module.

The earlier normalizer controls and the two source inspections remain
explicit independent inputs; this module does not assert that the source
classification hypotheses follow for an arbitrary fundamental setup.
Source: Aschbacher–Smith 10.2.9, printed pp.750–753.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The deleted obstruction retains the original setup when the vector is
on the conjugate plane and the containing component contains L itself. -/
theorem source_a5_deleted_partner_point_component_not_seven
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 5)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G)) :
    ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) := by
  let a := MulAut.conj t
  let u := a v
  let H := centralizer ({v} : Set G)
  let J := I.map (a : G →* G)
  have hH : H.map (a : G →* G) = centralizer ({u} : Set G) := by
    change (centralizer ({v} : Set G)).map a.toMonoidHom = _
    rw [map_centralizer_equiv,Set.image_singleton]
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hsquare := conjugate_twice_eq_of_index_two L T (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) inf_le_right ht
  have hV : D.fullModule.map (a : G →* G) = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht))
  have hW : ((⁅D.fullModule,L⁆).map (a : G →* G)).map (a : G →* G) = ⁅D.fullModule,L⁆ := by
    rw [map_commutator,hV,map_commutator,hV]
    exact congrArg (fun K : Subgroup G => ⁅D.fullModule,K⁆) hsquare
  have hu : u ∈ ⁅D.fullModule,L⁆ := hW ▸ mem_map_of_mem (a : G →* G) hv
  have hune : u ≠ 1 := fun h => hvne (a.injective (h.trans a.map_one.symm))
  have hJX : J ≤ centralizer ({u} : Set G) := hH ▸ map_mono hIX
  have hmapI : (I.subgroupOf H).map (a.subgroupMap H).toMonoidHom =
      J.subgroupOf (H.map (a : G →* G)) := by
    apply map_injective (H.map (a : G →* G)).subtype_injective
    rw [map_map,show (H.map (a : G →* G)).subtype.comp (a.subgroupMap H).toMonoidHom =
      (a : G →* G).comp H.subtype from rfl,←map_map,map_subgroupOf_eq_of_le hIX,
      map_subgroupOf_eq_of_le (map_mono hIX)]
  have hJ : (J.subgroupOf (centralizer ({u} : Set G))).IsCComponent := by
    have hh := hI.map_equiv (a.subgroupMap H)
    rwa [hmapI,hH] at hh
  have hNJ : centralizer ({u} : Set G) ≤ normalizer (J : Set G) := by
    rw [←hH]
    exact (map_mono hNI).trans (I.le_normalizer_map (a : G →* G))
  intro he
  let d := (a.subgroupMap I).symm
  have heJ : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7)) :=
    ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans he.some⟩
  exact source_a5_deleted_point_component_not_seven D e c ht htn hu hune J
    (map_mono hLI) hJX hJ hNJ heJ

/-- Source 10.2.6 for W also controls the normalizer and centralizer of the
literal conjugate moved factor. -/
theorem source_a5_partner_moved_normalizer_le
    {t : G} (ht : t ∈ (T : Subgroup G))
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal) :
    normalizer ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom : Set G) ≤ D.maximalLocal := by
  rw [←map_normalizer_eq_of_bijective _ (MulAut.conj t).bijective]
  exact (map_mono hNW).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal.le_normalizer
      (le_normalizer_componentOrbit L T ht)))

/-- The common-centralizer row of the quasisimple embedding inspection is
already contradictory in the original point-centralizer configuration. -/
theorem source_a5_point_component_common_centralizer_impossible
    {t : G} (ht : t ∈ (T : Subgroup G))
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (I : Subgroup G) (hout : ¬ I ≤ D.maximalLocal)
    (hc : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G)) : False := by
  exact hout ((le_centralizer_iff.mp hc).trans
    ((Subgroup.centralizer_le_normalizer _).trans (source_a5_partner_moved_normalizer_le D ht hNW)))

/-- The exceptional A7 row VI=W is eliminated using the actual orbit
normalization, before any classification of the actor quotient. -/
theorem source_a5_point_component_full_moved_orbit_impossible
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (I : Subgroup G) (hout : ¬ I ≤ D.maximalLocal) (Z : Subgroup G)
    (he : conjugateSpanBy Z I = ⁅D.fullModule,L⁆) : False := by
  exact hout ((he ▸ le_normalizer_conjugateSpanBy Z I).trans hNW)

/-- Local Sylow saturation can be made on the opposite original moved
factor: M permutes the two factors and the prescribed t exchanges them. -/
theorem source_a5_moved_point_control_of_partner_saturated
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hpartner : ∀ u ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, u ≠ 1 →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (D.maximalLocal ⊓ centralizer ({u} : Set G)) →
      centralizer ({u} : Set G) ≤ D.maximalLocal) :
    ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  intro v hv hvne
  by_contra hout
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  obtain ⟨m,_,hs⟩ := source_exists_locally_sylow_element D (hWV hv)
  let u := (MulAut.conj (m : G)) v
  have hune : u ≠ 1 := fun he => hvne ((MulAut.conj (m : G)).injective
    (he.trans (map_one _).symm))
  have huout := source_element_centralizer_not_le_conj D hout m
  have humem : u ∈ (⁅D.fullModule,L⁆).map (MulAut.conj (m : G)).toMonoidHom :=
    mem_map_of_mem _ hv
  have hV (g : G) (hg : g ∈ D.maximalLocal) :
      D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hg)
  have hpair : (⁅D.fullModule,L⁆).map (MulAut.conj (m : G)).toMonoidHom = ⁅D.fullModule,L⁆ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj (m : G)).toMonoidHom =
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
    rw [map_commutator,hV m m.property,map_commutator,hV t (le_normalizer_componentOrbit L T ht)]
    rcases source_nonnormal_maximal_pair D hn ht htn m m.property with he | he
    · exact .inl (congrArg (fun K : Subgroup G => ⁅D.fullModule,K⁆) he)
    · exact .inr (congrArg (fun K : Subgroup G => ⁅D.fullModule,K⁆) he)
  rcases hpair with he | he
  · have huW : u ∈ ⁅D.fullModule,L⁆ := he ▸ humem
    let a := MulAut.conj t
    have htM : t ∈ D.maximalLocal := le_normalizer_componentOrbit L T ht
    have hs' := (Chapter1.IsSylowIn.map_iff a.toMonoidHom a.injective).mpr hs
    have hT : (T : Subgroup G).map a.toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    have hM : D.maximalLocal.map a.toMonoidHom = D.maximalLocal :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal.le_normalizer htM)
    rw [Subgroup.map_inf _ _ _ a.injective,Subgroup.map_inf _ _ _ a.injective,
      hT,hM,map_centralizer_equiv,Set.image_singleton] at hs'
    have hc := hpartner (a u) (mem_map_of_mem a.toMonoidHom huW)
      (fun h => hune (a.injective (h.trans a.map_one.symm))) hs'
    exact source_element_centralizer_not_le_conj D huout ⟨t,htM⟩ hc
  · exact huout (hpartner u (he ▸ humem) hune hs)

/-- The literal source embedding/module alternatives. Their production from
A3.12 and the constrained FF classification remains a separate source input. -/
inductive SourceA5PointComponentAlternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : G) (I : Subgroup G) : Prop
  | common (hc : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G))
  | torus (x : G) (hx : orderOf x = 3) (hL : x ∈ sectionCentralizer L)
      (hW : x ∉ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
  | exceptional (Z : Subgroup G) (he : conjugateSpanBy Z I = ⁅D.fullModule,L⁆)
  | ordinary
      (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        ((BinaryPermutation.alternatingNaturalRepresentation (Fin 5)).comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
      (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
  | characteristic (R : Subgroup (ChapterB.baumann (T : Subgroup G)))
      (hchar : R.Characteristic) (hne : R ≠ ⊥)
      (hn : I ≤ normalizer (R.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G))

/-- All endpoint contradictions in 10.2.9, using the original vectors and
components. Both large-group inspections feed this same finite alternative. -/
theorem source_a5_point_component_alternatives_impossible
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hout : ¬ I ≤ D.maximalLocal)
    (hcases : SourceA5PointComponentAlternative D e t I) : False := by
  cases hcases with
  | common hc => exact source_a5_point_component_common_centralizer_impossible D ht hNW I hout hc
  | torus x hx hL hW =>
    exact source_a5_no_moving_cubic_sectionCentralizer D e hn ht htn hsep hNL ⟨x,hx,hL,hW⟩
  | exceptional Z he => exact source_a5_point_component_full_moved_orbit_impossible D hNW I hout Z he
  | ordinary c eI =>
    exact source_a5_deleted_partner_point_component_not_seven D e c ht htn
      hv hvne I hLI hIX hI hNI ⟨eI⟩
  | characteristic R hchar hne hIR =>
    let := hchar
    exact hne (source_overgroup_characteristic_baumann_eq_bot D I hLI hout R hIR)

/-- The remaining source inspection has the actual enlarged component,
normal generation and proved characteristic-two/reduced-module input. -/
@[expose] def SourceA5PointComponentInspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t v : G) : Prop :=
  ∀ I : Subgroup G, L < I → I ≤ centralizer ({v} : Set G) →
      (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent →
      centralizer ({v} : Set G) ≤ normalizer (I : Set G) →
      ¬ I ≤ D.maximalLocal → componentOrbit L I = I →
      (IsQuasisimple I ∨
        (generalizedFitting (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Subgroup G) =
          pCore 2 (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Subgroup G) ∧
        IsPReduced 2 ((conjugateSpanBy
          (⁅D.fullModule,L⁆ ⊓ centralizer (((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) I).subgroupOf
            (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))))) →
      SourceA5PointComponentAlternative D e t I

/-- The point-centralizer endpoint after the two independent source
inspections. The constrained inspection receives the proved exact reduced
module; its construction is no longer an assumption. -/
theorem source_a5_partner_point_centralizer_le_of_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hinspect : SourceA5PointComponentInspection D e t v) :
    centralizer ({v} : Set G) ≤ D.maximalLocal := by
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hmapV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht))
  have hvV : v ∈ D.fullModule := hmapV ▸ (map_mono hWV hv)
  have hCW := (Subgroup.centralizer_le_normalizer _).trans hNW
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  by_contra hout
  obtain ⟨I,hLI,hIX,hI,hNI,hIM,hgen⟩ := source_escaping_element_component D hNL hn
    (D.fullModule_le_sylow hu hvV) hvne (hcross hv) hv0 hs hout
  apply source_a5_point_component_alternatives_impossible D e hn ht htn hsep hNL hNW
    hv hvne I hLI.le hIX hI hNI hIM
  apply hinspect I hLI hIX hI hNI hIM hgen
  by_cases hq : IsQuasisimple I
  · exact .inl hq
  · exact .inr ⟨source_a5_point_component_characteristicTwo D hvV hvne (hcross hv) hCW I hIX hI hq,
      source_a5_point_component_reduced_module D hvV hvne (hcross hv) hCW I hLI.le hIX hI hNI hq hs⟩

/-- Full original moved-vector control once the independent earlier source
normalizer, fixed-vector, Sylow-promotion and embedding inputs are supplied.
The conjugation choice and every endpoint contradiction are discharged here. -/
theorem source_a5_moved_point_centralizers_of_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hfixed : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∈ centralizer (localOrbit T L : Set G) → centralizer ({v} : Set G) ≤ D.maximalLocal)
    (hpromote : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)))
    (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v) :
    ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  apply source_a5_moved_point_control_of_partner_saturated D hn ht htn
  intro v hv hvne hsM
  by_cases hv0 : v ∈ centralizer (localOrbit T L : Set G)
  · exact hfixed v hv hvne hv0
  · have hs := hpromote v hv hvne hv0 hsM
    exact source_a5_partner_point_centralizer_le_of_inspection D e hn ht htn hsep hcross
      hNL hNW hv hvne hv0 hs (hinspect v hv hvne hv0 hs)
end CFSG.Quasithin.Chapter10
