module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonbinaryElementaryCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalElementaryFiniteQuotient

/-!
# Constructed nonbinary elementary four-path roots

Lift the original full-Cartan involutions through the locally injective
universal cover. The lifts preserve their squares, endpoint action and the
normalizer of the same full Cartan. Choose the compatible Cartans supplied
by F.1.3, and apply the proved five-path transitivity and odd fixer theorem.
This constructs both root actions from actual four-path stabilizer cores;
each acts sharply transitively on the exits at its original endpoint.

The consumer retains each defining path, its marked last edge and support
in the constructed reflection apartment. No local catalogue, Cartan choice,
reflection, root subgroup or transitivity witness is supplied by the caller.
The nonbinary condition concerns the literal original beta quotient.
The binary and nonelementary branches, exchange, the Borel root signs and
complete marked comparison remain open; these root actions alone do not
establish the whole source recognition theorem.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175,
(14.1)--(14.2) and the root notation, pp.210--211.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile CommutingNontrivial
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (Reduction.G₀ L S))
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily (reducedAmalgam L S)
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype ⧸
        pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype)) 2 2)
include h hc hb hcomm helem hnb

omit h hc hb hcomm helem hnb in
private theorem elementary_middle_eq_overlap : originalMiddle A = T false ⊓ T true := by
  exact (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).symm

omit h hc hb hcomm helem hnb in
private theorem elementary_middle_le_endpoint (i : Bool) : originalMiddle A ≤ T i := by
  rw [elementary_middle_eq_overlap]
  cases i
  · exact inf_le_left
  · exact inf_le_right

/-- Each original universal endpoint contains the required involution,
normalizing the same prescribed full Cartan. -/
theorem original_elementary_nonbinary_tree_reflection
    (c : CompatibleCartans L (reducedSylow L S)) (i : Bool) :
    ∃ t : (reducedAmalgam L S).Universal, t • base T i = base T i ∧
      t • base T (!i) ≠ base T (!i) ∧ t*t=1 ∧
      t ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal) := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let U := (twoGroup L S).map φ
  let E := F false ⊓ F true
  let : Finite (F false) := (finite_endpoints (reduced_triple h)) false
  let : Finite (F true) := (finite_endpoints (reduced_triple h)) true
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hmapE : (originalMiddle A).map φ = E := by
    rw [elementary_middle_eq_overlap]
    exact cov.map_inf
  have hCE : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hUE : U ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hUnorm : E ≤ normalizer (U : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hUcore : U ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hUE hUnorm
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  have hd : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨m,hm⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hm]; exact ho.coprime_two_right.pow_right m)
  have hg : C ⊔ E.pCoreIn 2 = E := by
    apply le_antisymm (sup_le hCE (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    calc
      E = U ⊔ C := he.symm
      _ ≤ C ⊔ E.pCoreIn 2 :=
        sup_le (hUcore.trans le_sup_right) le_sup_left
  have hEi : E = stabilizer F (base F i) ⊓ stabilizer F (base F (!i)) := by
    have hi : stabilizer F (base F i) = F i :=
      Subgroup.CosetGeometry.stabilizer_base F i
    have hni : stabilizer F (base F (!i)) = F (!i) :=
      Subgroup.CosetGeometry.stabilizer_base F (!i)
    rw [hi, hni]
    cases i
    · rfl
    · exact inf_comm _ _
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨g,_,hgC,hgsq,hgfix,hgmove⟩ := original_elementary_nonbinary_cartan_reflection
    h hc hb hcomm helem hnb hadj C (hEi ▸ hCE) ho (hEi ▸ hd) (hEi ▸ hg)
  have hgFi : g ∈ F i := by
    rw [←Subgroup.CosetGeometry.stabilizer_base F i]
    exact hgfix
  have hgimage : g ∈ (T i).map φ := (cov.map_eq i).symm ▸ hgFi
  obtain ⟨t,ht,htg⟩ := hgimage
  have hfix : t • base T i = base T i := by
    have hh := ht
    rw [←Subgroup.CosetGeometry.stabilizer_base T i] at hh
    exact hh
  have hmove : t • base T (!i) ≠ base T (!i) := by
    intro he
    have hh := congrArg cov.vertex he
    apply hgmove
    have hh' : (bOne_tree_map h) t • base (reducedFamily L S) (!i) =
        base (reducedFamily L S) (!i) := by
      simpa only [cov.vertex_smul, cov.vertex_base] using hh
    change φ t • base F (!i) = base F (!i) at hh'
    rw [← htg]
    exact hh'
  have hsq : t*t=1 := by
    have he : φ (t*t) = φ 1 := by rw [map_mul,htg,hgsq,map_one]
    exact congrArg Subtype.val (cov.injective i
      (a₁ := ⟨t*t,(T i).mul_mem ht ht⟩) (a₂ := 1) he)
  have hKi : cartan c ≤ T i := (cartan_le c).trans (elementary_middle_le_endpoint i)
  let Ki := (cartan c).subgroupOf (T i)
  let f : T i →* G₀ := φ.comp (T i).subtype
  have hf : Function.Injective f := cov.injective i
  have hKmap : Ki.map f = C := by
    change Ki.map (φ.comp (T i).subtype) = C
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le hKi]
  have htKi : (⟨t,ht⟩ : T i) ∈ normalizer (Ki : Set (T i)) := by
    have hh : (⟨t,ht⟩ : T i) ∈ (normalizer (Ki.map f : Set G₀)).comap f := by
      change f ⟨t,ht⟩ ∈ normalizer (Ki.map f : Set G₀)
      rw [hKmap]
      exact htg.symm ▸ hgC
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective hf] at hh
    exact hh
  have hnorm := Ki.le_normalizer_map (T i).subtype (mem_map_of_mem (T i).subtype htKi)
  rw [map_subgroupOf_eq_of_le hKi] at hnorm
  exact ⟨t,hfix,hmove,hsq,hnorm⟩

/-- Both involutions normalize the same full original Cartan. -/
theorem original_elementary_nonbinary_tree_reflections
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ t : Bool → (reducedAmalgam L S).Universal,
      (∀ i, t i • base T i = base T i) ∧
      (∀ i, t i • base T (!i) ≠ base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal)) := by
  choose t htfix htmove htsq htnorm using
    (fun i => original_elementary_nonbinary_tree_reflection h hc hb hcomm helem hnb c i)
  exact ⟨t,htfix,htmove,htsq,htnorm⟩

/-- Construct the two four-path roots from the original nonbinary elementary
source. The same chosen full Cartan and the actual involutions are retained;
each root acts sharply transitively on its marked exits. -/
theorem original_elementary_nonbinary_path_roots :
    ∃ ρ : Bool → LocalRootAction (X := (reducedAmalgam L S).Universal)
        (sourceGraph (reducedAmalgam L S)),
      (∀ i, (ρ i).a = base T i) ∧
      (∀ i, (ρ i).b = base T (!i)) ∧
      (∀ i, (ρ i).reflection ∈ normalizer
        (cartan (chosenCartans h) : Set (reducedAmalgam L S).Universal)) ∧
      (∀ i, (ρ i).reflection * (ρ i).reflection = 1) ∧
      (∀ i, ∃ d, ∃ p : (sourceGraph (reducedAmalgam L S)).Walk d (base T i),
        p.IsPath ∧ p.length = 4 ∧ p.penultimate = base T (!i) ∧
        (ρ i).root = (pathFixer (X := (reducedAmalgam L S).Universal) p).pCoreIn 2 ∧
        cartan (chosenCartans h) ≤ pathFixer (X := (reducedAmalgam L S).Universal) p ∧
        ∀ z ∈ p.support, z ∈ cartanApartment (reducedAmalgam L S)
          (apartmentGroup (chosenCartans h) ρ)) ∧
      (∀ i z, (sourceGraph (reducedAmalgam L S)).Adj (ρ i).a z → z ≠ (ρ i).b →
        ∃! x : (ρ i).root, (x : (reducedAmalgam L S).Universal) • (ρ i).c = z) := by
  let c := chosenCartans h
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb c
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hthick := original_source_tree_thickness h t
  let ρ := pathRoots h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  refine ⟨ρ,?_,?_,?_,?_,?_,?_⟩
  · exact pathRoots_a h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  · exact pathRoots_b h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  · exact pathRoots_normalizes h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  · exact pathRoots_square h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  · intro i
    let p := reflectionPath c t htfix htmove htnorm 4 (by decide) i
    exact ⟨p.start,p.walk,p.isPath,p.length_eq,p.previous,rfl,p.fixed,
      pathRoots_supported h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick i⟩
  · exact pathRoots_sharply_transitive h c 4 (by decide) t htfix htmove htsq htnorm
      hpath.1 hthick hpath.2

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
