module
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import Theory.SpecificGroups.Alternating.FiveCoreSubgroups
public import Theory.GroupTheory.SolvableResidual.NormalSupplement

/-!
# The residual of an original A5 point centralizer

Let a vector in the original full module centralize L but not L₀. The
index-two orbit is L₀=LL₂, with both original factors normal in L₀.
The two-core of L₀ centralizes the full module because that module lies
in the reduced subgroup of M. Hence the proper point stabilizer in L₂
contains O₂(L₂) and is solvable, using the actual A5 quotient. The point
centralizer is L times this solvable stabilizer, and its solvable residual
is exactly the original perfect subgroup L.

This is the A5 specialization of the residual identification in
Aschbacher–Smith 10.2.10, printed p.753. It uses no escaping Baumann
normalizer or classification of the full module.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The two-core of the original component orbit centralizes the original
full module, before any classification of that module. -/
theorem source_fullModule_orbit_core_centralizes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    (localOrbit T L).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) := by
  have hc : (localOrbit T L).pCoreIn 2 ≤ D.maximalLocal.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (localOrbit T L).le_normalizer le_rfl
  apply hc.trans
  apply le_centralizer_iff.mpr
  intro v hv q hq
  obtain ⟨v',hv',rfl⟩ := D.fullModule_le_reduced_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hv
  obtain ⟨q',hq',rfl⟩ := hq
  exact congrArg Subtype.val (reducedPSubgroup_le_centralizer_pCore 2 D.maximalLocal hv' q' hq')

/-- In the original A5 pair, a full-module vector fixed by the first block
but moved by the pair has exactly that first block as its point-centralizer
solvable residual. -/
theorem source_a5_point_centralizer_residual
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hv : v ∈ D.fullModule)
    (hvL : v ∈ centralizer (L : Set G))
    (hvnot : v ∉ centralizer (localOrbit T L : Set G)) :
    (solvableResidual (localOrbit T L ⊓ centralizer ({v} : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer ({v} : Set G)).subtype = L := by
  let X := localOrbit T L
  let C := centralizer ({v} : Set G)
  obtain ⟨t,ht,_,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let a := MulAut.conj t
  let B := L.map a.toMonoidHom
  have hpair' : X = L ⊔ B := hpair
  have hLX : L ≤ X := hpair' ▸ le_sup_left
  have hBX : B ≤ X := hpair' ▸ le_sup_right
  have hXL : X ≤ normalizer (L : Set G) := source_nonnormal_orbit_le_normalizer D hn
  have hXmap : X.map a.toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_componentOrbit L T) ht)
  have hXB : X ≤ normalizer (B : Set G) := by
    rw [←hXmap]
    exact (map_mono hXL).trans (L.le_normalizer_map a.toMonoidHom)
  have hLC : L ≤ C := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hvL l hl)
  have hBnot : ¬ B ≤ C := by
    intro hBC
    apply hvnot
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((hpair' ▸ sup_le hLC hBC) hx)
  have hcore : B.pCoreIn 2 ≤ C := by
    intro b hb
    have hc := source_fullModule_orbit_core_centralizes D
      (pCoreIn_mono_of_normalizes hBX hXB hb)
    exact mem_centralizer_singleton_iff.mpr (hc v hv).symm
  let N := B ⊓ C
  let K := N.subgroupOf B
  have hKne : K ≠ ⊤ := by
    intro he
    apply hBnot
    intro b hb
    have hh : (⟨b,hb⟩ : B) ∈ K := he ▸ mem_top _
    exact hh.2
  have hcoreK : pCore 2 B ≤ K := by
    intro b hb
    exact ⟨b.property,hcore (mem_map_of_mem B.subtype hb)⟩
  let eb : B ≃* L := (a.subgroupMap L).symm
  let eq : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  let : Group.IsSolvable K :=
    alternatingGroup.isSolvable_proper_subgroup_containing_twoCore (eq.trans e) K hKne hcoreK
  let : Group.IsSolvable N := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe (show N ≤ B from inf_le_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show N ≤ B from inf_le_left)).surjective
  have hsplit : X ⊓ C = L ⊔ N := by
    apply le_antisymm
    · intro x hx
      have hp : x ∈ (L : Set G) * (B : Set G) := by
        rw [←coe_mul_of_left_le_normalizer_right L B (hLX.trans hXB),←hpair']
        exact hx.1
      obtain ⟨l,hl,b,hb,rfl⟩ := hp
      have hbc : b ∈ C := by
        simpa only [inv_mul_cancel_left] using C.mul_mem (C.inv_mem (hLC hl)) hx.2
      exact mul_mem_sup hl ⟨hb,hbc⟩
    · exact sup_le (le_inf hLX hLC) (le_inf (inf_le_left.trans hBX) inf_le_right)
  let := Chapter1.mem_L_isPerfect D.maximal.1
  rw [show localOrbit T L ⊓ centralizer ({v} : Set G) = L ⊔ N from hsplit]
  exact map_solvableResidual_sup_eq_of_perfect_normalized L N (inf_le_left.trans (hBX.trans hXL))

/-- A perfect conjugate component inside the original point centralizer
must lie in L. This is the inclusion used in the intersection argument. -/
theorem source_a5_point_centralizer_perfect_subgroup_le
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hv : v ∈ D.fullModule)
    (hvL : v ∈ centralizer (L : Set G))
    (hvnot : v ∉ centralizer (localOrbit T L : Set G))
    (A : Subgroup G) [Group.IsPerfect A]
    (hA : A ≤ localOrbit T L ⊓ centralizer ({v} : Set G)) : A ≤ L := by
  rw [←source_a5_point_centralizer_residual D e hn hv hvL hvnot]
  exact le_map_solvableResidual_of_isPerfect A _ hA

end CFSG.Quasithin.Chapter10
