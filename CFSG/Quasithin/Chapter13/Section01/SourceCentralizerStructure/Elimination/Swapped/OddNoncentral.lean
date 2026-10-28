module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Orbit

/-!
# Odd Sylow noncentrality for the exchanged component

The existing escape record gives noncontainment for the whole canonical radical
`XiP p L`. Under an explicit
commutator bound on the two-core of `XiP p L`, the odd Sylow image is noncentral modulo the literal two-core of
`C_G(u)`. The proof keeps the ambient image of the Sylow subgroup and the
original centralizer quotient unchanged.

The unconditional result, which does not need that bound, is proved in
`Swapped.Containment.Noncentral` using two-perfectness.

Source: Aschbacher--Smith, 13.1.12(3), printed p.874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/--
A sufficient clause for passing from full radical movement to an odd
Sylow witness.  The clause
`⁅(XiP p L).pCoreIn 2, K⁆ ≤ C_G(u).pCoreIn 2` is not part of `Escape`; it is
kept explicit in this conditional interface.
-/
theorem Context.exists_odd_sylow_noncentral_of_twoCore_commutator_bound
    (h : Context T L p) (_o : OrbitFacts T L p) (_c : Control T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G}
    (e : Escape T L p u K)
    (_hr : ¬ ComponentNormalizerIrreducible L K p u)
    (hcore : ⁅(XiP p L).pCoreIn 2, K⁆ ≤
      (centralizer ({u} : Set G)).pCoreIn 2) :
    ∃ P : Sylow p (XiP p L),
      ¬ ⁅K,((P : Subgroup (XiP p L)).map (XiP p L).subtype)⁆ ≤
        (centralizer ({u} : Set G)).pCoreIn 2 := by
  let H := centralizer ({u} : Set G)
  let X := XiP p L
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  have hQ := uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2
  have hq := (XiP_oddQuotient_of_A36 h36 h.maximal.1.1 hQ h.nonquasisimple h.odd h.divides).2
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p X))
  let P₀ := (P : Subgroup X).map X.subtype
  have htop : (P : Subgroup X).map (QuotientGroup.mk' (pCore 2 X)) = ⊤ := by
    apply top_unique
    exact (hq.isPGroup.to_subgroup ⊤).le_sylow_of_normal
      (P.mapSurjective (QuotientGroup.mk'_surjective _))
  have hsup : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
    have hh := congrArg (fun A : Subgroup (XiQuotient X) =>
        A.comap (QuotientGroup.mk' (pCore 2 X))) htop
    simpa only [QuotientGroup.ker_mk', comap_map_eq, comap_top, sup_comm] using hh
  have hfactor : X.pCoreIn 2 ⊔ P₀ = X := by
    have hh := congrArg (fun A : Subgroup X => A.map X.subtype) hsup
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, X.range_subtype,
      pCoreIn, P₀] using hh
  have hXH : X ≤ H := (SourceNonquasisimple.XiP_le_moved_centralizer h.hypothesis h.many h.maximal.1
    h.nonquasisimple p s.mem).trans inf_le_right
  have hHC : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hXC : X ≤ normalizer (H.pCoreIn 2 : Set G) := hXH.trans hHC
  refine ⟨P, ?_⟩
  intro hP
  apply e.moved_mod_core
  have hcomm : ⁅X.pCoreIn 2 ⊔ P₀, K⁆ ≤ H.pCoreIn 2 := by
    apply commutator_sup_le_of_relative_normal X (X.pCoreIn 2) P₀ K (H.pCoreIn 2)
      hXC (pCoreIn_le 2 X) (map_subtype_le _)
    · exact hcore
    · rw [commutator_comm]
      exact hP
  rwa [hfactor,commutator_comm] at hcomm

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
