module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.ConstructionResidual
public import Theory.GroupTheory.WeakClosureCentralizerSylow

/-!
# The original opposite centralizer is Sylow

The abelian span X is weakly closed in the supplied T. Its normalizer
preserves the source plane V, and Ω₁(X)=V⟨w⟩. The original R is transitive
on Vw, so every normalizer conjugate of w is already T-conjugate to w.
The weak-closure Sylow argument proves that the literal C_T(w) is Sylow
in C_G(w), and hence also in C_H(w), without changing T or the RQ marking.

Source: Aschbacher--Smith 14.3.22, printed p.999.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s


/-- The literal opposite centralizer in the supplied T is globally Sylow. -/
theorem source_triple_global_sylow
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    ∃ S : Sylow 2 (centralizer ({tripleProduct d a} : Set G)),
      (S : Subgroup _).map (centralizer ({tripleProduct d a} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G) := by
  let := hc.abelian
  have hwX := s.product_mem_span hc
  have hwV : tripleProduct d a ∉ rankTwoSeed T M := by
    intro hw
    exact source_triple_outside_transfer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
      (mem_sup_right (s.seed_le_core hw))
  have hw1 : tripleProduct d a ≠ 1 := fun he => hwV (he ▸ (rankTwoSeed T M).one_mem)
  have hRT := (source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1
  obtain ⟨_,_,_,_,_,_,_,_,hNM⟩ := source_supplement_span
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc.strict
  have hNV : normalizer (span F : Set G) ≤ normalizer (rankTwoSeed T M : Set G) := by
    rw [span_eq_conjugateSpanIn]
    exact hNM.trans RankTwoHypothesis.M_normalizes_seed
  apply T.centralizer_sylow_of_weakly_closed_orbit (span F) (tripleProduct d a)
    (conjugateSubgroupClosure_le_self _ _)
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mul_comm' (⟨x,hx⟩ : span F) ⟨_,hwX⟩))
  · intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [span_eq_conjugateSpanIn] at hb ⊢
    exact ChapterI.Section06To08.conjugateSpanIn_weakly_closed b hb
  · apply normalizer_orbit_of_omega_coset (T : Subgroup G) (span F) (rankTwoSeed T M)
      (tripleProduct d a) hc.seed_le hwX (s.involution_of_ne_one hc hw1).2 hwV hNV
      (source_span_omega hG T hempty hM hu hmany hcard e F hc s)
    intro v hv
    obtain ⟨r,hr,he⟩ := (source_triple_core_orbit_and_card
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).1 v hv
    exact ⟨r,hRT hr,he⟩

/-- The same Sylow subgroup restricts to the original point centralizer. -/
theorem source_triple_local_sylow
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    ∃ S : Sylow 2 (F.H ⊓ centralizer ({tripleProduct d a} : Set G) : Subgroup G),
      (S : Subgroup _).map (F.H ⊓ centralizer ({tripleProduct d a} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G) := by
  obtain ⟨S,hS⟩ := source_triple_global_sylow
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  let C := centralizer ({tripleProduct d a} : Set G)
  let H := F.H ⊓ C
  have hHC : H ≤ C := inf_le_right
  have hSH : (S : Subgroup C) ≤ H.subgroupOf C := by
    intro x hx
    have hxT : (x : G) ∈ (T : Subgroup G) := (hS ▸ mem_map_of_mem C.subtype hx).1
    exact ⟨F.invariant 1 hxT,x.property⟩
  let eH := subgroupOfEquivOfLe hHC
  let S' := (S.subtype hSH).mapSurjective (f := eH.toMonoidHom) eH.surjective
  refine ⟨S',?_⟩
  change (((S : Subgroup C).subgroupOf (H.subgroupOf C)).map
    eH.toMonoidHom).map H.subtype = _
  rw [map_map]
  have he : H.subtype.comp eH.toMonoidHom = C.subtype.comp (H.subgroupOf C).subtype := rfl
  rw [he,←map_map,map_subgroupOf_eq_of_le hSH]
  exact hS

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
