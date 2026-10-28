module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NineAmbientParallel.CoreGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.MovedQuotient

/-!
# The two cubic supports on the original moved section

Restrict the original quotient representation to its four-dimensional moved
space. Its faithful elementary-nine residual supplies two cubic support
planes. Minimal normality and the same Sylow image force an actual element
of T to exchange the two cubic subgroups. For each subgroup, original
14.6.2 puts the original central point in the commutator with the two-residual
of its full preimage through J → J/O₂(J).

These are supports inside the singleton factor, not the two dihedral factors
asserted by 14.6.12. In particular their exchange does not exclude E₉:C₄.
The ambient exclusion remains open.

Source: Aschbacher--Smith, 14.6.2 and 14.6.12, printed pp.1021,1031;
D.2.17(3), printed p.188.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab



open OddCriticalPair.OrthogonalSource

/-- The two cubic supports belong to the literal original residual. Their
source lifts move the original point and the original Sylow exchanges them. -/
theorem source_singleton_nine_support_planes
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    ∃ s : ChapterD.FittingConfigurations.SupportFactors (movedRepresentation a)
        (pResidual 2 (J ⧸ pCore 2 J)) 2,
      (∃ t : T, (s.ambient 0).conjBy
        (QuotientGroup.mk' (pCore 2 J) ⟨(t : G),hJ.1.1.2 t.property⟩) = s.ambient 1) ∧
      ∀ i : Fin 2,
        let A := (s.ambient i).comap (QuotientGroup.mk' (pCore 2 J))
        centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) J,
          ((pResidual 2 A).map A.subtype).map J.subtype⁆ := by
  let P := pResidual 2 (J ⧸ pCore 2 J)
  have hdimE : IsElementaryAbelian 3 P ∧ Module.finrank (ZMod 2) (movedSpace a) = 4 := by
    obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
    have hc := source_singleton_factor_star_cyclic hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hone i
    have halt := source_ratio_singleton_cyclicStar_alternatives
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd i hi hc
    rcases halt with hcyc | ⟨hE,_,hdim⟩
    · let := hcyc
      obtain ⟨p,hp,hE,_,_,_⟩ := source_solvable_minimal_elementary_residual
        hG T hempty hM hu hmany hcard e hab J hJ hs
      let := hE
      have hv := IsElementaryAbelian.exponent_dvd_p (p := p)
        (G := pResidual 2 (J ⧸ pCore 2 J))
      rw [IsCyclic.exponent_eq_card,hnine] at hv
      rcases hp with rfl | rfl <;> norm_num at hv
    · refine ⟨hE,?_⟩
      rw [movedSpace,source_rankTwo_whole_moved_eq_residual
        hG T hempty hM hu hmany hcard e hab J hJ.1 a]
      exact hdim
  let : IsElementaryAbelian 3 P := hdimE.1
  let W : Subrepresentation a.representation := {
    toSubmodule := movedSpace a
    apply_mem_toSubmodule := fun g _ hv => (movedSpace_invariant a (mem_top g) _).mpr hv }
  have hspan : W.toSubmodule ⊔ fixedSpace a.representation ⊤ = ⊤ := by
    change movedSpace a ⊔ fixedSpace a.representation ⊤ = ⊤
    rw [movedSpace,source_rankTwo_whole_moved_eq_residual
      hG T hempty hM hu hmany hcard e hab J hJ.1 a]
    exact source_rankTwo_span_decomposition hG T hempty hM hu hmany hcard e hab J hJ.1 a
  have hf : Function.Injective (movedRepresentation a) :=
    ChapterD.SourceReduction.subrepresentation_faithful_of_fixed_complement
      a.representation a.faithful W hspan
  have hm : subspaceCommutator (movedRepresentation a) ⊤ P = ⊤ := by
    apply Submodule.map_injective_of_injective (movedSpace a).subtype_injective
    have hh := subspaceCommutator_map_embedding a.representation (movedRepresentation a)
      (MonoidHom.id _) (movedSpace a).subtype (fun _ _ => rfl) P ⊤
    have hm : subspaceCommutator a.representation (movedSpace a) P = movedSpace a := by
      rw [movedSpace,source_rankTwo_whole_moved_eq_residual
        hG T hempty hM hu hmany hcard e hab J hJ.1 a]
      exact NormalOddSeed.odd_moved_self a.representation P (hnine ▸ (by decide : Odd 9))
    simpa only [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id,hm] using hh.symm
  obtain ⟨s⟩ := ChapterD.FittingConfigurations.supportFactors_of_nine_four_moved
    (movedRepresentation a) hf P hnine hdimE.2 hm
  have hc (i : Fin 2) : Nat.card (s.ambient i) = 3 :=
    (card_map_of_injective P.subtype_injective).trans (s.card_factor i)
  have hne (i : Fin 2) : s.ambient i ≠ ⊥ := by
    intro hz
    have hh := hc i
    rw [hz,card_bot] at hh
    omega
  refine ⟨s,?_,?_⟩
  · let q := QuotientGroup.mk' (pCore 2 J)
    let S := ((T : Subgroup G).subgroupOf J).map q
    have hgen : P ⊔ S = ⊤ := pResidual_sup_sylow_eq_top
      ((T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J)))
    have hx : ∃ t ∈ S, (s.ambient 0).conjBy t = s.ambient 1 := by
      by_contra hn
      push Not at hn
      have hSN : S ≤ normalizer (s.ambient 0 : Set (J ⧸ pCore 2 J)) := by
        intro t ht
        apply mem_normalizer_iff_map_conj_eq.mpr
        obtain ⟨j,hj⟩ := s.factor_conj_closed (movedRepresentation a) hf t 0
        fin_cases j
        · exact hj
        · exact (hn t ht hj).elim
      have hPN : P ≤ normalizer (s.ambient 0 : Set (J ⧸ pCore 2 J)) :=
        ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
          (centralizer_le (show s.ambient 0 ≤ P from map_subtype_le _))).trans
            (Subgroup.centralizer_le_normalizer _)
      have hBN : (s.ambient 0).Normal := normalizer_eq_top_iff.mp
        (top_unique (hgen ▸ sup_le hPN hSN))
      obtain ⟨_,_,_,_,_,hmin⟩ := source_solvable_minimal_elementary_residual
        hG T hempty hM hu hmany hcard e hab J hJ hs
      have he := (hmin (s.ambient 0) hBN (map_subtype_le _)).resolve_left (hne 0)
      have hh := hc 0
      rw [he,hnine] at hh
      omega
    obtain ⟨t,⟨x,hx,hxt⟩,ht⟩ := hx
    exact ⟨⟨(x : G),hx⟩,hxt ▸ ht⟩
  · intro i
    exact source_point_le_lifted_odd_factor hG T hempty hM hu hmany hcard e hab
      J hJ hs (s.ambient i) (map_subtype_le _) (hne i)

end CFSG.Quasithin.Chapter14.Section06
