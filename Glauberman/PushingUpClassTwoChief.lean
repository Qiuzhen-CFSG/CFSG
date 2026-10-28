module
public import Glauberman.PushingUpFullCenters
public import Glauberman.PushingUpTheoremBReduction
public import Theory.GroupTheory.CentralCoreActionKernel
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralChiefInterval
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The class-two branch of the original Main Hypothesis

The two generating Sylow subgroups have class at most two, so their
commutators with the two-core lie in its center. The whole ambient group
therefore centralizes the core modulo its center. The natural central-omega
chief interval is consequently the only noncentral chief layer. The paired
automorphism kernel argument identifies its centralizer with the two-core,
giving the literal SL₂(4) quotient marking.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 5.5(a)
and Corollary 5.6, printed pp.51–52. The independent class bound remains
explicit; no chief-count or quotient-recognition premise remains.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace Glauberman
universe u v
variable {H : Type u} {F : Type v} [Group H] [Finite H] [Field F] [Finite F]

omit [Finite H] in
private theorem commutator_le_centerIn_of_class_two (S : Subgroup H)
    [Group.IsNilpotent S] (hc : Group.nilpotencyClass S ≤ 2) : ⁅S,S⁆ ≤ centerIn S := by
  have hbot : (⊤ : Subgroup S).lowerCentralSeries 2 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc
  have hcomm : _root_.commutator S ≤ center S := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one] at hbot
    exact hbot
  rw [centerIn_eq_map_center, ← map_subtype_commutator]
  exact map_mono hcomm

/-- Class at most two makes the original two-core quotient by its center
central in the ambient group, as in Niles 5.5(a). -/
theorem original_psl2_four_core_commutator_of_class_two
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (hclass : Group.nilpotencyClass S ≤ 2) :
    ⁅(⊤ : Subgroup H), pCore 2 H⁆ ≤ omegaCenterIn (pCore 2 H) := by
  let _ := S.isPGroup'.isNilpotent
  obtain ⟨g, hgen, _, _⟩ := Theory.SpecificGroups.SL2.original_twisted_pair_of_psl2_four
    hF S α hu K e hno
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hclassT : Group.nilpotencyClass T ≤ 2 := by
    let f : S ≃* T := (MulAut.conj g).subgroupMap (S : Subgroup H)
    exact (Group.nilpotencyClass_le_of_surjective f.toMonoidHom f.surjective).trans hclass
  have hcentral (P : Sylow 2 H)
      (hcP : Group.nilpotencyClass P ≤ 2) :
      ⁅(P : Subgroup H), pCore 2 H⁆ ≤ omegaCenterIn (pCore 2 H) := by
    let _ := P.isPGroup'.isNilpotent
    have hPQ : pCore 2 H ≤ (P : Subgroup H) := pCore_isPGroup.le_sylow_of_normal P
    have hd := commutator_le_centerIn_of_class_two (P : Subgroup H) hcP
    have hZ : centerIn (P : Subgroup H) ≤ pCore 2 H := by
      have hCQ : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
        simpa only [hf] using centralizer_generalizedFitting_le H
      exact inf_le_right.trans ((centralizer_le hPQ).trans hCQ)
    have hZV : centerIn (P : Subgroup H) ≤ centerIn (pCore 2 H) :=
      le_inf hZ (inf_le_right.trans (centralizer_le hPQ))
    rw [(original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno).2]
    exact ((commutator_mono le_rfl hPQ).trans hd).trans hZV
  have hh := commutator_sup_le_of_relative_normal (⊤ : Subgroup H)
    (S : Subgroup H) (T : Subgroup H) (pCore 2 H) (omegaCenterIn (pCore 2 H))
    (by let _ := omegaCenterIn_normal_of_normal (pCore 2 H); exact le_normalizer_of_normal)
    le_top le_top (hcentral S hclass) (hcentral T hclassT)
  rwa [show (S : Subgroup H) ⊔ (T : Subgroup H) = ⊤ from hgen] at hh

/-- The class-two Main Hypothesis has exactly one noncentral chief factor,
and the quotient by the literal two-core is SL₂(4). -/
theorem original_psl2_four_quotient_chief_of_class_two
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (hclass : Group.nilpotencyClass S ≤ 2) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL) ∧
      ∀ t : NoncentralChiefRefinement.SeriesOn (pCore 2 H), t.noncentralCount = 1 := by
  have hcomm := original_psl2_four_core_commutator_of_class_two
    hF S α hu K e hf hno hclass
  have hcenter := (original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno).2
  have hcentral : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    simpa only [hf] using centralizer_generalizedFitting_le H
  have hker : centralizer (omegaCenterIn (pCore 2 H) : Set H) = pCore 2 H := by
    rw [hcenter]
    apply centralizer_centerIn_pCore_eq 2 hcentral
    rwa [← hcenter]
  obtain ⟨q,hq,hk,hcov,hn,_,_,_⟩ := original_psl2_four_natural_chief_data
    hF S hu K e hf hno.noCharacteristicNormal
  refine ⟨⟨QuotientGroup.liftEquiv (pCore 2 H) hq (hk.trans hker).symm⟩, ?_⟩
  intro t
  apply NoncentralChiefRefinement.SeriesOn.noncentralCount_eq_one_of_central_chief_strata
    pCore_isPGroup (centralOmegaNode H) (omegaNode H) ?_ hcov hn ?_ ?_ t
  · rw [NoncentralChiefRefinement.isCentral_iff_commutator_le]
    exact (commutator_top_left_eq_bot_iff_le_center.mpr inf_le_right).le
  · intro x hx
    exact ((mem_omegaCenterIn_iff _ _).mp hx).1
  · exact (NoncentralChiefRefinement.isCentral_iff_commutator_le _ _).mpr hcomm

/-- The original Niles Theorem B follows from only the independent Main
Hypothesis Sylow class bound; exponent, quotient and all chief-factor markings
are derived from the original source hypotheses. -/
theorem niles_theoremB_four_of_main_class
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hmain : ∀ (X : Type u) [Group X] [Finite X] (P : Sylow 2 X)
      (L : Subgroup X) [L.Normal],
      ((X ⧸ L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) →
      generalizedFitting X = pCore 2 X →
      Order.HasUniqueMaximalOver (P : Subgroup X) ⊤ →
      (∃ β : MulAut P, NoInvariantNormal (P : Subgroup X) β) →
      Group.nilpotencyClass P ≤ 2) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
      ∃ eQ : (H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL,
        K = pCore 2 H ∧
        ∀ s : SeriesOn (pCore 2 H), s.noncentralCount = 1 ∧
          ∀ i : Fin s.series.length, ¬ s.Central i →
            Nat.card (s.Factor i) = 16 ∧
            ∃ f : s.Factor i ≃* Multiplicative Representation.SL2FourNatural.V,
              ∀ h x, (f (s.action i h x)).toAdd =
                Representation.specialLinearNatural 2
                  (eQ (QuotientGroup.mk' (pCore 2 H) h)) (f x).toAdd := by
  apply niles_theoremB_four_of_main_class_chief hF S hu K e hf hno
  intro X _ _ P L _ eL hfX huP hb
  have hcl := hmain X P L eL hfX huP hb
  obtain ⟨β,hβ⟩ := hb
  obtain ⟨he,hcount⟩ := original_psl2_four_quotient_chief_of_class_two
    hF P β huP L eL hfX hβ hcl
  obtain ⟨t⟩ := NoncentralChiefRefinement.SeriesOn.exists_series (pCore 2 X)
  exact ⟨hcl,he,t,hcount t⟩

end Glauberman
