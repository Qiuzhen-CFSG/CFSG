module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.Common
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.AlternatingGeometry
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowNormalizedSupIntersection
public import Theory.Representation.BinaryOffender.IrreducibleCentralSeed
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The S₆ marked parabolic in 13.5.21

The checked A₆ plane recognition bounds the even part of a Sylow-invariant
plane stabilizer by 24. Its full S₆ stabilizer consequently has order at
most 48 and index at most three over a Sylow two-subgroup.

In the source application the model is the actual K*V*, while the
stabilizer is taken in K*T*. The supplement index formula handles this
larger actor without putting T* inside K*V*. Irreducibility and generation
of the original seed make its central projection injective. The calculation
therefore applies to Action.seedSpace, including possible central extensions
of the whole module. Basic then identifies the exact local product and
its embedded two-residual.

These results establish the S₆ part of clause (5); generation by L₁ in
clause (6) remains a separate model calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21(5), printed p.924 (PDF p.941).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics

/-- The actual six-letter natural plane has stabilizer index at most three. -/
theorem six_plane_index (S : Sylow 2 (Equiv.Perm (Fin 6))) (J : Subgroup (Equiv.Perm (Fin 6)))
    (hSJ : (S : Subgroup _) ≤ J)
    (E : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hdim : Module.finrank (ZMod 2) E = 2)
    (hE : J ≤ subspaceStabilizer (BinaryPermutation.naturalRepresentation (Fin 6)) E) :
    (S : Subgroup _).relIndex J ≤ 3 := by
  let A := alternatingGroup (Fin 6)
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal A
  have hRJ : (R : Subgroup A) ≤ J.subgroupOf A := by
    rw [hR]
    exact comap_mono hSJ
  have hEA : J.subgroupOf A ≤ subspaceStabilizer
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) E := by
    intro j hj
    exact hE hj
  obtain ⟨g, hg⟩ := alternating_plane_placement R (J.subgroupOf A) hRJ E hdim hEA
  have h24 : Nat.card (J.subgroupOf A) ≤ 24 := by
    have hh := Nat.card_le_card_of_injective (inclusion hg) (inclusion_injective hg)
    rw [card_map_of_injective (MulAut.conj g).injective] at hh
    exact hh.trans_eq a6SynthemeStabilizer_order
  have hcard : Nat.card (A.subgroupOf J) = Nat.card (J.subgroupOf A) :=
    Nat.card_congr {
      toFun := fun x => ⟨⟨x.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hi : (A.subgroupOf J).index ≤ 2 := by
    have hh := relIndex_le_of_le_right (show J ≤ ⊤ from le_top)
      (show A.relIndex ⊤ ≠ 0 from index_ne_zero_of_finite)
    rw [relIndex_top_right] at hh
    change (A.subgroupOf J).index ≤ A.index at hh
    simpa only [A, alternatingGroup.index_eq_two] using hh
  have h48 : Nat.card J ≤ 48 := by
    have hh := (A.subgroupOf J).card_mul_index
    rw [hcard] at hh
    nlinarith
  have hs : Nat.card S = 16 :=
    (Nat.card_congr (S.equiv borelSylow).toEquiv).trans borel_order
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (Equiv.Perm (Fin 6)))
    (S : Subgroup _) J bot_le hSJ
  simp only [relIndex_bot_left] at hh
  rw [hs] at hh
  omega

/-- Restriction to the model computes the bound with the entire ambient Sylow retained. -/
theorem six_supplement_index {G U : Type*} [Group G] [Finite G]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) G U) (B : Subgroup G) (T : Sylow 2 G)
    (hn : (T : Subgroup G) ≤ normalizer (B : Set G))
    (R : Sylow 2 B) (hR : (R : Subgroup B) = (T : Subgroup G).subgroupOf B)
    (e : B ≃* Equiv.Perm (Fin 6))
    (p : U →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hp : ∀ b : B, ∀ u, p (ρ b.val u) =
      BinaryPermutation.naturalRepresentation (Fin 6) (e b) (p u))
    (E : Submodule (ZMod 2) U)
    (hdim : Module.finrank (ZMod 2) (E.map p) = 2)
    (hT : (T : Subgroup G) ≤ subspaceStabilizer ρ E) :
    (T : Subgroup G).relIndex ((B ⊔ (T : Subgroup G)) ⊓ subspaceStabilizer ρ E) ≤ 3 := by
  let P := (B ⊔ (T : Subgroup G)) ⊓ subspaceStabilizer ρ E
  have hTP : (T : Subgroup G) ≤ P := le_inf le_sup_right hT
  let S := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let J := (P.subgroupOf B).map e.toMonoidHom
  have hSJ : (S : Subgroup _) ≤ J := by
    change (R : Subgroup B).map e.toMonoidHom ≤ J
    exact map_mono (hR ▸ comap_mono hTP)
  have hJ : J ≤ subspaceStabilizer (BinaryPermutation.naturalRepresentation (Fin 6)) (E.map p) := by
    apply le_subspaceStabilizer
    rintro _ ⟨b, hb, rfl⟩ _ ⟨u, hu, rfl⟩
    refine ⟨ρ b.val u, (hb.2 u).mpr hu, hp b u⟩
  have hi := six_plane_index S J hSJ (E.map p) hdim hJ
  change ((R : Subgroup B).map e.toMonoidHom).relIndex
    ((P.subgroupOf B).map e.toMonoidHom) ≤ 3 at hi
  rw [relIndex_map_map_of_injective _ _ e.injective, hR] at hi
  rw [supplement_index B (T : Subgroup G) P hn hTP inf_le_left]
  exact hi

open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) {K : Subgroup G}
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The six-letter model bounds the stabilizer in the original K*T*.
Only the genuine central quotient is identified with the natural module. -/
theorem symmetric_six_index_bound
    (s : Selected D K)
    (_proper : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (S : Subrepresentation
      ((Action.starRepresentation D h).comp (localStar D).subtype))
    [Representation.IsIrreducible S.toRepresentation]
    (hS : S.toSubmodule = Action.seedSpace D)
    (hdim : Module.finrank (ZMod 2) (Action.seedSpace D) = 2)
    (hcomm : Action.seedSpace D = subspaceCommutator (Action.starRepresentation D h)
      (Action.seedSpace D) (starImage D.H D.L₁))
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      Equiv.Perm (Fin 6))
    (eV : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (heV : ∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ u, centralProjection D h eV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e b) (centralProjection D h eV u)) :
    (starImage D.H D.T).relIndex (markedParabolic D h K) ≤ 3 := by
  have hn := normal_in_H s h hSQ hLK hm
  let : (starImage D.H K).Normal := hn.map (QuotientGroup.mk' (pCore 2 D.H))
    (QuotientGroup.mk'_surjective _)
  have hdis : Disjoint (Action.seedSpace D)
      (fixedSpace (Action.starRepresentation D h) (starImage D.H K)) := by
    rw [← hS]
    apply irreducible_commutator_disjoint_fixedSpace (Action.starRepresentation D h)
      (starImage D.H K) (starImage D.H D.L₁) (localStar D) S
    · exact le_normalizer_of_normal
    · exact map_mono (comap_mono hLK)
    · simpa only [hS] using hcomm
  have hdim' : Module.finrank (ZMod 2)
      ((Action.seedSpace D).map (centralProjection D h eV)) = 2 := by
    rw [image_plane_dimension _ _ (by rwa [centralProjection_ker]), hdim]
  have hVT : starImage D.H D.V ≤ (starSylow D h : Subgroup (Hstar D.H)) :=
    map_mono (comap_mono h.V_le_T)
  have hVB : starImage D.H D.V ≤ normalizer (starImage D.H K : Set (Hstar D.H)) :=
    le_normalizer_of_normal
  obtain ⟨R, hR⟩ := Sylow.exists_subgroupOf_sup_of_normalized (starSylow D h)
    (starImage D.H K) (starImage D.H D.V) hVT hVB
    ((starSylow D h).exists_subgroupOf_eq_of_normal _)
  have hTV : starImage D.H D.T ≤ normalizer (starImage D.H D.V : Set (Hstar D.H)) := by
    have hv : (D.T : Subgroup G).subgroupOf D.H ≤
        normalizer (D.V.subgroupOf D.H : Set D.H) := by
      rw [← subgroupOf_normalizer_eq h.V_le_H]
      exact comap_mono h.T_normalizes_V
    exact (map_mono hv).trans (le_normalizer_map _)
  have hTB : (starSylow D h : Subgroup (Hstar D.H)) ≤
      normalizer ((starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) : Set _) :=
    (le_inf le_normalizer_of_normal hTV).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have heq : (starImage D.H K ⊔ starImage D.H D.V) ⊔
      (starSylow D h : Subgroup (Hstar D.H)) =
      starImage D.H K ⊔ starImage D.H D.T := by
    rw [sup_assoc, sup_of_le_right hVT]
    rfl
  have hi := six_supplement_index (Action.starRepresentation D h)
    (starImage D.H K ⊔ starImage D.H D.V) (starSylow D h) hTB R hR e
    (centralProjection D h eV) heV (Action.seedSpace D) hdim'
    (le_sup_right.trans (localStar_stabilizes_seed D h))
  rw [heq] at hi
  exact hi

/-- Exact index, original local product, and literal embedded two-residual
for the S₆ source case. -/
theorem symmetric_six_marked_parabolic
    (s : Selected D K)
    (_proper : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (S : Subrepresentation
      ((Action.starRepresentation D h).comp (localStar D).subtype))
    [Representation.IsIrreducible S.toRepresentation]
    (hS : S.toSubmodule = Action.seedSpace D)
    (hdim : Module.finrank (ZMod 2) (Action.seedSpace D) = 2)
    (hcomm : Action.seedSpace D = subspaceCommutator (Action.starRepresentation D h)
      (Action.seedSpace D) (starImage D.H D.L₁))
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      Equiv.Perm (Fin 6))
    (eV : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (heV : ∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ u, centralProjection D h eV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e b) (centralProjection D h eV u)) :
    (starImage D.H D.T).relIndex (markedParabolic D h K) = 3 ∧
      localStar D = markedParabolic D h K ∧
      (pResidual 2 (markedParabolic D h K)).map
        (markedParabolic D h K).subtype = starImage D.H D.L₁ := by
  apply marked_parabolic_of_index_bound D h hLK hm
  exact symmetric_six_index_bound D h s _proper hSQ hLK hm S hS hdim hcomm e eV heV

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
