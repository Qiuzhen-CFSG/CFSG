module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.SixGeneration

/-!
# The marked alternating-four residual in the six-letter case

The actual component coordinates put the local residual inside A₆. Its
normalized Sylow and the projected original seed plane identify its image
with the two-residual of the syntheme stabilizer. The component equivalence
remembers its inclusion in the supplied S₆ actor, so the marking can be used
for cubic fixed-index and chief-factor calculations on the original group.
Source: Aschbacher–Smith 13.5.21 and 13.5.24, printed pp.924–925.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource
open Recognition Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
open Section08.Source
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]


theorem symmetric_six_residual_marking {K : Subgroup G}
    (s : Selected D K)
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
    ∃ c : starImage D.H K ≃* alternatingGroup (Fin 6),
      (∀ k, (c k).val = e ⟨k.val, mem_sup_left k.property⟩) ∧
      ∃ g : alternatingGroup (Fin 6),
        ((starImage D.H D.L₁).subgroupOf (starImage D.H K)).map c.toMonoidHom =
          ((pResidual 2 AlternatingAction.parabolic).map
            AlternatingAction.parabolic.subtype).map (MulAut.conj g).toMonoidHom := by
  let ρ : Representation (ZMod 2) (Hstar D.H) (Action.Space D) := Action.starRepresentation D h
  let C := starImage D.H K
  let L := starImage D.H D.L₁
  let B := C ⊔ starImage D.H D.V
  have hCB : C ≤ B := le_sup_left
  let p := centralProjection D h eV
  have hLC : L ≤ C := map_mono (comap_mono hLK)
  have hn := normal_in_H s h hSQ hLK hm
  let : C.Normal := hn.map (QuotientGroup.mk' (pCore 2 D.H))
    (QuotientGroup.mk'_surjective _)
  have hmark := symmetric_six_component_marking D s hn e
  let c : C ≃* alternatingGroup (Fin 6) :=
    ((subgroupOfEquivOfLe (show C ≤ B from le_sup_left)).symm.trans
      (e.subgroupMap (C.subgroupOf B))).trans (MulEquiv.subgroupCongr hmark)
  have hc (k : C) : (c k).val = e ⟨k.val, hCB k.property⟩ := rfl
  let a : alternatingGroup (Fin 6) →* Hstar D.H := C.subtype.comp c.symm.toMonoidHom
  have hac : a.comp c.toMonoidHom = C.subtype := by
    ext k
    exact congrArg Subtype.val (c.symm_apply_apply k)
  have hae (g : alternatingGroup (Fin 6)) :
      e ⟨a g, hCB (c.symm g).property⟩ = g.val :=
    (hc (c.symm g)).symm.trans (congrArg Subtype.val (c.apply_symm_apply g))
  have hp (g : alternatingGroup (Fin 6)) (u : Action.Space D) :
      p (ρ (a g) u) = BinaryPermutation.alternatingNaturalRepresentation (Fin 6) g (p u) := by
    change p (ρ (a g) u) = BinaryPermutation.naturalRepresentation (Fin 6) g.val (p u)
    rw [← hae g]
    exact heV ⟨a g, hCB (c.symm g).property⟩ u
  have hdis : Disjoint (Action.seedSpace D) (fixedSpace ρ C) := by
    rw [← hS]
    apply irreducible_commutator_disjoint_fixedSpace ρ C L (localStar D) S
    · exact le_normalizer_of_normal
    · exact hLC
    · simpa only [hS] using hcomm
  let E := (Action.seedSpace D).map p
  have hdimE : Module.finrank (ZMod 2) E = 2 := by
    rw [image_plane_dimension _ _ (by rwa [centralProjection_ker]), hdim]
  obtain ⟨R, hR⟩ := (starSylow D h).exists_subgroupOf_eq_of_normal C
  let R' := R.mapSurjective (f := c.toMonoidHom) c.surjective
  let J := (L.subgroupOf C).map c.toMonoidHom
  have hJa : J.map a = L := by
    rw [map_map, hac, map_subgroupOf_eq_of_le hLC]
  have hRa : (R' : Subgroup (alternatingGroup (Fin 6))).map a ≤ starImage D.H D.T := by
    change ((R : Subgroup C).map c.toMonoidHom).map a ≤ _
    rw [map_map, hac, hR, subgroupOf_map_subtype]
    exact inf_le_left
  have hJ : IsPPerfect 2 J := by
    have hl := (localStar_residual_twoPerfect D h).of_surjective
      (subgroupOfEquivOfLe hLC).symm.toMonoidHom (subgroupOfEquivOfLe hLC).symm.surjective
    exact hl.of_surjective (c.toMonoidHom.subgroupMap (L.subgroupOf C))
      (c.toMonoidHom.subgroupMap_surjective _)
  have hJne : J ≠ ⊥ := by
    intro hz
    have hzL : L = ⊥ := by rw [← hJa, hz, Subgroup.map_bot]
    exact hm (by change ⁅C, L⁆ = ⊥; rw [hzL, commutator_bot_right])
  have hRn : (R : Subgroup C) ≤ normalizer (L.subgroupOf C : Set C) := by
    rw [hR, ← subgroupOf_normalizer_eq hLC]
    exact comap_mono (starSylow_normalizes_local D h)
  have hR'n : (R' : Subgroup (alternatingGroup (Fin 6))) ≤ normalizer
      (J : Set (alternatingGroup (Fin 6))) :=
    (map_mono hRn).trans (le_normalizer_map _)
  have hE : J ⊔ (R' : Subgroup (alternatingGroup (Fin 6))) ≤
      subspaceStabilizer (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) E := by
    have hlocal : (J ⊔ (R' : Subgroup (alternatingGroup (Fin 6)))).map a ≤ localStar D := by
      rw [Subgroup.map_sup, hJa]
      exact sup_le le_sup_left (hRa.trans le_sup_right)
    apply le_subspaceStabilizer
    rintro g hg _ ⟨u, hu, rfl⟩
    exact ⟨ρ (a g) u,
      (localStar_stabilizes_seed D h (hlocal (mem_map_of_mem a hg)) u).mpr hu, hp g u⟩
  exact ⟨c,hc,SixGeneration.residual_marking R' J hJ hJne hR'n E hdimE hE⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource
