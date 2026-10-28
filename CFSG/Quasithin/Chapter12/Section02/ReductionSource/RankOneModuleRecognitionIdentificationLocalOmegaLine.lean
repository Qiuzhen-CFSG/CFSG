module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalOmegaLine
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalCentralOmega

/-!
# The source 6.2.2 conclusions on the whole reduced layer

The original H-star centralization of 6.1.5, together with an outside
H-star member, supplies omega-centralizer escape. B.2.14 places that omega
subgroup in the whole reduced subgroup. The central omega line, its order,
its escaping involution centralizer and the marked S₅ quotient then follow
on the literal Chapter 12 subgroups.

The 6.1.5 input remains with qt-d-1222-rankone-recognition-natural.
The complete local-analysis assembly remains with
qt-d-1222-recognition-local-analysis; this theorem does not supply the
order-eight core intersection of 6.2.11.
Source: Aschbacher--Smith, 6.2.2, printed p.680, applied to R₂(LT)
in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}

/-- The central omega field on the literal whole reduced subgroup, from 6.1.5's escape. -/
theorem source_local_centralOmega_eq_zpowers_of_escape
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hescape : ¬ centralizer (centralOmega (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralOmega (T : Subgroup G) = zpowers z :=
  local_centralOmega_eq_zpowers_of_escape h611 hnatural
    (source_local_centralOmega_le_wholeReduced h611) hescape hz ho hT

/-- All clauses of 6.2.2 from the original H-star centralization of 6.1.5.
The natural-reduction owner must supply this earlier-source premise. -/
theorem source_local_omega_geometry_of_hstar_centralization
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hcentral : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ∃ z ∈ ZS (T : Subgroup G) L (wholeReduced T L), orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      centralOmega (T : Subgroup G) = zpowers z ∧
      Nat.card (centralOmega (T : Subgroup G)) = 2 ∧
      (¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) ∧
      (let H := L ⊔ (T : Subgroup G)
       ∃ e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5),
         (L.subgroupOf H).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))) =
           alternatingGroup (Fin 5)) := by
  have he : centralOmega (T : Subgroup G) =
      Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    rw [centralOmega, ← map_center_subtype_eq_inf_centralizer,
      ← omegaCenterIn_eq_omegaOneAmbient]
    rfl
  have hescape : ¬ centralizer (centralOmega (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := by
    obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
    rw [he]
    exact fun hc => hH.1.2 ((hcentral H hH).trans hc)
  obtain ⟨z, hz, ho, hT⟩ := exists_central_involution_in_ZS h611
  have hline := source_local_centralOmega_eq_zpowers_of_escape h611 hnatural hescape hz ho hT
  have hCZ : centralizer ({z} : Set G) =
      centralizer (centralOmega (T : Subgroup G) : Set G) := by
    rw [hline]
    apply le_antisymm
    · apply le_centralizer_iff.mp
      apply zpowers_le.mpr
      intro t ht
      exact mem_centralizer_singleton_iff.mp ht
    · exact centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers z))
  exact ⟨z, hz, ho, hT, hline, by rw [hline, Nat.card_zpowers, ho],
    fun hc => hescape (hCZ.symm ▸ hc),
    local_marked_symmetricFive_of_omega_line h611 hnatural ho hline⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
