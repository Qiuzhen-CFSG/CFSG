module
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosure
public import CFSG.Quasithin.Chapter10.SourceA5HallGeneration
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction

/-!
# The original small weak-closure offender in the A5 branch

The source H-star group has positive attained generation parameter. Its actual
odd Hall subgroup, when placed in the original L₀T as in the preceding Hall
argument, supplies n(H)≤2. Element-centralizer containment from 10.2.9(1)
forces r≥4, so E.3.35 gives w≤n(H)≤2. The attained weak-closure theorem then
selects the literal offender V^g∩M, with corank at most two.

The final source configuration retains the original pair V=[V,L]·[V,L]^t,
the escaping conjugator g, and failure of L₀≤M^g. It supplies the input to
the remaining 10.2.12 module argument. The original element-centralizer bound
and Hall placement remain explicit earlier-source premises; neither the
lower bound on w nor Corollary10.2.13 is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
10.2.3, 10.2.9, and the opening of 10.2.12–13, printed pp.744–755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- Actual H-star attainment removes the extra positivity premise from the generation comparison. -/
theorem source_a5_hstar_globalW_le_generation
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hbound : generationParameter H ≤ 2) :
    globalW D.fullModule (T : Subgroup G) ≤ (generationParameter H : ℕ∞) :=
  source_a5_globalW_le_generation_of_element_centralizers D e hcent hH.1.1.2 hH.1.2
    (source_hstar_generation_positive D hH) hbound

/-- Original element-centralizer control and Hall placement give the required weak-closure upper bound. -/
theorem source_a5_globalW_le_two_of_hall_placement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) : globalW D.fullModule (T : Subgroup G) ≤ 2 := by
  have hb := source_a5_hstar_generation_bound_of_hall_placement D e hn hH B hBM hHall hBJ
  exact (source_a5_hstar_globalW_le_generation D e hcent hH hb).trans (by exact_mod_cast hb)

/-- The upper bound is attained by the literal relative normalizer V^g ∩ M. -/
theorem source_a5_small_offender_of_hall_placement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) :
    ∃ g : G, ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      globalW D.fullModule (T : Subgroup G) =
        (subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
          (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) : ℕ∞) ∧
      subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
        (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  have hw := source_a5_globalW_le_two_of_hall_placement D e hn hcent hH B hBM hHall hBJ
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top
    (source_fullModule_weakClosure_hypotheses D) (ne_top_of_le_ne_top (by simp) hw)
  have he := hg.2
  unfold offenderNormalizer at he
  rw [source_fullModule_normalizer D] at he
  exact ⟨g,hg.1,he,by exact_mod_cast (he ▸ hw)⟩

/-- Original10.2.12 starts with this actual pair and small escaping offender. -/
theorem source_a5_small_offender_configuration
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      D.fullModule = ⁅D.fullModule,L⁆ ⊔
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ∧
      ∃ g ∉ D.maximalLocal,
        ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
        subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
          (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2 ∧
        ¬ localOrbit T L ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨t,ht,htn,_,hpair,_⟩ := source_nonnormal_fullModule_pair D hn
  obtain ⟨g,hcomm,_,hsmall⟩ := source_a5_small_offender_of_hall_placement D e hn hcent hH B hBM hHall hBJ
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  have hg : g ∉ D.maximalLocal := by
    intro hgm
    apply hcomm
    have he : D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hgm)
    rw [he]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer _)
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact ⟨t,ht,htn,hpair,g,hg,hcomm,hsmall,
    fun hc => hg ((source_nonnormal_orbit_le_conjugate_maximal_iff D hn hd g).mp hc)⟩

end CFSG.Quasithin.Chapter10
