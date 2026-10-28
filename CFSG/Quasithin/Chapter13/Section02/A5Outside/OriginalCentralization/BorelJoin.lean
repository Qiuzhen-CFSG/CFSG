module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Omega
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.FactorFixedSpaces

/-!
# The original Borel-join reductions with Borel centrality discharged

The earlier omega splitting shows that the literal O²(N_L(T∩L))
centralizes Ω₁Z(T). Consequently the contrary core-free join in 13.2.12
has center-free H. This supplies the center hypothesis to the existing
paired quotient, plane, and original factor-line constructions.

The independent Baumann normalizer bound and solvability of H remain
explicit here. Their proof and the eventual core-free-join contradiction
remain with the original outside-centralization assembly, qt-d-1367-assembly;
these reductions do not assert 13.2.7 or 13.2.12.

Source: Aschbacher--Smith 13.2.11--12, printed pp.881--882.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The contrary core-free join forces Z(H)=1 without an additional
Borel-centrality hypothesis. -/
theorem center_eq_bot_of_borel_join_core_eq_bot
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) : center H = ⊥ :=
  source_center_eq_bot_of_borel_join_core_eq_bot d hH
    (borelResidual_centralizes_omega_of_omega_movement d hH hZ) hcore

/-- The original omega line, Thompson plane, two residual centralizers
and Baumann plane stabilizer for the actual contrary join. -/
theorem coreFree_borel_join_geometry
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    center H = ⊥ ∧
      omegaOneCenterAmbient (T : Subgroup G) = V₁ ∧
      ChapterB.thompsonAlpha (T : Subgroup G) = V₂ ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      (T : Subgroup G) ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) = ⊥ ∧
      ChapterB.baumann (T : Subgroup G) = (T : Subgroup G) ⊓ centralizer (V₂ : Set G) ∧
      omegaOrbit T H = ⁅omegaOrbit T H, H⁆ := by
  have hz := center_eq_bot_of_borel_join_core_eq_bot d hH hZ hcore
  exact ⟨hz, source_omegaCenter_eq_flag_line d hH hB hZ hs hz,
    source_alpha_eq_flag_plane d hH hB hZ hs hz,
    source_local_sylow_centralizer_eq_bot d hH hB hZ hs hz,
    source_residual_sylow_centralizer_eq_bot T H hH.1.1.2 hz,
    source_baumann_eq_flag_plane_centralizer d hH hB hZ hs hz,
    source_centerfree_omegaOrbit_eq_commutator d hH hB hZ hs hz⟩

/-- The literal two-core quotients are the paired symmetric-three model
and its elementary cubic residual. -/
theorem coreFree_borel_join_paired_models
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) ∧
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
        Multiplicative (Fin 2 → ZMod 3)) :=
  source_centerfree_residual_core_quotient_models d hH hB hZ hs
    (center_eq_bot_of_borel_join_core_eq_bot d hH hZ hcore)

/-- The actual E.2.3 factors have the original two distinct fixed lines,
with their literal normalizers and point centralizers in T. -/
theorem coreFree_borel_join_original_fixed_lines
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      c.count = 2 ∧
      (∀ i j, ∃ t : S, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) ∧
      let E := fun i => (⁅U, (c.factor i).comap q⁆ ⊓
        centralizer (ChapterB.baumann (S : Subgroup H) : Set H)).map H.subtype
      (∀ i, Nat.card (E i) = 2 ∧ E i ≤ V₂ ∧ Disjoint (E i) V₁) ∧
      (∀ i j, i ≠ j → Disjoint (E i) (E j) ∧ E i ⊔ E j = V₂ ∧
        ∀ a ∈ E i, a ≠ 1 → ∀ b ∈ E j, b ≠ 1 → zpowers (a * b) = V₁) ∧
      (∀ i, (T : Subgroup G) ⊓ normalizer (((c.factor i).comap q).map H.subtype : Set G) =
        ChapterB.baumann (T : Subgroup G)) ∧
      ∀ i a, a ∈ E i → a ≠ 1 →
        (T : Subgroup G) ⊓ centralizer ({a} : Set G) = ChapterB.baumann (T : Subgroup G) :=
  source_solvable_paired_original_fixed_lines d hH hB hZ hs
    (center_eq_bot_of_borel_join_core_eq_bot d hH hZ hcore)

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
