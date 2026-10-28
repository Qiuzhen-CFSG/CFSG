module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.AlphaTransport
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaGeometry.Original
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.LinearSelection
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleAlphaCard
/-!
# The actual HStar selected field orders

The original A5 natural source gives the common Thompson alpha order sixteen.
Vanishing of the H-fixed omega-center kills the intrinsic Sylow residual
centralizer. The single source then gives alpha order q and the exchanged
pair gives q squared. Thus the same selected HStar fields have orders sixteen
and four respectively; no identification with the generation parameter is used.
All quotient maps and marked sections remain those of the original H orbit.

Source: Aschbacher--Smith E.2.3 and 10.2.3(4), printed pp.216--217 and746.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false
variable {H : Subgroup G}
variable {F : Type*} [Field F] [CharP F 2]
local instance hstarAlphaFieldsAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4)
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))

include e hn hH hZH hF f n

/-- The actual selected H* pair has field order four, from the common original alpha. -/
theorem source_hstar_paired_field_card
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D hH).normal
    letI := (source_hstar_omega_orbit_reduced D hH).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (d : SourceTwoFactorCase (α.comp Y.subtype)) (K : BinaryField)
      (_c : d.MarkedProduct (linearNatural K 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H ⧸ C)).toMonoidHom = d.first),
      Nat.card K.Carrier = 4 := by
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hP := source_a5_hstar_minimal_parabolic D e hn hH
  have hJ := source_hstar_thompson_moves_omega_orbit_of_natural_four D e hn hH hZH hF f n
  have hzS := RankOneBaumann.sylow_subtype_residual_centralizer_eq_bot_of_omega hH.1.1.2 hzH
  have hcard16 : Nat.card (thompsonAlpha (S : Subgroup H)) = 16 :=
    (RankOneBaumann.alpha_card_subtype hH.1.1.2).trans
      (source_original_alpha_card_of_hstar_natural_four D e hn hH hZH hF f n hz)
  dsimp only
  intro d K c hexchange
  have hcard := RankOneBaumann.PairedFactorOrbit.source_alpha_card_of_trivial_sylow_residual_centralizer
    S hP U hU hJ q hq hk d K c hexchange hzS
  rw [hcard16] at hcard
  nlinarith

/-- The actual selected single H* source has field order sixteen. -/
theorem source_hstar_single_field_card
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D hH).normal
    letI := (source_hstar_omega_orbit_reduced D hH).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hqs : IsQuasisimple (generalizedFitting Y))
      (s : MovedSection (α.comp Y.subtype) (generalizedFitting Y)) (K : BinaryField)
      (_hnatural : IsLinearNatural (s.action.comp (generalizedFitting Y).subtype) K 2),
      Nat.card K.Carrier = 16 := by
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hP := source_a5_hstar_minimal_parabolic D e hn hH
  have hJ := source_hstar_thompson_moves_omega_orbit_of_natural_four D e hn hH hZH hF f n
  have hzS := RankOneBaumann.sylow_subtype_residual_centralizer_eq_bot_of_omega hH.1.1.2 hzH
  have hcard16 : Nat.card (thompsonAlpha (S : Subgroup H)) = 16 :=
    (RankOneBaumann.alpha_card_subtype hH.1.1.2).trans
      (source_original_alpha_card_of_hstar_natural_four D e hn hH hZH hF f n hz)
  dsimp only
  intro hqs s K hnatural
  have hcard := quasisimple_linear_alpha_card_of_trivial_sylow_residual_centralizer
    S hP U hU hJ q hq hk hqs s K hnatural hzS
  exact hcard.symm.trans hcard16

/-- The original selected alternatives with their field orders discharged. -/
theorem source_hstar_linear_field_alternatives
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H)) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D hH).normal
    letI := (source_hstar_omega_orbit_reduced D hH).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    let σ := α.comp Y.subtype
    letI := offenderSubgroup_normal α
    (IsQuasisimple (generalizedFitting Y) ∧
      ∃ c : ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        ∃ K : BinaryField, Nat.card K.Carrier = 16 ∧ IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) K 2) ∨
      ∃ (d : SourceTwoFactorCase σ) (K : BinaryField),
        Nat.card K.Carrier = 4 ∧ Nonempty (d.MarkedProduct (linearNatural K 2)) ∧
        ∃ t : S.mapSurjective hq,
          d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
          d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  let := hU.elementary
  rcases source_hstar_linear_alternatives_of_seed_centralizer D e hn hH hZH hF f n hlarge hCZ with
    ⟨hqs,c,K,hlinear⟩ | ⟨d,K,⟨c⟩,hexchange⟩
  · exact Or.inl ⟨hqs,c,K,
      source_hstar_single_field_card D e hn hH hZH hF f n hz hzH hqs c.sectionData K hlinear,
      hlinear⟩
  · exact Or.inr ⟨d,K,
      source_hstar_paired_field_card D e hn hH hZH hF f n hz hzH d K c hexchange,
      ⟨c⟩,hexchange⟩

end CFSG.Quasithin.Chapter10
