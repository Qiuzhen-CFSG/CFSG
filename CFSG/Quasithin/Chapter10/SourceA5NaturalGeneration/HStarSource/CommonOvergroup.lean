module
public import CFSG.Quasithin.Chapter3.Section01.HStarResidualNormalizer
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.LinearSelection
/-!
# The actual H-star natural source has a common local overgroup

Both genuine single and paired natural rows make the common Baumann subgroup
Sylow in its join with the H-star residual. Transporting the literal Sylow
inclusion to G permits the proved common-normal theorem to place H and the
full Baumann normalizer in a maximal two-local subgroup. No block structure,
field-size identification, full-core recovery or overcomponent-normalizer
hypothesis is needed.

Source: Aschbacher–Smith 10.2.2(4), printed p.744, using E.2.3 and3.1.1.
-/
public noncomputable section
open Subgroup

open Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.RankOneBaumann.PairedFactorOrbit
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
  (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
  {F : Type*} [Field F] [CharP F 2]
local instance normalizerSourceAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable (hF : Nat.card F=4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
  (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
  (hlarge : 1 < generationParameter H)
  (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
include D e hn hH hZH hF f n hlarge hCZ
set_option backward.isDefEq.respectTransparency false in
theorem source_hstar_baumann_sylow_of_seed_centralizer :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      ((pResidual 2 H).map H.subtype ⊔ baumann (T : Subgroup G)) := by
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
  let := offenderSubgroup_normal α
  have hP := source_a5_hstar_minimal_parabolic D e hn hH
  have hJ := source_hstar_thompson_moves_omega_orbit_of_natural_four D e hn hH hZH hF f n
  have hs : Chapter1.IsSylowIn 2 (baumann (S : Subgroup H))
      (pResidual 2 H ⊔ baumann (S : Subgroup H)) := by
    rcases source_hstar_linear_alternatives_of_seed_centralizer D e hn hH hZH hF f n hlarge hCZ with
      ⟨hqs,c,K,hlinear⟩ | ⟨d,K,⟨c⟩,hexchange⟩
    · exact (quasisimple_linear_baumann_of_section S hP U hU hJ q hq hk
        hqs c.sectionData K hlinear).1
    · exact (source_global_baumann_and_alpha S hP U hU hJ q hq hk d K c hexchange).1
  have hm := Chapter1.Section02.IndexTwo.isSylowIn_map hs H.subtype
  have hSm : (S : Subgroup H).map H.subtype=(T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hBm := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
  change (baumann (S : Subgroup H)).map H.subtype=baumann ((S : Subgroup H).map H.subtype) at hBm
  rw [hSm] at hBm
  rwa [Subgroup.map_sup,hBm] at hm

theorem source_hstar_baumann_normalizer_common_overgroup :
    ∃ M₁ : Subgroup G, IsMaximalTwoLocal M₁ ∧
      normalizer (baumann (T : Subgroup G) : Set G) ⊔ H ≤ M₁ := by
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZB : omegaOneCenterAmbient (T : Subgroup G) ≤ baumann (T : Subgroup G) := by
    intro z hz
    refine ⟨hZT hz,?_⟩
    intro a ha
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 a
      ((sSup_le (fun _ hA => hA.1) : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G))
        ((mem_omegaOneCenterAmbient_iff _ _).mp ha).1))
  have hB : baumann (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hz := bot_unique (hZB.trans he.le)
    rw [hz,commutator_bot_left] at hZH
    exact hZH rfl
  exact Chapter3.HStar.normalizer_residual_sylow_common_overgroup D.simpleQTKE T
    (le_normalizer_componentOrbit L T) hH (baumann (T : Subgroup G)) hB inf_le_left
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _))
    (source_hstar_baumann_sylow_of_seed_centralizer D e hn hH hZH hF f n hlarge hCZ)
end CFSG.Quasithin.Chapter10
