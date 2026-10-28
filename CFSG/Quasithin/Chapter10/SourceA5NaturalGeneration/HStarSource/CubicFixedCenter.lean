module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.LinearSelection
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.CubicFixedCenter
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleCubicFixed
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection
/-!
# Actual H* cubic fixed-center equality

The genuine E.2.3 single or exchanged natural source is selected from the
literal orbit of the original Sylow omega-center. Its action kernel lies in
the Sylow subgroup because the Hall seed centralizer is exactly that Sylow.
Every actual cubic therefore has nontrivial natural action. The single moved
section and paired exchanger calculations give residual-fixed points; the
Sylow supplement makes them precisely H-fixed points. The final theorem
transports this equality through the actual H inclusion into the original G.
No field-size, chosen-component membership, or independent quotient matching
is assumed of the cubic element.

Source: Aschbacher--Smith E.2.3 and 10.2.3(4), pp.216--217 and746.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

variable {F : Type*} [Field F] [CharP F 2]
local instance hstarCubicFixedFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
include e hn hH hZH hF f n


set_option backward.isDefEq.respectTransparency false in
theorem source_hstar_intrinsic_cubic_fixed_center
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (b : H) (hb : orderOf b=3) :
    omegaOneCenterAmbient (T.subtype hH.1.1.2 : Subgroup H) ⊓ centralizer ({b} : Set H) =
      omegaOneCenterAmbient (T.subtype hH.1.1.2 : Subgroup H) ⊓ centralizer (⊤ : Subgroup H) := by
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
  have hZU : omegaOneCenterAmbient (S : Subgroup H) ≤ U := by
    rw [show U = normalClosure (omegaOneCenterAmbient (S : Subgroup H) : Set H) from
      source_hstar_omega_orbit_eq_normalClosure D hH]
    exact subset_normalClosure
  have hbR : b ∈ pResidual 2 H := mem_pResidual_of_orderOf_coprime (by rw [hb]; decide)
  let bR : pResidual 2 H := ⟨b,hbR⟩
  have hbR3 : bR^3=1 := by
    apply Subtype.ext
    change b^3=1
    simpa [hb] using pow_orderOf_eq_one b
  have hmove : b ∉ centralizer (U : Set H) := by
    intro hc
    have hbS : b ∈ (S : Subgroup H) := hCZ.le
      ((centralizer_le (subgroupOf_mono H (le_conjugateSpanBy _ _))) hc)
    have hh := S.isPGroup'.orderOf_coprime (by decide : Nat.Coprime 2 3) ⟨b,hbS⟩
    have ho : orderOf (⟨b,hbS⟩ : (S : Subgroup H))=3 := by
      rw [← orderOf_injective (S : Subgroup H).subtype (S : Subgroup H).subtype_injective]
      exact hb
    rw [ho] at hh
    norm_num at hh
  have heq : omegaOneCenterAmbient (S : Subgroup H) ⊓ centralizer ({b} : Set H) =
      omegaOneCenterAmbient (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H) := by
    rcases source_hstar_linear_alternatives_of_seed_centralizer D e hn hH hZH hF f n hlarge hCZ with
      ⟨hqs,c,K,hlinear⟩ | ⟨d,K,⟨c⟩,hexchange⟩
    · have hZa : omegaOneCenterAmbient (S : Subgroup H) ≤ thompsonAlpha (S : Subgroup H) :=
        omegaCenter_le_omegaCenter_maxJ (S : Subgroup H)
      have ha := (source_hstar_alpha_and_span_of_natural_four D e hn hH hZH hF f n).1
      exact quasisimple_linear_cubic_fixed_center S hP U hU hJ q hq hk hqs
        c.sectionData K hlinear (omegaOneCenterAmbient (S : Subgroup H))
        (hZa.trans (ha.le.trans (sup_le_sup inf_le_left inf_le_right))) bR hbR3 hmove
    · exact paired_source_cubic_fixed_center S hP U hU hJ q hq hk d K c hexchange hZU bR hbR3 hmove
  rw [heq]
  apply le_antisymm
  · intro z hz
    refine ⟨hz.1,?_⟩
    have hR : pResidual 2 H ≤ centralizer ({z} : Set H) := by
      intro r hr x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact (hz.2 r hr).symm
    have hS : (S : Subgroup H) ≤ centralizer ({z} : Set H) := by
      intro t ht x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 t ht).symm
    have htop : (⊤ : Subgroup H) ≤ centralizer ({z} : Set H) := by
      rw [←pResidual_sup_sylow_eq_top S]
      exact sup_le hR hS
    intro x hx
    exact (htop hx z (Set.mem_singleton _)).symm
  · exact inf_le_inf_left _ (centralizer_le le_top)


/-- Every actual cubic in H* has precisely the H*-fixed original omega-center. -/
theorem source_hstar_cubic_fixed_center
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (b : H) (hb : orderOf b=3) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b:G)} : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) := by
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hz : omegaOneCenterAmbient (T.subtype hH.1.1.2 : Subgroup H) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (hZT.trans hH.1.1.2)]
    congr 1
    exact map_subgroupOf_eq_of_le hH.1.1.2
  have he := source_hstar_intrinsic_cubic_fixed_center D e hn hH hZH hF f n hlarge hCZ b hb
  rw [hz] at he
  apply le_antisymm
  · intro z hzin
    let zH : H := ⟨z,hH.1.1.2 (hZT hzin.1)⟩
    have hzH : zH ∈ (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H ⊓
        centralizer ({b} : Set H) := by
      refine ⟨hzin.1,?_⟩
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact Subtype.ext (hzin.2 b (Set.mem_singleton _))
    have hfixed := (he.le hzH).2
    refine ⟨hzin.1,?_⟩
    intro x hx
    exact congrArg H.subtype (hfixed ⟨x,hx⟩ (mem_top _))
  · intro z hz
    exact ⟨hz.1,fun x hx => Set.mem_singleton_iff.mp hx ▸ hz.2 b b.property⟩

end CFSG.Quasithin.Chapter10
