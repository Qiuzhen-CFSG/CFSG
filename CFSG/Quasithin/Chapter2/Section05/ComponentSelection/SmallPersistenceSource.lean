module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.SmallModels
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CentralCoreInvolutionSource
/-!
# The actual small component in the central-core involution centralizer

For every original involution t in O₂(H)∩Z(S), apply source persistence
to its cyclic subgroup. Its normalizer is exactly C_G(t), with the
original Sylow. The small A.3.18 theorem then proves relative normality
and identifies the original ambient K with the embedded prime-to-three
residual of this exact centralizer. No component-in-centralizer or
residual identity is assumed.
Source: Aschbacher–Smith 2.5.6 and 2.5.15, printed pp.554,558.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.small_component_centralizer_residual
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H=K⊔(S : Subgroup H).map H.subtype)
    (hm : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (t : G) (ht : orderOf t=2) (htC : t∈twoCore H)
    (htZ : t∈centerIn ((S : Subgroup H).map H.subtype)) :
    IsComponentIn K (centralizer ({t} : Set G)) ∧
      (K.subgroupOf (centralizer ({t} : Set G))).Normal ∧
      K=(primeToResidual 3 (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype := by
  let Y := (S : Subgroup H).map H.subtype
  let E := zpowers t
  have ht1 : t≠1 := by intro he; rw [he,orderOf_one] at ht; omega
  have hE : E≠⊥ := by intro he; exact ht1 (mem_bot.mp (he ▸ mem_zpowers t))
  have htK : t∈centralizer (K : Set G) := by
    have hc := generated_orbit_core ⟨c.component_le,c.component⟩ S hgen
    rw [←hc] at htC
    exact (centralizer_le (le_componentOrbit K Y)) htC.2
  have hEC : E≤Y⊓centralizer (K : Set G) := zpowers_le.mpr ⟨htZ.1,htK⟩
  have hYE : Y≤normalizer (E : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_order_two t ht]
    exact fun a ha => mem_centralizer_singleton_iff.mpr (htZ.2 a ha)
  have hKJ := SmallPersistence.component_in_normalizer_of_small_model hG
    c.T c.maximal c.sylow_le c.unique hempty (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le,c.component⟩ hgen hm hE hEC hYE
  rw [normalizer_zpowers_eq_centralizer_of_order_two t ht] at hKJ
  have hJ : IsSQTK KnownSimple.IsKnownSimple (centralizer ({t} : Set G)) := by
    apply hG.twoLocal_sqtk
    refine ⟨E,hE,?_,(normalizer_zpowers_eq_centralizer_of_order_two t ht).symm⟩
    exact (S.isPGroup'.map H.subtype).to_le (hEC.trans inf_le_left)
  let e := subgroupOfEquivOfLe hKJ.1
  have hm' : Nonempty (K.subgroupOf (centralizer ({t} : Set G)) ≃* Matrix.PSL3Three.PSL) ∨
      Nonempty (K.subgroupOf (centralizer ({t} : Set G)) ≃* Sporadic.Mathieu.M11) :=
    hm.imp (fun ⟨a⟩ => ⟨e.trans a⟩) (fun ⟨a⟩ => ⟨e.trans a⟩)
  obtain ⟨hn,he⟩ := ChapterA.Section03.OddPrime.SourceModels.SmallComponents.component_eq_cubic_residual
    hJ hKJ.2 hm'
  refine ⟨hKJ,hn,?_⟩
  have hh := congrArg (Subgroup.map (centralizer ({t} : Set G)).subtype) he
  simpa only [map_subgroupOf_eq_of_le hKJ.1] using hh
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
