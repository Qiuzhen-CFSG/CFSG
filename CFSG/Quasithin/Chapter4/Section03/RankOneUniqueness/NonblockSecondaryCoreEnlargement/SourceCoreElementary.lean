module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameElementaryCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreParity

/-!
# SourceCoreElementary without strict core enlargement

These are the original core-action arguments with their literal subtype maps,
using only SecondaryActionData. No strict enlargement clause is supplied.
They feed recognition of the full component-core Frattini module.
Source: Aschbacher--Smith, original 4.3.2 and 4.3.11--16, pp.617--619.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
open Nonblock.RootCoordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}
namespace RootCoordinates
variable (m : RootCoordinates d)
  (s : SecondaryActionData c 2) (D : Chapter12.Section02.ChosenModule T L V)
  (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
  (hXr : X ≤ rootNormalizer c) (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
  (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
  (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)

omit [Finite G] in
include hXr in
private theorem component_extension_normal :
    ((s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X)).Normal := by
  let := s.normal
  apply normal_subgroupOf_of_le_normalizer
  have hh := s.component.le_normalizer_map (rootNormalizer c).subtype
  have hn : rootNormalizer c ≤ normalizer (s.component.map (rootNormalizer c).subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  exact (sup_le (map_subtype_le _) hXr).trans hn

include m D hX hXK hXr hfix hcomm e

/-- An irreducible section of an invariant elementary core subgroup has trivial component action. -/
theorem elementary_core_section_component_kernel
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (a : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ)
    [ρ.IsIrreducible] :
    (s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let H := M.subgroupOf E
  let : H.Normal := component_extension_normal s X hXr
  let : Finite W := Finite.of_surjective (fun x => (a.coordinates x).toAdd) a.onto
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  let f : H ≃* s.component := (subgroupOfEquivOfLe (show M ≤ E from le_sup_left)).trans
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).symm
  let eq : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Four.PSL :=
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  by_contra hnt
  have hc : ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype ≤ R₂ c := by
    change (s.component.pCoreIn 2).map (rootNormalizer c).subtype ≤ R₂ c
    rw [map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    exact s.component_core_le D
  have hd := d.elementary_section_card_le (by decide) A
    (hA.trans (hc.trans (radical_le_sylow c))) (fun x => (a.coordinates x).toAdd) a.onto
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hd
  have hdim : Module.finrank (ZMod 2) W ≤ 12 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hd
  have h9 := Representation.PSL3Four.normal_core_simple_degree H eq ρ hdim hnt
  apply (SourceActionEndgame.RootCoordinates.component_section_not_odd_degree m) s D X hX hXK hfix hcomm A B hA
    a.kernel_le a.normalized a.kernel_normalized (show Odd 9 by decide)
  rw [a.relIndex_eq_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h9]


/-- The component fixes every elementary source section, without assuming
that the whole extension action is irreducible. -/
theorem elementary_core_action_component_kernel
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (a : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ) :
    (s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let H := M.subgroupOf E
  let : Finite W := Finite.of_surjective (fun x => (a.coordinates x).toAdd) a.onto
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  by_contra hn
  let : Group.IsPerfect s.component := s.isComponent.perfect
  let f : H ≃* s.component := (subgroupOfEquivOfLe (show M ≤ E from le_sup_left)).trans
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).symm
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := f.symm.toMonoidHom) f.symm.surjective
  obtain ⟨P,N,hi,hnt⟩ :=
    Representation.QuadraticFourGroup.exists_irreducible_section_surviving_perfect (ρ := ρ) H hn
  let aa := a.invariantSection P
  let bb := aa.quotientSection N
  let : IsElementaryAbelian 2 (a.invariantPreimage P) :=
    IsElementaryAbelian.of_injective (inclusion (a.invariantPreimage_le P))
      (inclusion_injective (a.invariantPreimage_le P))
  let : N.quotientRepresentation.IsIrreducible := hi
  exact hnt ((SourceActionEndgame.RootCoordinates.elementary_core_section_component_kernel m) s D X hX hXK hXr hfix hcomm e
    _ _ ((a.invariantPreimage_le P).trans hA) N.quotientRepresentation bb)

/-- Every invariant elementary subgroup of the actual component core is central. -/
theorem elementary_core_centralizes_component
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    (hN : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G)) :
    s.component.map (rootNormalizer c).subtype ≤ centralizer (A : Set G) := by
  let M := s.component.map (rootNormalizer c).subtype
  let E := M ⊔ X
  let H := M.subgroupOf E
  have hAE : A ≤ E := hA.trans ((map_mono (map_subtype_le _)).trans le_sup_left)
  obtain ⟨ρ,⟨a⟩⟩ := BinaryConjugationSection.exists_conjugation_coordinates E A ⊥
    hAE hN bot_le (by rw [(⊥ : Subgroup G).normalizer_eq_top]; exact le_top)
  have hker : H ≤ ρ.ker := (SourceActionEndgame.RootCoordinates.elementary_core_action_component_kernel m) s D X
    hX hXK hXr hfix hcomm e A ⊥ hA ρ a
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  apply commutator_le.mpr
  intro g hg x hx
  exact (a.action_mem_ker_iff (⟨g,show g ∈ E from mem_sup_left hg⟩ : E)).mp
    (hker hg) x hx


end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
