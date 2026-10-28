module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameCriticalCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreElementary

/-!
# SourceCoreSmall without strict core enlargement

These are the original core-action arguments with their literal subtype maps,
using only SecondaryActionData. No strict enlargement clause is supplied.
They feed recognition of the full component-core Frattini module.
Source: Aschbacher--Smith, original 4.3.2 and 4.3.11--16, pp.617--619.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement

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
include m D hX hXK hXr hfix hcomm e

theorem abelian_core_centralizes_component
    (A : Subgroup G) [IsMulCommutative A]
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    (hN : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G)) :
    s.component.map (rootNormalizer c).subtype ≤ centralizer (A : Set G) := by
  let M := s.component.map (rootNormalizer c).subtype
  let O := (omega A (p := 2) 1).map A.subtype
  let : (omega A (p := 2) 1).Characteristic := omega_characteristic A 1
  let : IsElementaryAbelian 2 (omega A (p := 2) 1) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.map_subtype
  have hO := (SourceActionEndgame.RootCoordinates.elementary_core_centralizes_component m) s D X hX hXK hXr hfix hcomm e O
    ((map_subtype_le _).trans hA)
    (hN.trans (normalizer_le_normalizer_characteristic_image A _))
  let : Group.IsPerfect s.component := s.isComponent.perfect
  let : Group.IsPerfect M := Group.IsPerfect.ofSurjective
    (f := (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).toMonoidHom)
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).surjective
  have hp : IsPGroup 2 A :=
    ((pCore_isPGroup (p := 2) (G := s.component)).map s.component.subtype |>.map
      (rootNormalizer c).subtype).to_le hA
  exact OmegaAction.perfect_centralizes_of_centralizes_omega_one M A hp
    (le_sup_left.trans hN) hO
end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame

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

/-- A source core section of binary degree at most twelve has trivial component action when irreducible. -/
theorem small_core_section_component_kernel
    (A B : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (a : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ)
    [ρ.IsIrreducible] (hbound : Nat.card W ≤ 2^12) :
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
  have hd := hbound
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hd
  have hdim : Module.finrank (ZMod 2) W ≤ 12 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hd
  have h9 := Representation.PSL3Four.normal_core_simple_degree H eq ρ hdim hnt
  apply (SourceActionEndgame.RootCoordinates.component_section_not_odd_degree m) s D X hX hXK hfix hcomm A B hA
    a.kernel_le a.normalized a.kernel_normalized (show Odd 9 by decide)
  rw [a.relIndex_eq_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h9]


/-- The component fixes every source section of binary degree at most twelve, including sections of nonabelian subgroups. -/
theorem small_core_action_component_kernel
    (A B : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (a : BinaryConjugationSection (s.component.map (rootNormalizer c).subtype ⊔ X) A B ρ) (hbound : Nat.card W ≤ 2^12) :
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
  let : N.quotientRepresentation.IsIrreducible := hi
  exact hnt ((SourceActionEndgame.RootCoordinates.small_core_section_component_kernel m) s D X hX hXK hXr hfix hcomm e
    _ _ ((a.invariantPreimage_le P).trans hA) N.quotientRepresentation bb
      ((Nat.card_le_card_of_surjective N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective).trans
        ((Nat.card_le_card_of_injective (fun x : P.toSubmodule => (x : W))
          Subtype.val_injective).trans hbound)))

end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
