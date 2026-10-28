module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.InitialModule
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover.Ambient

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The whole central-omega natural quotient in the small G₂ case

The supplement clause of the proved FF classification says that the moved
space supplements the fixed space, except for four natural-module rows.
The component order 6048 excludes all four. The literal moved-section
quotient therefore identifies the entire central-omega quotient by its
component-fixed space with the trace-zero octonions modulo scalars.

This is an initial-layer result. Exhaustion of the intrinsic commutator
core still requires the later MS93 geometric arguments.
Source: AS B.5.1(5), C.1.31–32; MS93 (3.2)(vii), pp.863–866.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction
open ChapterB.QuasisimpleSource

private theorem supplement_card_ne {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    (hc : Nat.card D = 6048) : ¬ SupplementNatural ρ := by
  intro hs
  cases hs with
  | symplectic F he =>
    have heq := (Nat.card_congr he.some.groupEquiv.toEquiv).symm.trans hc
    rw [Theory.SpecificGroups.SymplecticFour.card_sp] at heq
    by_cases hq : Nat.card F.Carrier ≤ 2
    · have hb : Nat.card F.Carrier ^ 4 * (Nat.card F.Carrier ^ 2 - 1) *
          (Nat.card F.Carrier ^ 4 - 1) ≤ 2 ^ 4 * (2 ^ 2 - 1) * (2 ^ 4 - 1) := by
        gcongr
      norm_num at hb
      omega
    · have hb : 3 ^ 4 * (3 ^ 2 - 1) * (3 ^ 4 - 1) ≤
          Nat.card F.Carrier ^ 4 * (Nat.card F.Carrier ^ 2 - 1) *
            (Nat.card F.Carrier ^ 4 - 1) := by
        gcongr <;> omega
      norm_num at hb
      omega
  | alternatingSix he =>
    have heq := (Nat.card_congr he.some.groupEquiv.toEquiv).symm.trans hc
    rw [nat_card_alternatingGroup] at heq
    norm_num [Nat.factorial] at heq
  | alternatingEight he =>
    have heq := (Nat.card_congr he.some.groupEquiv.toEquiv).symm.trans hc
    rw [nat_card_alternatingGroup] at heq
    norm_num [Nat.factorial] at heq
  | linearThree he =>
    have heq := (Nat.card_congr he.some.groupEquiv.toEquiv).symm.trans hc
    rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear] at heq
    norm_num [BinaryField.two] at heq

private theorem moved_sup_fixed_of_card {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D)
    [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hc : Nat.card C = 6048) (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    moved ρ C ⊔ fixedSpace ρ C = ⊤ := by
  obtain ⟨hCJ,⟨c⟩⟩ := SourceCompletion.ff_socle_source_conclusion ρ C hC hsq hf hff
  have hc' : Nat.card (C.subgroupOf (offenderSubgroup ρ)) = 6048 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCJ).toEquiv).trans hc
  have hs : c.sectionData.space.toSubmodule ⊔
      Representation.invariants (ρ.comp (offenderSubgroup ρ).subtype) = ⊤ := by
    rcases c.clause_five with hs | hs
    · exact hs
    · exact (supplement_card_ne _ hc' hs.2.1).elim
  have hm := c.sectionData.space_eq
  rw [moved_comp_map,map_subgroupOf_eq_of_le hCJ] at hm
  have hi : Representation.invariants (ρ.comp (offenderSubgroup ρ).subtype) ≤ fixedSpace ρ C := by
    intro v hv g
    exact hv ⟨g,hCJ g.property⟩
  apply top_unique
  rw [← hs,hm]
  exact sup_le_sup_left hi _

private def wholeQuotientEquiv {D E V W : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {τ : Representation (ZMod 2) E W}
    {C : Subgroup D} [C.Normal] (s : MovedSection ρ C)
    (hsup : moved ρ C ⊔ fixedSpace ρ C = ⊤)
    (e : ActionEquiv (s.action.comp C.subtype) τ) :
    ActionEquiv ((fixedQuotient ρ C).comp (C).subtype) τ := by
  rw [←s.space_eq] at hsup
  let Z := (fixedSubrepresentation ρ C).toSubmodule
  let f : s.space.toSubmodule →ₗ[ZMod 2] V ⧸ Z := Z.mkQ.comp s.space.toSubmodule.subtype
  have hk : f.ker = s.central.toSubmodule := by
    ext w
    rw [s.central_eq]
    change Z.mkQ (w:V) = 0 ↔ _
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h g
      exact Subtype.ext (h g)
    · intro h g
      exact congrArg Subtype.val (h g)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨v,rfl⟩ := Z.mkQ_surjective x
    obtain ⟨w,hw,z,hz,hv⟩ := Submodule.mem_sup.mp
      (hsup ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
    refine ⟨⟨w,hw⟩,?_⟩
    change Z.mkQ w = Z.mkQ v
    rw [←hv,map_add]
    have hz0 : Z.mkQ z = 0 := (Submodule.Quotient.mk_eq_zero Z).mpr hz
    rw [hz0,add_zero]
  let Q : (s.space.toSubmodule ⧸ s.central.toSubmodule) ≃ₗ[ZMod 2] V ⧸ Z :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)
  have hQ (w : s.space.toSubmodule) : Q (s.central.toSubmodule.mkQ w) = Z.mkQ (w:V) := rfl
  refine {groupEquiv := e.groupEquiv, linearEquiv := Q.symm.trans e.linearEquiv, intertwines := ?_}
  intro g x
  obtain ⟨w,rfl⟩ := hf x
  change e.linearEquiv (Q.symm ((fixedQuotient ρ C) g (f w))) =
    τ (e.groupEquiv g) (e.linearEquiv (Q.symm (f w)))
  have h1 : Q.symm (f w) = s.central.toSubmodule.mkQ w := by
    apply Q.injective
    rw [Q.apply_symm_apply,hQ]
    rfl
  have h2 : Q.symm ((fixedQuotient ρ C) g (f w)) =
      s.central.quotientRepresentation (g:D) (s.central.toSubmodule.mkQ w) := by
    apply Q.injective
    rw [Q.apply_symm_apply]
    change Z.mkQ (ρ (g:D) (w:V)) = Q (s.central.toSubmodule.mkQ (s.space.toRepresentation (g:D) w))
    rw [hQ]
    rfl
  rw [h1,h2]
  exact e.intertwines g (s.central.toSubmodule.mkQ w)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "H" => (L ⊔ R : Subgroup G)
local notation "C" => quotientComponent (L := L) (R := R)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
include h e

theorem centralOmega_moved_sup_fixed :
    moved (centralOmegaAction h e) C ⊔ fixedSpace (centralOmegaAction h e) C = ⊤ := by
  let := (quotientComponent_structure h e).1
  let := (quotientComponent_structure h e).2.1
  let := (quotientComponent_structure h e).2.2.1
  exact moved_sup_fixed_of_card _ _ (quotientComponent_card h e)
    (quotientComponent_structure h e).2.2.2 (quotientComponent_sqtk h)
    (centralOmegaAction_faithful h e) (central_omega_FF h e)

theorem centralOmega_whole_natural :
    let := (quotientComponent_structure h e).1
    Nonempty (ActionEquiv
      ((fixedQuotient (centralOmegaAction h e) C).comp (C).subtype)
      (g2DerivedNatural (ZMod 2))) := by
  let := (quotientComponent_structure h e).1
  obtain ⟨E⟩ := (initial_moved_natural h e).2
  exact ⟨wholeQuotientEquiv (MovedSection.ofNormal _ _) (centralOmega_moved_sup_fixed h e) E⟩

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction
