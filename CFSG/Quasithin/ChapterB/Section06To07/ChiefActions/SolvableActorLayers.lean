module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WholeActor
public import Theory.SpecificGroups.OrthogonalFourBinary.WreathAction
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Solvable
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.Rank
public import Theory.Representation.BinaryOffender.IrreducibleResidual
public import CFSG.Quasithin.Defs

/-!
# Matched solvable actor and offender types

The same one- or two-factor source decomposition identifies both the whole
faithful actor and its offender subgroup. In the one-factor branch the two
are S₃. In the two-factor branch transitivity gives the full S₃≀C₂ actor,
while the offender subgroup is S₃ × S₃. The original SQTK cover bounds the
factor count before this common case split, preserving the source pairing.

The final theorem uses the literal faithful image of an irreducible chief
action. Its vanishing two-core and inherited minimal parabolicity discharge
the hypotheses of the source solvable factor theorem.

Source: Aschbacher–Smith B.6.9 and original 3.1.9(5), printed pp.115–116,578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB

/-- The ambient and offender types are chosen from the same factor count. -/
theorem SolvableFFFactors.actor_and_offender_types
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (d : SolvableFFFactors ρ) (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (hr : pResidual 2 G ≤ offenderSubgroup ρ)
    (hc : d.count = 1 ∨ d.count = 2)
    (ht : ∀ i j, ∃ g : G, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j) :
    (Nonempty (G ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (offenderSubgroup ρ ≃* Equiv.Perm (Fin 3))) ∨
    (Nonempty (G ≃* RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∧
      Nonempty (offenderSubgroup ρ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) := by
  obtain ⟨e₃⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  rcases hc with hc | hc
  · obtain ⟨c,e,he⟩ := d.one_factor_moved_natural_coordinates hf hcore hr hc
    exact Or.inl ⟨⟨e.trans e₃⟩,⟨(d.singleActorCoordinates hc).trans e₃⟩⟩
  · obtain ⟨c,e,he⟩ := d.two_factor_moved_orthogonal_coordinates hf hcore hr hc ht
    obtain ⟨eW,eV,hev⟩ := OrthogonalFourBinary.isometry_equiv_natural_wreath
    exact Or.inr ⟨⟨(e.trans eW).trans
      (RegularWreathProduct.congr e₃ (MulEquiv.refl _))⟩,
      ⟨(d.pairActorCoordinates hc).trans (MulEquiv.prodCongr e₃ e₃)⟩⟩

universe u v
/-- The original SQTK cover bounds the same source factor count for both layers. -/
theorem chief_solvable_image_actor_and_offender_types
    {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    {K : GroupClass.{u}} (hG : IsSQTK K G)
    (S : Sylow 2 G) (hS : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (imageRepresentation ρ))
    (hsolv : Group.IsSolvable (actionImage ρ)) :
    (Nonempty (actionImage ρ ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (offenderSubgroup (imageRepresentation ρ) ≃* Equiv.Perm (Fin 3))) ∨
    (Nonempty (actionImage ρ ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∧
      Nonempty (offenderSubgroup (imageRepresentation ρ) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hf := imageRepresentation_injective ρ
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    obtain ⟨A,hA⟩ := hff
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
    obtain ⟨g,hg⟩ := hq (a : actionImage ρ)
    apply ha
    apply Subtype.ext
    change (a : actionImage ρ) = 1
    rw [←hg]
    exact (show g ∈ q.ker from he ▸ mem_top g)
  obtain ⟨d,ht,_,hr,_⟩ := source_solvable_minimalParabolic_factors
    (S.mapSurjective hq) (minimalParabolic_reduced_image S hS q hq hc hn).2
    hsolv hc hf hff
  have hcount := d.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank q hq
    (hG.stronglyQuasithin 3 (by decide) (by decide))
  exact d.toSolvableFFFactors.actor_and_offender_types hf hc hr hcount
    (fun i j => let ⟨t,ht⟩ := ht i j; ⟨t,ht⟩)

end CFSG.Quasithin.ChapterB
