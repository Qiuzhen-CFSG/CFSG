module
public import Theory.SpecificGroups.SymplecticFour.CentralNaturalDerivedAmbient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
/-!
# The source field-size bound on actual moving derived groups

The local two-residual normalizes every commutator [W,L_alpha] and contains
it whenever W lies in the vertex stabilizer. Thus a derived subgroup lying
in the source fixed core is centralized by its actual actor. Applying the
natural quotient bound to its literal conjugation action gives order at most
four. The specialization uses the original radius-two group V_alpha^circ.

This proves the nonbinary numerical step in MS93 (3.10)(i), printed p.880.
The natural quotient coordinates and central derived containment are precisely
the preceding source hypotheses; the distance-four exclusion in (ii) remains
separate. No binary natural-six representation is used here.
-/
public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M F : Type*} [Group M] [Field F] [Finite F]

private theorem local_moving_le_component (R : Subgroup M) (a : Vertex R)
    (W : Subgroup (FreeAmalgam R)) (hW : W ≤ stabilizer R a) :
    ⁅W,Ltilde R a⁆ ≤ Ltilde R a := by
  have hn : stabilizer R a ≤ normalizer (Ltilde R a : Set _) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  exact le_normalizer_iff_commutator_le_right.mp (hW.trans hn)

/-- The field-size derived bound on an actual local moving group. -/
theorem local_moving_derived_card_le_four (R : Subgroup M) (a : Vertex R)
    (W : Subgroup (FreeAmalgam R)) (hW : W ≤ stabilizer R a)
    (hF : Nat.card F = 4)
    (π : Ltilde R a →* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hπ : Function.Surjective π)
    (f : ↥(⁅W,Ltilde R a⁆ : Subgroup (FreeAmalgam R)) →* Multiplicative
      (Theory.SpecificGroups.SymplecticFour.Vector F))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ (centralizer (Ltilde R a : Set (FreeAmalgam R))).comap
      (⁅W,Ltilde R a⁆ : Subgroup (FreeAmalgam R)).subtype)
    (hequiv : ∀ (l : Ltilde R a) (v : ↥(⁅W,Ltilde R a⁆ : Subgroup (FreeAmalgam R))),
      (f ⟨(l : FreeAmalgam R) * v * (l : FreeAmalgam R)⁻¹,
        (mem_normalizer_iff.mp (normalizer_commutator_ge_right W (Ltilde R a)
          l.property) v).mp v.property⟩).toAdd = π l • (f v).toAdd)
    (hderived : ⁅⁅W,Ltilde R a⁆,⁅W,Ltilde R a⁆⁆ ≤ fixedCore R a) :
    Nat.card (⁅⁅W,Ltilde R a⁆,⁅W,Ltilde R a⁆⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (f := 2) hF
  rw [←hF]
  exact Subgroup.ClassTwo.card_derived_le_of_natural_centralizer_section
    (Ltilde R a) ⁅W,Ltilde R a⁆ (local_moving_le_component R a W hW)
    (normalizer_commutator_ge_right W (Ltilde R a)) π hπ f hf hker hequiv
    (hderived.trans inf_le_right)

/-- Specialization to the literal source radius-two moving group. -/
theorem Vcirc_derived_card_le_four [Finite M]
    (R : Subgroup M) (geometry : Geometry R) (a : Vertex R)
    (ha : color R a = false) (hb : 2 < geometry.b R) (hF : Nat.card F = 4)
    (π : Ltilde R a →* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hπ : Function.Surjective π)
    (f : Vcirc R a →* Multiplicative
      (Theory.SpecificGroups.SymplecticFour.Vector F))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ (centralizer (Ltilde R a : Set (FreeAmalgam R))).comap
      (Vcirc R a).subtype)
    (hequiv : ∀ (l : Ltilde R a) (v : Vcirc R a),
      (f ⟨(l : FreeAmalgam R) * v * (l : FreeAmalgam R)⁻¹,
        (mem_normalizer_iff.mp (normalizer_commutator_ge_right (V R a) (Ltilde R a)
          l.property) v).mp v.property⟩).toAdd = π l • (f v).toAdd)
    (hderived : ⁅Vcirc R a,Vcirc R a⁆ ≤ fixedCore R a) :
    Nat.card (⁅Vcirc R a,Vcirc R a⁆ : Subgroup (FreeAmalgam R)) ≤ 4 :=
  local_moving_derived_card_le_four R a (V R a)
    ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)) hF π hπ f hf hker hequiv hderived
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
