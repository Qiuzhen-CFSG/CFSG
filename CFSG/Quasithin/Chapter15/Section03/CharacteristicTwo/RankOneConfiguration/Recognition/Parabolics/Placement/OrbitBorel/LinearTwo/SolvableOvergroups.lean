module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearTwo.Coordinates
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal

/-!
# Solvable overgroups in the linear-two orbit

A solvable overgroup of the full root group in PSL₂(2ⁿ), n ≥ 2, lies in
its matrix Borel. The existing root-generation theorem proves this after
lifting to SL₂; a larger overgroup would be the whole nontrivial perfect
SL₂. Apply this independently to both coordinate projections and pull the
containment back through the actual orbit quotient.

This is used on Y₊(S ∩ L₀), whose solvability follows from the S₃ shadow.
It constructs Borel containment from solvability and the full root group.

Source: Aschbacher–Smith, proof of 15.3.27(1), printed p.1130 (PDF p.1147).
-/

@[expose] public section
open Subgroup
open Matrix.ProjectiveSpecialLinearGroup OddBorel EvenBorelResidual
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearTwo
variable {G : Type*} [Group G] [Finite G]
variable {L S : Subgroup G} {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem sl2_not_solvable (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) : ¬ Group.IsSolvable SL(2,F) := by
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := by simpa using ha
  have hasq : (a : F) ^ 2 ≠ 1 := by
    intro h
    apply ha1
    exact (frobenius_inj F 2) (by simpa [frobenius_def] using h)
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top a.ne_zero hasq⟩
  let : Nontrivial SL(2,F) := ⟨⟨
    Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F),
    1, by
      intro h
      have he := congrArg (fun g : SL(2,F) => g.val 0 1) h
      simp [Matrix.SpecialLinearGroup.transvection_coe] at he⟩⟩
  exact Group.IsPerfect.not_isSolvable _

private theorem projective_solvable_overgroup_le_borel
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (H : Subgroup PSL(2,F)) [Group.IsSolvable H]
    (hU : kernel F ≤ H) : H ≤ borel F := by
  let P := H.comap (BenderSuzuki.Converse.pi F)
  let f : P →* H :=
    ((BenderSuzuki.Converse.pi F).comp P.subtype).codRestrict H (fun x => x.property)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply BenderSuzuki.Converse.pi_injective
    exact congrArg (fun z : H => (z : PSL(2,F))) hxy
  let : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective hf
  have hP : P ≠ ⊤ := by
    intro he
    have hsur : Function.Surjective P.subtype := by
      intro x
      exact ⟨⟨x, he ▸ mem_top x⟩, rfl⟩
    exact sl2_not_solvable F hF (Group.isSolvable_of_surjective hsur)
  have hUP : Matrix.SpecialLinearGroup.upperUnipotent F ≤ P := by
    intro x hx
    apply hU
    rw [← upperUnipotent_map F]
    exact mem_map_of_mem _ hx
  have hb := Matrix.SpecialLinearGroup.overgroup_le_rankOneBorel hUP hP
  have he : (Matrix.SpecialLinearGroup.rankOneBorel F).map (BenderSuzuki.Converse.pi F) =
      borel F := by
    rw [Matrix.SpecialLinearGroup.rankOneBorel,
      map_normalizer_eq_of_bijective _
        ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩,
      upperUnipotent_map, normalizer_kernel]
  intro x hx
  obtain ⟨y, rfl⟩ := BenderSuzuki.Converse.pi_surjective (F := F) x
  rw [← he]
  exact mem_map_of_mem _ (hb hx)

private theorem product_solvable_overgroup_le_borel
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (H : Subgroup (PSL(2,F) × PSL(2,F)))
    [Group.IsSolvable H] (hU : (kernel F).prod (kernel F) ≤ H) :
    H ≤ (borel F).prod (borel F) := by
  have hproj (f : (PSL(2,F) × PSL(2,F)) →* PSL(2,F))
      (hf : kernel F ≤ H.map f) : H.map f ≤ borel F := by
    let : Group.IsSolvable (H.map f) := Group.isSolvable_of_surjective
      (f.subgroupMap_surjective H)
    exact projective_solvable_overgroup_le_borel F hF (H.map f) hf
  have hf := hproj (MonoidHom.fst _ _) (by
    intro x hx
    exact ⟨(x, 1), hU ⟨hx, one_mem _⟩, rfl⟩)
  have hs := hproj (MonoidHom.snd _ _) (by
    intro x hx
    exact ⟨(1, x), hU ⟨one_mem _, hx⟩, rfl⟩)
  exact fun x hx => ⟨hf (mem_map_of_mem _ hx), hs (mem_map_of_mem _ hx)⟩

omit [Finite G] in
theorem Coordinates.solvable_overgroup_le (a : Coordinates L S F)
    (hF : 4 ≤ Nat.card F) (X : Subgroup G) (hXL : X ≤ L)
    (hSX : S ⊓ L ≤ X) (hs : Group.IsSolvable X) : X ≤ canonicalBorel L S := by
  let H := X.subgroupOf L
  let : Group.IsSolvable X := hs
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hXL).toMonoidHom) (subgroupOfEquivOfLe hXL).injective
  let : Group.IsSolvable (H.map a.quotient) := Group.isSolvable_of_surjective
    (a.quotient.subgroupMap_surjective H)
  have hU : (kernel F).prod (kernel F) ≤ H.map a.quotient := by
    intro x hx
    obtain ⟨y, rfl⟩ := a.onto x
    have hy : y ∈ ((kernel F).prod (kernel F)).comap a.quotient := hx
    rw [a.root_preimage] at hy
    exact mem_map_of_mem _ (hSX ⟨hy, y.property⟩)
  have hb := product_solvable_overgroup_le_borel F hF (H.map a.quotient) hU
  intro x hx
  have hm : (⟨x, hXL hx⟩ : L) ∈ ((borel F).prod (borel F)).comap a.quotient :=
    hb (mem_map_of_mem a.quotient (show (⟨x, hXL hx⟩ : L) ∈ H from hx))
  rw [a.borel_preimage] at hm
  exact hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearTwo
