module

public import Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry.Overgroups
public import Theory.SpecificGroups.SymplecticFour.Binary.PointModel
public import Theory.SpecificGroups.SymplecticFour.Binary.PlaneModel
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The two parabolics of the actual binary derived symplectic group

The explicit polar equivalence identifies Sp₄(2)′ with A₆. Its index in
Sp₄(2) is two. Each full matrix parabolic has order 48, so its intersection
with the derived group has order 24. The two intersections are distinct:
their common subgroup lies in the full Borel, of order 16.

Intersect the standard unipotent Sylow subgroup with the derived group.
The existing A₆ Sylow-overgroup census then proves that the two literal
matrix parabolics are exactly its maximal overgroups. The argument retains
the actual derived carrier and both point/plane labels; an isomorphism
between abstract groups of order 24 would not establish this statement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.5,
printed pp.419–422, and the Sp₄(2)′ case of 15.3.28(2), p.1131.
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.Binary
open Theory.SpecificGroups.SymmetricSix hiding A6
local notation "D" => commutator (Sp (ZMod 2))

/-- The point and plane stabilizers restricted to Sp₄(2)′, in that order. -/
noncomputable def derivedParabolic (i : Fin 2) : Subgroup D :=
  (if i = 0 then pointParabolic else planeParabolic (F := ZMod 2)).subgroupOf D

private theorem card_derived : Nat.card D = 360 := by
  rw [Nat.card_congr (derivedEquivAlternatingSix (F := ZMod 2) (by simp)).toEquiv]
  exact AlternatingSix.ShadowLocal.card_A6

private theorem index_derived : (D).index = 2 := by
  have h := (D).card_mul_index
  rw [card_derived, card_sp_two] at h
  omega

private theorem card_full_parabolic (i : Fin 2) :
    Nat.card (if i = 0 then pointParabolic else planeParabolic : Subgroup (Sp (ZMod 2))) = 48 := by
  fin_cases i
  · change Nat.card (pointParabolic (F := ZMod 2)) = 48
    rw [Nat.card_congr pointParabolicZModEquivProd.toEquiv]
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm]
  · change Nat.card (planeParabolic (F := ZMod 2)) = 48
    rw [Nat.card_congr planeParabolicZModEquivProd.toEquiv]
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm]

private theorem card_derived_intersection (P : Subgroup (Sp (ZMod 2))) (hP : Nat.card P = 48) :
    Nat.card (P.subgroupOf D) = 24 := by
  let e : P.subgroupOf D ≃* (D).subgroupOf P := {
    toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hd := (D).relIndex_dvd_index_of_normal (K := P)
  rw [index_derived] at hd
  have hc := ((D).subgroupOf P).card_mul_index
  change Nat.card ((D).subgroupOf P) * (D).relIndex P = Nat.card P at hc
  rw [← Nat.card_congr e.toEquiv, hP] at hc
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · rw [h, mul_one] at hc
    have hd' := (P.subgroupOf D).card_subgroup_dvd_card
    rw [hc, card_derived] at hd'
    norm_num at hd'
  · rw [h] at hc
    omega

/-- Each literal derived parabolic has order 24. -/
theorem card_derivedParabolic (i : Fin 2) : Nat.card (derivedParabolic i) = 24 :=
  card_derived_intersection _ (card_full_parabolic i)

private theorem derivedParabolic_ne_top (i : Fin 2) : derivedParabolic i ≠ ⊤ := by
  intro he
  have hc := card_derivedParabolic i
  rw [he, Nat.card_congr (topEquiv : (⊤ : Subgroup D) ≃* D).toEquiv, card_derived] at hc
  omega

/-- Restriction to the derived group keeps the two parabolics distinct. -/
theorem derivedParabolic_injective : Function.Injective derivedParabolic := by
  have hne : derivedParabolic 0 ≠ derivedParabolic 1 := by
    intro he
    have hle : derivedParabolic 0 ≤ (borel (F := ZMod 2)).subgroupOf D := by
      intro x hx
      have hx' : x ∈ derivedParabolic 1 := he ▸ hx
      exact ⟨hx, hx'⟩
    have hc := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    have hc' : Nat.card ((borel (F := ZMod 2)).subgroupOf D) ≤ Nat.card (borel (F := ZMod 2)) := by
      let f : (borel (F := ZMod 2)).subgroupOf D → (borel (F := ZMod 2)) :=
        fun x => ⟨x.val.val, x.property⟩
      exact Nat.card_le_card_of_injective f (fun _ _ h => Subtype.ext (Subtype.ext
        (congrArg (fun x => x.val) h)))
    rw [card_derivedParabolic] at hc
    rw [card_borel] at hc'
    norm_num at hc'
    omega
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (hne hij)
  · exact False.elim (hne hij.symm)
  · rfl

/-- The two literal matrix parabolics are exactly the maximal overgroups of
one actual Sylow subgroup in Sp₄(2)′. -/
theorem exists_derived_flag : ∃ T : Sylow 2 D,
    Function.Injective derivedParabolic ∧ ∀ P : Subgroup D,
      (IsCoatom P ∧ (T : Subgroup D) ≤ P) ↔ ∃ i, P = derivedParabolic i := by
  let e := derivedEquivAlternatingSix (F := ZMod 2) (by simp)
  let S := unipotentSylow (F := ZMod 2) (n := 1) (by norm_num) (by decide)
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal D
  have hTU : (T : Subgroup D) = (unipotent (F := ZMod 2)).subgroupOf D := hT
  have hle (i : Fin 2) : (T : Subgroup D) ≤ derivedParabolic i := by
    rw [hTU]
    intro x hx
    have hb := unipotent_le_borel hx
    fin_cases i
    · exact hb.1
    · exact hb.2
  have hcardT : Nat.card T = 8 := by
    rw [Nat.card_congr (e.subgroupMap (T : Subgroup D)).toEquiv]
    exact AlternatingSix.ShadowLocal.alternatingSylow_card (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hcoat (i : Fin 2) : IsCoatom (derivedParabolic i) := by
    rcases ComponentActionGeometry.sylow_overgroup_cases e T _ (hle i)
      (derivedParabolic_ne_top i) with he | hc
    · have hcard := card_derivedParabolic i
      rw [he, hcardT] at hcard
      omega
    · exact hc
  obtain ⟨g, _, hg⟩ := a6_coatoms_over_sylow (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  have cases (P : Subgroup D) (hP : IsCoatom P) (hTP : (T : Subgroup D) ≤ P) :=
    (hg (P.map e.toMonoidHom)).mp
      ⟨(e.mapSubgroup.isCoatom_iff P).mpr hP, map_mono hTP⟩
  refine ⟨T, derivedParabolic_injective, fun P => ⟨?_, ?_⟩⟩
  · rintro ⟨hp, htp⟩
    have hh := cases P hp htp
    have h0 := cases (derivedParabolic 0) (hcoat 0) (hle 0)
    have h1 := cases (derivedParabolic 1) (hcoat 1) (hle 1)
    have hne : (derivedParabolic 0).map e.toMonoidHom ≠
        (derivedParabolic 1).map e.toMonoidHom := by
      intro he
      have hi := derivedParabolic_injective (e.mapSubgroup.injective he)
      exact (by decide : (0 : Fin 2) ≠ 1) hi
    have he : P.map e.toMonoidHom = (derivedParabolic 0).map e.toMonoidHom ∨
        P.map e.toMonoidHom = (derivedParabolic 1).map e.toMonoidHom := by
      rcases hh with hh | hh <;> rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
        grind
    rcases he with he | he
    · exact ⟨0, e.mapSubgroup.injective he⟩
    · exact ⟨1, e.mapSubgroup.injective he⟩
  · rintro ⟨i, rfl⟩
    exact ⟨hcoat i, hle i⟩

end Theory.SpecificGroups.SymplecticFour.Binary
