module
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.TorusEquivariance
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.ModelRelations
public import Theory.SpecificGroups.G2.FiniteUniversalCover

/-!
# Commuting positive-root lifts in G₂

In a central extension, torus-equivariant additive sections satisfy the ten
literal commuting relations between the positive A–F roots. For each pair a
torus element fixes the first root and scales the second nontrivially.
Conjugating the second section by the first gives another additive section
with the same projection and scalar action; scalar-equivariant uniqueness
therefore makes this conjugation trivial. A generator of the field units
separates all needed characters when the field has more than four elements.

The final applications construct such sections for finite perfect central
covers, including the literal universal projection, in both ordinary source
ranges. Polynomial interchange relations and defining-prime exclusion remain
with the positive-relations assembly.

Source: Aschbacher–Smith I.1.3–I.1.4 (PDF pp.418–419), with the source ranges
in A.2.2–A.2.4 (PDF p.44), and GLS III §6.1. The A–F roots and their torus
characters use the attributed ATLAS octonion model of the imported modules.
-/

public section
namespace Atlas.G2.MultiplierOrdinary.RootSections
variable {F E : Type*} [Field F] [Group E] {f : E →* Model F}

/-- A torus element fixing one root and scaling a commuting base root
nontrivially forces their lifted sections to commute. -/
theorem commute_of_torus_separates (L : RootSections f) (hL : L.TorusEquivariant)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (i j : Fin 6) (l m : Fˣ)
    (hi : positiveWeight i l m = 1) (hj : positiveWeight j l m ≠ 1)
    (hbase : ∀ s t : F, positiveRoot i s * positiveRoot j t =
      positiveRoot j t * positiveRoot i s) (s t : F) :
    L.x i s * L.x j t = L.x j t * L.x i s := by
  obtain ⟨z, hz⟩ := hf (torus l m)
  have hfix : z * L.x i s * z⁻¹ = L.x i s := by
    rw [hL l m z hz, hi, Units.val_one, one_mul]
  let u : Multiplicative F →* E := (MulAut.conj (L.x i s)).toMonoidHom.comp (L.root j)
  have hproj : f.comp u = f.comp (L.root j) := by
    apply MonoidHom.ext
    intro a
    change f (L.x i s * L.x j a.toAdd * (L.x i s)⁻¹) = f (L.x j a.toAdd)
    rw [map_mul, map_mul, map_inv, L.project_x, L.project_x, hbase]
    simp only [mul_inv_cancel_right]
  have hu (a : F) : z * u (.ofAdd a) * z⁻¹ =
      u (.ofAdd ((positiveWeight j l m : F) * a)) := by
    change z * (L.x i s * L.x j a * (L.x i s)⁻¹) * z⁻¹ =
      L.x i s * L.x j ((positiveWeight j l m : F) * a) * (L.x i s)⁻¹
    calc
      _ = (z * L.x i s * z⁻¹) * (z * L.x j a * z⁻¹) *
          (z * L.x i s * z⁻¹)⁻¹ := by group
      _ = _ := by rw [hfix, hL l m z hz]
  have he := hom_ext_of_scalar_equivariant hk u (L.root j) hproj z
    (positiveWeight j l m : F) (fun h => hj (Units.ext h)) hu (hL l m z hz j)
  have ht := DFunLike.congr_fun he (.ofAdd t)
  change L.x i s * L.x j t * (L.x i s)⁻¹ = L.x j t at ht
  exact (mul_inv_eq_iff_eq_mul).mp ht

private theorem exists_separating_unit [Finite F] (hF : 4 < Nat.card F) :
    ∃ c : Fˣ, c ≠ 1 ∧ c^2 ≠ 1 ∧ c^3 ≠ 1 := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have horder : 3 < orderOf c := by rw [hc, Nat.card_units]; omega
  refine ⟨c, ?_, ?_, ?_⟩
  · simpa using pow_ne_one_of_lt_orderOf (x := c) (n := 1) (by decide) (by omega)
  · exact pow_ne_one_of_lt_orderOf (by decide) (by omega)
  · exact pow_ne_one_of_lt_orderOf (by decide) horder

/-- All ten commuting relations lift for any torus-equivariant root sections
when the field has more than four elements. -/
theorem TorusEquivariant.commutingRelations [Finite F]
    (L : RootSections f) (hL : L.TorusEquivariant) (hF : 4 < Nat.card F)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    L.CommutingRelations := by
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_separating_unit hF
  have R := (model_collectionRelations (F := F)).toCommutingRelations
  constructor
  · exact L.commute_of_torus_separates hL hf hk 1 0 c (c^2)
      (by simp [positiveWeight])
      (by simpa [positiveWeight, ← pow_succ, ← pow_succ', ← pow_two] using hc3) R.ba
  · exact L.commute_of_torus_separates hL hf hk 2 0 1 c
      (by simp [positiveWeight])
      (by simpa [positiveWeight, ← pow_succ, ← pow_succ', ← pow_two] using hc1) R.ca
  · exact L.commute_of_torus_separates hL hf hk 2 1 1 c
      (by simp [positiveWeight])
      (by simpa [positiveWeight, ← pow_succ, ← pow_succ', ← pow_two] using hc1) R.cb
  · exact L.commute_of_torus_separates hL hf hk 3 0 c 1
      (by simp [positiveWeight])
      (by simpa [positiveWeight, ← pow_succ, ← pow_succ', ← pow_two] using hc1) R.da
  · exact L.commute_of_torus_separates hL hf hk 3 1 c 1
      (by simp [positiveWeight])
      (by simpa [positiveWeight, ← pow_succ, ← pow_succ', ← pow_two] using hc2) R.db
  · exact L.commute_of_torus_separates hL hf hk 4 0 (c^2) c
      (by simp [positiveWeight])
      (by simpa [positiveWeight, ← pow_succ, ← pow_succ', ← pow_two] using hc3) R.ea
  · exact L.commute_of_torus_separates hL hf hk 4 2 (c^2) c
      (by simp [positiveWeight])
      (by simpa [positiveWeight, ← pow_succ, ← pow_succ', ← pow_two] using hc2) R.ec
  · exact L.commute_of_torus_separates hL hf hk 4 3 (c^2) c
      (by simp [positiveWeight])
      (by simpa [positiveWeight, ← pow_succ, ← pow_succ', ← pow_two] using hc1) R.ed
  · exact L.commute_of_torus_separates hL hf hk 5 0 c c
      (by simp [positiveWeight])
      (by simpa [positiveWeight, ← pow_succ, ← pow_succ', ← pow_two] using hc2) R.fa
  · exact L.commute_of_torus_separates hL hf hk 5 1 c c
      (by simp [positiveWeight])
      (by simpa [positiveWeight, pow_two] using hc1) R.fb

end Atlas.G2.MultiplierOrdinary.RootSections

namespace Atlas.G2.MultiplierOrdinary
open PerfectCentralCovering
variable {F E : Type*} [Field F] [Finite F] [Group E]

/-- The normalized sections of an actual finite perfect central cover in the
ordinary even-field range satisfy all ten commuting equations. -/
theorem even_cover_commuting_sections [Finite E] [CharP F 2]
    (hF : 4 < Nat.card F) (c : Cover E (Model F)) :
    ∃ L : RootSections c.toMonoidHom, L.TorusEquivariant ∧ L.CommutingRelations := by
  obtain ⟨L, hL⟩ := even_torusEquivariant_sections hF c.toMonoidHom
    c.surjective c.ker_le_center
  exact ⟨L, hL, hL.commutingRelations L hF c.surjective c.ker_le_center⟩

/-- The same construction on the prescribed finite perfect cover in the
ordinary prime-field range; the exceptional prime three is excluded. -/
theorem prime_cover_commuting_sections [Finite E] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p) (c : Cover E (Model F)) :
    ∃ L : RootSections c.toMonoidHom, L.TorusEquivariant ∧ L.CommutingRelations := by
  have hp5 := (Fact.out : p.Prime).five_le_of_ne_two_of_ne_three (by omega) (by omega)
  obtain ⟨L, hL⟩ := prime_torusEquivariant_sections hF (by omega) c.toMonoidHom
    c.surjective c.ker_le_center
  exact ⟨L, hL, hL.commutingRelations L (by omega) c.surjective c.ker_le_center⟩

/-- Application on the literal universal covering projection in even
characteristic, with the torus-equivariance premise discharged. -/
theorem even_universal_commuting_sections [CharP F 2] (hF : 4 < Nat.card F) :
    ∃ L : RootSections (universalProjection (Model F)),
      L.TorusEquivariant ∧ L.CommutingRelations := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact even_cover_commuting_sections hF (universalCover (Model F))

/-- Application on the literal universal covering projection in the ordinary
prime-field range, with the torus-equivariance premise discharged. -/
theorem prime_universal_commuting_sections {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p) :
    ∃ L : RootSections (universalProjection (Model F)),
      L.TorusEquivariant ∧ L.CommutingRelations := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact prime_cover_commuting_sections hF hp (universalCover (Model F))

end Atlas.G2.MultiplierOrdinary
end
