module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition

/-!
# The marked product step of the root-five calculation

This intermediate output records only the normalizer coordinates and the
inverting involution. Generation by the seed orbit, component centralization
and the complement to the extraspecial core are derived separately. Constructing
this output remains a genuine geometric obligation of 47.2(2).

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- Intermediate marked normalizer coordinates; this omits the generation and
complement assertions of `RootFiveWitness`. -/
structure ProductData (D : Seed G) (E : Subgroup G) where
  equiv : normalizer (E : Set G) ≃* (DihedralGroup 5 × alternatingGroup (Fin 5))
  component_factor :
    ((⊥ : Subgroup (DihedralGroup 5)).prod (⊤ : Subgroup (alternatingGroup (Fin 5)))).map
      ((normalizer (E : Set G)).subtype.comp equiv.symm.toMonoidHom) = fiveComponent E
  inverter : G
  inverter_conj : IsConj D.z inverter
  inverts : ∀ x ∈ E, inverter * x * inverter⁻¹ = x⁻¹
  dihedral_factor :
    ((⊤ : Subgroup (DihedralGroup 5)).prod (⊥ : Subgroup (alternatingGroup (Fin 5)))).map
      ((normalizer (E : Set G)).subtype.comp equiv.symm.toMonoidHom) =
      E ⊔ zpowers inverter

namespace ProductData
variable {D : Seed G} {E : Subgroup G} (W : ProductData D E)

/-- The marked dihedral coordinate forces the entire component to centralize
its chosen inverter. -/
theorem component_le : fiveComponent E ≤ involutionCentralizer W.inverter := by
  have hi : W.inverter ∈ E ⊔ zpowers W.inverter := mem_sup_right (mem_zpowers _)
  rw [← W.dihedral_factor] at hi
  obtain ⟨i, hi, hii⟩ := hi
  rw [← W.component_factor]
  rintro _ ⟨a, ha, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [← hii, ← map_mul, ← map_mul]
  apply congrArg
  exact Prod.ext (by simp [show a.1 = 1 from ha.1]) (by simp [show i.2 = 1 from hi.2])

include W in
/-- Every order-three subgroup in these coordinates lies in the A₅ factor. -/
theorem three_le_component (A : Subgroup G) (hA : Nat.card A = 3)
    (hAN : A ≤ normalizer (E : Set G)) : A ≤ fiveComponent E := by
  intro x hx
  let a : A := ⟨x, hx⟩
  let n : normalizer (E : Set G) := ⟨x, hAN hx⟩
  have hp : n ^ 3 = 1 := Subtype.ext (by
    have hh := pow_card_eq_one' (x := a)
    rw [hA] at hh
    exact congrArg (fun y : A => (y : G)) hh)
  have hp' : (W.equiv n).1 ^ 3 = 1 := by
    simpa only [map_pow, map_one, Prod.pow_fst, Prod.fst_one] using
      congrArg (fun a => (W.equiv a).1) hp
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp')
    (orderOf_dvd_natCard (W.equiv n).1)
  rw [DihedralGroup.nat_card] at hd
  have hone : (W.equiv n).1 = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (by
    simpa using hd))
  rw [← W.component_factor]
  exact ⟨W.equiv n, ⟨hone, mem_top _⟩, by simp [n]⟩

end ProductData
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer
