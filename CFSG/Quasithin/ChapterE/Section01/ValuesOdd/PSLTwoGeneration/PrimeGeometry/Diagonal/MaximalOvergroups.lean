module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OvergroupModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups.DicksonReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups.TorusExtensions
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups.ExceptionalExtensions

/-!
# Assembly of the prime-field PGL₂ maximal-overgroup calculation

Dickson's theorem applied to the actual canonical PSL₂ intersection leaves
dihedral and exceptional intersections. The elementary, cyclic, Borel, and
subfield alternatives are excluded in `DicksonReduction`. `TorusExtensions`
identifies the whole overgroup with a full dihedral involution centralizer,
including when the inner intersection is a four-group. `ExceptionalExtensions`
constructs the S₄ extension of A₄ and excludes S₄ and A₅ intersections.

The final theorem discharges both extension premises and supplies exactly the
maximal-overgroup input of `concreteGeometry_of_psl_geometry_and_overgroups`.
It proves the auxiliary prime-field calculation used in
Aschbacher--Smith E.1.14(6), printed p.214, citing Aschbacher (1982), Lemma
4.10. The model equivalences concern the original subgroup M; dihedral
rotation order q±1 means group order 2(q±1).
-/

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal

open GorensteinWalter MaximalOvergroups

/-- Assemble the actual Dickson exhaustion with two explicit whole-subgroup
extension calculations. -/
public theorem sylowOvergroupModel_of_inner_extension_cases
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M)
    (hdihedral : ∀ z : ℕ,
      (z ∣ (Nat.card F - 1) / 2 ∨ z ∣ (Nat.card F + 1) / 2) →
      Nat.card (inner M) = 2 * z → Nonempty (inner M ≃* DihedralGroup z) →
      ∃ n : ℕ, (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
        Nonempty (M ≃* DihedralGroup n))
    (hexceptional :
      (Nonempty (inner M ≃* alternatingGroup (Fin 4)) ∨
        Nonempty (inner M ≃* Equiv.Perm (Fin 4)) ∨
        Nonempty (inner M ≃* alternatingGroup (Fin 5))) →
      Nonempty (M ≃* Equiv.Perm (Fin 4))) :
    SylowOvergroupModel F M := by
  rcases inner_dickson_cases hpodd hFcard T M hTM hM.ne_top with h | h
  · obtain ⟨z, hz, hcard, e⟩ := h
    exact Or.inr (hdihedral z hz hcard e)
  · exact Or.inl (hexceptional h)

/-- Every maximal subgroup of prime-field PGL₂ containing an ambient Sylow
two-subgroup is actually isomorphic to S₄ or to a full dihedral torus normalizer.
This discharges the overgroup premise of the prime-field local geometry assembly. -/
public theorem sylowOvergroupModel_of_prime_card
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hpgt : 5 < p) (hFcard : Nat.card F = p)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M) :
    SylowOvergroupModel F M := by
  exact sylowOvergroupModel_of_inner_extension_cases hpodd hFcard T M hM hTM
    (prime_torusModel_of_inner_dihedral hpodd hpgt hFcard T M hM hTM)
    (symmetric_four_of_inner_exceptional hpodd hpgt hFcard T M hM hTM)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal
