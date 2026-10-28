module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.Reduction

/-!
# Outer four-group generation after centralizer containment

Intrinsic maximality of C_L(z), together with G = LT, identifies the proper
obstruction overgroup containing C_G(z). For p congruent to three modulo four,
a solvable Sylow overgroup moving z contradicts solvable E-generation. This
branch includes p = 3. For p congruent to one modulo four, an odd-prime subgroup
normalized by C_T(B) and inverted by z in B must be trivial, where B is a
conjugate of the whole original family actor.

The assembly proves the contradiction from these explicit model constructions.
It discharges the ambient two-core, conjugate-family membership, local Sylow,
E-member inheritance, odd squaring, and the congruence dichotomy. Intrinsic
centralizer maximality and the two model constructions remain independent
premises; this is not yet the unconditional outer four-group exclusion. The
SQTK, actor-order and inner-intersection hypotheses of that exclusion belong
to the producers of the model constructions, not to this algebraic assembly.

Source: Aschbacher--Smith, E.1.1--2, E.1.5, E.1.13 and E.1.14(7), printed
pp.209--214, and A.2.3(2), p.33; Aschbacher, *GF(2)-representations of finite
groups* (1982), Lemma 4.11.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry
variable {G : Type*} [Group G] [Finite G]

/-- Conditional source assembly for both odd-prime congruence cases. Its
remaining premises are intrinsic maximality and concrete local constructions;
neither E-generation nor a rank-one E-member is assumed. -/
theorem false_of_congruence_constructions [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T) {A : Subgroup G} (hA : A ∈ d.family)
    {z : G} (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup)
    (hmax : IsCoatom ((centralizer ({z} : Set G)).subgroupOf (generalizedFitting G)))
    (hthree : p % 4 = 3 → ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧
      Group.IsSolvable H ∧ ¬ H ≤ centralizer ({z} : Set G))
    (hone : p % 4 = 1 → ∃ (g : G) (r : ℕ), r.Prime ∧ Odd r ∧
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      ∃ X : Subgroup G, IsPGroup r X ∧ X ≠ ⊥ ∧
        (T : Subgroup G) ⊓ centralizer
          (A.map (MulAut.conj g).toMonoidHom : Set G) ≤ normalizer (X : Set G) ∧
        ∀ x ∈ X, z * x * z⁻¹ = x⁻¹) : False := by
  have hMC := InnerGeometry.overgroup_eq_centralizer_of_intrinsic_coatom
    (generalizedFitting G) hLT d z hTz hCM hmax
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨k, hk⟩ := ho
    omega
  rcases hmod with h | h
  · obtain ⟨g, r, hr, hro, hBT, hzB, X, hX, hne, hn, hinv⟩ := hone h
    let : Fact r.Prime := ⟨hr⟩
    have hcore : pCore 2 G = ⊥ :=
      (SimpleSocle.structure_of_sylow_supplement
        (nonabelian_of_model hp ho hmodel) T hLT).2.2.1
    exact hne (conjugate_inverted_odd_subgroup_eq_bot d hcore hMC hA g hBT hzB
      hro X hX hn hinv)
  · obtain ⟨H, hTH, hs, hn⟩ := hthree h
    let := hs
    exact hn (hMC ▸ solvable_sylow_overgroup_le d H hTH)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry
