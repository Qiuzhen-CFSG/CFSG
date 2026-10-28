module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.FamilyTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Maximality
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.WreathedNormalizer
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Transporting inner-section geometry to the original eight-actor

Let A be an actual actor in the obstruction family and B ≤ A. If O₂(G) = 1,
then tau(T,A) centralizes B. An odd-prime subgroup X normalized by C_T(B)
is therefore normalized by tau(T,A). The local E-member argument for A gives
[X,A] ≤ M, and commutator monotonicity gives [X,B] ≤ M. This does not require
B to belong to the family, and preserves the local Sylow, quotient-rank and
tau conditions through the existing E-member inheritance theorem.

Apply this with B = A ∩ F*(G), of order four. Intrinsic maximality of the
involution centralizer, together with the supplied centralizer containment,
identifies M with C_G(z). A solvable Sylow overgroup moving z when p ≡ 3
(mod 4), or the normalized odd subgroup for B when p ≡ 1 (mod 4), then gives
a contradiction. Both constructions can be shared with the inner-family
geometry: their contracts concern an actual inner four-group, without
requiring that four-group to be a family member.

The final `false_of_trapped_centralizer` discharges the three model premises
of `false_of_shared_model_geometry` using the shared unitary calculations.
They apply to arbitrary Hermitian models and all ambient two-extensions,
including p = 3 in the wreathed case and p = 5 in the semidihedral case.
Centralizer containment remains the independent input of this geometry;
the whole original family and its marked order-eight actor are retained.

Source: Aschbacher--Smith E.1.10(6)--(8), E.1.13 and E.1.14(7), pp.211--214;
A.2.3(2), p.33, and A.3.21, p.55. E.1.14(7) refers to Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- An odd commutator for any subgroup of a family actor is trapped when its
odd subgroup is normalized by the full Sylow centralizer of that subgroup.
The E-members used in the proof all have the original actor A. -/
theorem subactor_odd_commutator_le {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    (hcore : pCore 2 G = ⊥) {A B : Subgroup G}
    (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G)) (hBA : B ≤ A)
    {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) (X : Subgroup G) (hX : IsPGroup r X)
    (hn : (T : Subgroup G) ⊓ centralizer (B : Set G) ≤ normalizer (X : Set G)) :
    ⁅X, B⁆ ≤ d.overgroup := by
  have htau : tau (T : Subgroup G) A ≤
      (T : Subgroup G) ⊓ centralizer (B : Set G) := by
    intro t ht
    refine ⟨tau_le _ _ ht, mem_centralizer_iff.mpr ?_⟩
    intro b hb
    have hc := (mem_centralizerModulo_iff.mp ht).2 b (hBA hb)
    rw [hcore, mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  exact (commutator_mono le_rfl hBA).trans
    (InnerGeometry.tau_normalized_odd_commutator_le d hA hAT hr X hX (htau.trans hn))

/-- With intrinsic centralizer maximality, the obstruction traps both solvable
Sylow overgroups and the odd commutators for A ∩ F*(G). Only A is required
to belong to the original conjugation-invariant family. -/
theorem inner_section_constraints [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T) {A : Subgroup G}
    (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    {z : G} (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup)
    (hmax : IsCoatom ((centralizer ({z} : Set G)).subgroupOf (generalizedFitting G))) :
    d.overgroup = centralizer ({z} : Set G) ∧
      (∀ H : Subgroup G, (T : Subgroup G) ≤ H → Group.IsSolvable H →
        H ≤ centralizer ({z} : Set G)) ∧
      ∀ (r : ℕ), r.Prime → Odd r → ∀ X : Subgroup G, IsPGroup r X →
        (T : Subgroup G) ⊓ centralizer (A ⊓ generalizedFitting G : Set G) ≤
          normalizer (X : Set G) →
        ⁅X, A ⊓ generalizedFitting G⁆ ≤ centralizer ({z} : Set G) := by
  have hMC := InnerGeometry.overgroup_eq_centralizer_of_intrinsic_coatom
    (generalizedFitting G) hLT d z hTz hCM hmax
  refine ⟨hMC, ?_, ?_⟩
  · intro H hTH hs
    let := hs
    exact hMC ▸ solvable_sylow_overgroup_le d H hTH
  · have hcore : pCore 2 G = ⊥ :=
      (SimpleSocle.structure_of_sylow_supplement
        (nonabelian_of_model hp ho hmodel) T hLT).2.2.1
    intro r hr ho X hX hn
    let : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)
    exact hMC ▸ subactor_odd_commutator_le d hcore hA hAT inf_le_left hr2 X hX hn

/-- Conditional application of the shared unitary model calculations to an
actual family actor with inner intersection of order four. The semidihedral
input is applied to that intersection; its commutator is controlled using A.
The final theorem below supplies all three model premises. -/
theorem false_of_shared_model_geometry [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T) {A : Subgroup G}
    (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hinner : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4)
    {z : G} (hzL : z ∈ generalizedFitting G) (hzA : z ∈ A)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup)
    (hmax : IsCoatom ((centralizer ({z} : Set G)).subgroupOf (generalizedFitting G)))
    (hwreathed : p % 4 = 3 → ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧
      Group.IsSolvable H ∧ ¬ H ≤ centralizer ({z} : Set G))
    (hsemidihedral : p % 4 = 1 → ∀ B : Subgroup G, IsElementaryAbelian 2 B →
      Nat.card B = 4 → B ≤ (T : Subgroup G) → B ≤ generalizedFitting G → z ∈ B →
      ∃ (r : ℕ) (X : Subgroup G), r.Prime ∧ Odd r ∧ IsPGroup r X ∧
        (T : Subgroup G) ⊓ centralizer (B : Set G) ≤ normalizer (X : Set G) ∧
        ¬ ⁅X, B⁆ ≤ centralizer ({z} : Set G)) : False := by
  obtain ⟨_, hsolvable, hcomm⟩ := inner_section_constraints hp ho hmodel hLT d
    hA hAT hTz hCM hmax
  have hcases : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.odd_iff.mp ho
    omega
  rcases hcases with h1 | h3
  · let := d.elementary.1 A hA
    let : IsElementaryAbelian 2 (A ⊓ generalizedFitting G : Subgroup G) :=
      IsElementaryAbelian.of_le (show A ⊓ generalizedFitting G ≤ A from inf_le_left)
    obtain ⟨r, X, hr, hro, hX, hn, hmove⟩ := hsemidihedral h1
      (A ⊓ generalizedFitting G) inferInstance hinner (inf_le_left.trans hAT)
      inf_le_right ⟨hzA, hzL⟩
    exact hmove (hcomm r hr hro X hX hn)
  · obtain ⟨H, hTH, hs, hmove⟩ := hwreathed h3
    exact hmove (hsolvable H hTH hs)

/-- The outer eight-actor geometry in E.1.14(7), given containment of the
marked involution centralizer. Intrinsic maximality and both congruence-specific
movement constructions follow from the actual projective unitary model.
The SQTK, outer-family and order-eight hypotheses are retained for the source
application; the geometric argument uses the marked inner four-section. -/
theorem false_of_trapped_centralizer [IsSimpleGroup (generalizedFitting G)]
    {κ : GroupClass} (_hG : IsSQTK κ G)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T)
    (_houter : ∀ B ∈ d.family, B ≤ (T : Subgroup G) → B ≠ ⊥ →
      ¬ B ≤ generalizedFitting G)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (_hne : A ≠ ⊥) (_hcard : Nat.card A = 8)
    (hinner : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G) (hzA : z ∈ A)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup) : False := by
  apply false_of_shared_model_geometry hp ho hmodel hLT d hA hAT hinner
    hzL hzA hTz hCM
  · exact InnerGeometry.ambient_centralizer_isCoatom_of_matrix_geometry hp ho
      (generalizedFitting G) hmodel z hzL hz
  · intro hmod
    exact InnerGeometry.WreathedNormalizer.exists_solvable_sylow_overgroup
      (generalizedFitting G) hLT hp ho hmod hmodel hz hzL (hAT hzA) hTz
  · intro hmod B hB hcard _hBT hBL hzB
    let := hB
    obtain ⟨r, hr, hro, X, hX, hn, hmove⟩ :=
      InnerGeometry.SemidihedralTorus.escape_of_isPSU
        (generalizedFitting G) hp ho hmod hmodel T B hcard hBL z hz hzB
    exact ⟨r, X, hr, hro, hX, hn, hmove⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
