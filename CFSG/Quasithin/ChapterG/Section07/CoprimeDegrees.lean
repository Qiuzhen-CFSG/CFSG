module

public import Theory.Representation.BinaryCoprimeDegree
import Mathlib.Tactic

/-!
# Coprime degree bounds in G.7

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, G.7.1(2),(3), printed p.347 (PDF p.358), and the
triple-cover A₇ argument, printed p.349 (PDF p.360).

The faithful lower bound follows by choosing an irreducible constituent on
which the extraspecial center acts nontrivially. The exact irreducible degree
and the separate central-fixed-point-free divisibility theorem justify the
stronger fact used later for A₇. For G.7.1(3), the elementary abelian
character-space decomposition gives the orbit bound and the equality clause
for fixed spaces in the original module. The source minimum is attained;
its existence forces nontriviality, and it exists for every nontrivial P by
`Representation.BinaryCoprimeDegree.exists_minimumHyperplaneOrbit`.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section07

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- G.7.1(2): an extraspecial subgroup of order `p³` forces degree at least
`p * d(p)` in every faithful binary representation. -/
theorem lemma_G_7_1_2 (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (P : Subgroup G) [IsExtraspecial p P] (hP : Nat.card P = p ^ 3) :
    p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  exact Representation.BinaryCoprimeDegree.extraspecial_finrank_le hp2
    (ρ.comp P.subtype) (hρ.comp Subtype.val_injective) hP

/-- The orbit-lower-bound version of G.7.1(3), including the equality clause
for every nonzero hyperplane fixed space in the original module. -/
theorem lemma_G_7_1_3_of_orbit_lower_bound (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (P : Subgroup G) [IsElementaryAbelian p P] (hP : P ≠ ⊥) (n : ℕ)
    (hn : ∀ H : Subgroup P, H.index = p →
      n ≤ Nat.card (Representation.BinaryCoprimeDegree.normalizerHyperplaneOrbit P H)) :
    n * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V ∧
      (Module.finrank (ZMod 2) V = n * orderOf (2 : ZMod p) →
        ∀ H : Subgroup P, H.index = p →
          Representation.invariants (ρ.comp (P.subtype.comp H.subtype)) ≠ ⊥ →
          Module.finrank (ZMod 2)
            (Representation.invariants (ρ.comp (P.subtype.comp H.subtype))) =
              orderOf (2 : ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  exact Representation.BinaryCoprimeDegree.hyperplane_orbit_degree ρ hρ hp2 P hP n hn

/-- G.7.1(3): the minimum length of an actual normalizer orbit on hyperplanes
bounds the binary degree; equality determines every nonzero hyperplane fixed
dimension. Attainment of the minimum excludes the trivial subgroup. -/
theorem lemma_G_7_1_3 (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (P : Subgroup G) [IsElementaryAbelian p P] {n : ℕ}
    (hn : Representation.BinaryCoprimeDegree.IsMinimumHyperplaneOrbit p P n) :
    n * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V ∧
      (Module.finrank (ZMod 2) V = n * orderOf (2 : ZMod p) →
        ∀ H : Subgroup P, H.index = p →
          Representation.invariants (ρ.comp (P.subtype.comp H.subtype)) ≠ ⊥ →
          Module.finrank (ZMod 2)
            (Representation.invariants (ρ.comp (P.subtype.comp H.subtype))) =
              orderOf (2 : ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  exact Representation.BinaryCoprimeDegree.hyperplane_orbit_degree_of_minimum ρ hρ hp2 P hn

/-- The exact extraspecial irreducible-degree assertion used in the proof of
G.7.3(3), stronger than the lower bound stated in G.7.1(2). -/
theorem extraspecial_irreducible_degree (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (P : Subgroup G) [IsExtraspecial p P] (hP : Nat.card P = p ^ 3)
    [Representation.IsIrreducible (ρ.comp P.subtype)] :
    Module.finrank (ZMod 2) V = p * orderOf (2 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  exact Representation.BinaryCoprimeDegree.extraspecial_irreducible_finrank hp2
    (ρ.comp P.subtype) (hρ.comp Subtype.val_injective) hP

/-- The divisibility used in the A₇ triple-cover case. The source assembly
must establish the vanishing of the central fixed space. -/
theorem six_dvd_degree_of_extraspecial_twentySeven
    (ρ : Representation (ZMod 2) G V) (P : Subgroup G) [IsExtraspecial 3 P]
    (hP : Nat.card P = 27)
    (hfix : Representation.invariants
      (ρ.comp (P.subtype.comp (Subgroup.center P).subtype)) = ⊥) :
    6 ∣ Module.finrank (ZMod 2) V :=
  Representation.BinaryCoprimeDegree.six_dvd_finrank_of_extraspecial_twentySeven
    (ρ.comp P.subtype) hP hfix

end CFSG.Quasithin.ChapterG.Section07
