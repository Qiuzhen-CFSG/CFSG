module
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicApartment
public import Mathlib.Order.Atoms

/-!
# Exact rotation order on a periodic apartment

The stabilizer of a vertex class contains the image of the original vertex
stabilizer. If that image is maximal proper and some element moves the class,
the two subgroups coincide. This step requires maximality; disjointness of the
quotient kernel and the original stabilizer alone does not suffice.

For a line separated modulo its period 2n, a translation by minus two has
order exactly n in any quotient whose kernel is the fixer of the two marked
vertex classes. The proof calculates all powers using integer coordinates.
It neither identifies equivalence classes with kernel orbits nor assumes
that fixing the line implies fixing every quotient vertex.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.6)--(3.7), pp.77--80,
and the integer apartment coordinates following (14.2), p.211.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.GroupAction.CubicTree
variable {X V W : Type*} [Group X] [Group W] [MulAction X V]
variable (r : Setoid V) (hr : Invariant (X := X) r)

/-- The actual stabilizer under the faithful quotient action on vertex classes. -/
def classStabilizer (a : V) : Subgroup (X ⧸ quotientKernel r hr) :=
  (MulAction.stabilizer (Equiv.Perm (Quotient r)) (Quotient.mk r a)).comap
    (QuotientGroup.kerLift (quotientAction r hr))

/-- Membership retains the original action and the literal quotient map. -/
theorem mem_classStabilizer (g : X) (a : V) :
    QuotientGroup.mk' (quotientKernel r hr) g ∈ classStabilizer r hr a ↔ r (g • a) a := by
  change Quotient.mk r (g • a) = Quotient.mk r a ↔ _
  exact Quotient.eq

/-- A maximal endpoint image is the whole class stabilizer when the class moves. -/
theorem classStabilizer_eq_image (a : V)
    (hmax : IsCoatom ((MulAction.stabilizer X a).map
      (QuotientGroup.mk' (quotientKernel r hr))))
    (hmove : ∃ g : X, ¬ r (g • a) a) :
    classStabilizer r hr a = (MulAction.stabilizer X a).map
      (QuotientGroup.mk' (quotientKernel r hr)) := by
  have hle : (MulAction.stabilizer X a).map
      (QuotientGroup.mk' (quotientKernel r hr)) ≤ classStabilizer r hr a := by
    rintro _ ⟨g, hg, rfl⟩
    apply (mem_classStabilizer r hr g a).mpr
    change g • a = a at hg
    rw [hg]
  rcases hmax.le_iff.mp hle with ht | he
  · obtain ⟨g, hg⟩ := hmove
    exact (hg ((mem_classStabilizer r hr g a).mp (ht ▸ Subgroup.mem_top _))).elim
  · exact he

/-- A two-step rotation of a separated period-2n line has exact order n. -/
theorem orderOf_line_rotation {Γ : SimpleGraph V} (hΓ : Γ.IsAcyclic) (l : Line Γ)
    (n : ℕ) (hn : 0 < n) (hsep : Separated r Γ (2*n))
    (hperiod : ∀ i : ℤ, r (l.vertex (i+(2*n:ℕ))) (l.vertex i))
    (N : Subgroup X) (f : N →* W)
    (hker : ∀ g : N, f g = 1 ↔
      r ((g : X) • l.vertex 0) (l.vertex 0) ∧
      r ((g : X) • l.vertex 1) (l.vertex 1))
    (u : N) (hu : ∀ i : ℤ, (u : X) • l.vertex i = l.vertex (i-2)) :
    orderOf (f u) = n := by
  have hpow (k : ℕ) (i : ℤ) : ((u : X)^k) • l.vertex i = l.vertex (i-2*k) := by
    induction k generalizing i with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_smul, hu, ih]
      congr 1
      push_cast
      omega
  have hiff (k : ℕ) : (f u)^k = 1 ↔ n ∣ k := by
    rw [← map_pow, hker]
    simp only [Subgroup.coe_pow, hpow, line_related_iff_mod hΓ l r (2*n)
      (by omega) hsep hperiod]
    constructor
    · rintro ⟨hz, _⟩
      have hd : (2*(n:ℤ)) ∣ 2*(k:ℤ) := by
        have : (2*(n:ℤ)) ∣ -(2*(k:ℤ)) := by
          apply Int.dvd_of_emod_eq_zero
          simpa using hz
        exact Int.dvd_neg.mp this
      have : (n:ℤ) ∣ (k:ℤ) := (mul_dvd_mul_iff_left (by norm_num : (2:ℤ) ≠ 0)).mp hd
      exact Int.natCast_dvd_natCast.mp this
    · intro hk
      have hd : ((2*n : ℕ) : ℤ) ∣ 2*(k:ℤ) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          mul_dvd_mul_left (2:ℤ) (Int.natCast_dvd_natCast.mpr hk)
      have hm := Int.emod_eq_zero_of_dvd hd
      constructor <;> rw [Int.sub_emod, hm, sub_zero, Int.emod_emod]
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((hiff n).mpr (dvd_refl n))
  · exact (hiff (orderOf (f u))).mp (pow_orderOf_eq_one (f u))
end Theory.GroupTheory.WeakBNPair.RegularTree
