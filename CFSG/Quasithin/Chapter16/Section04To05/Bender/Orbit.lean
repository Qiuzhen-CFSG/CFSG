module

public import CFSG.Quasithin.Chapter16.Section04To05.Basic
/-!
# The Sylow-fixed orbit obstruction

A subgroup containing a Sylow two-subgroup has odd index. Therefore the
orbit of an object fixed by that Sylow has odd cardinality. In the Bender
application the object is U_C and the group is the actual normalizer action.
This excludes alternatives (ii) and (iii) of GLS96 C.14.2, whose orbit sizes
are respectively two and a positive power of two. The moving conjugator
excludes alternative (i) separately.

Source: Aschbacher–Smith, Proposition 16.5.1, printed p.1194;
GLS, Number 2, Chapter C, Definition 14.1 and Proposition 14.2
(`refs/KGroup/GLS2/ChapterC.tex`).
-/

@[expose] public section

open Subgroup MulAction
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
variable {A W : Type*} [Group A] [Finite A] [MulAction A W]

/-- A Sylow-fixed object has an orbit of odd cardinality. -/
theorem orbit_odd_of_sylow_fixed (S : Sylow 2 A) (w : W)
    (hS : (S : Subgroup A) ≤ stabilizer A w) : Odd (orbit A w).ncard := by
  rw [← index_stabilizer, ← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact fun h => S.not_dvd_index (h.trans (index_dvd_of_le hS))

/-- In particular its orbit cannot have positive two-power cardinality. -/
theorem orbit_ne_two_power_of_sylow_fixed (S : Sylow 2 A) (w : W)
    (hS : (S : Subgroup A) ≤ stabilizer A w) {n : ℕ} (hn : 0 < n) :
    (orbit A w).ncard ≠ 2 ^ n := by
  intro he
  have ho := orbit_odd_of_sylow_fixed S w hS
  rw [he] at ho
  exact (Nat.not_even_iff_odd.mpr ho)
    (even_iff_two_dvd.mpr (dvd_pow_self 2 hn.ne'))
end CFSG.Quasithin.Chapter16.Intersections.Bender
