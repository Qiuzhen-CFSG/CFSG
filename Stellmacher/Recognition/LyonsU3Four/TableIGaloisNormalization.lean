module
public import Stellmacher.Recognition.LyonsU3Four.TableISignedDegreeTransport
import Mathlib.Tactic

/-!
# Galois normalization of repeated degree labels

When every z-value is positive, the relative Galois signs are positive as well.
A labeling by representatives and column-rotation steps then aligns the degrees:
send a printed row to the corresponding iterate of its representative under the
actual Galois permutation. Equality of two images forces equality of their rows,
hence equality of their steps; injectivity of the Galois iterate then identifies
the representatives. Finiteness makes this map a permutation.

This argument retains all equal rows with multiplicity and does not require the
Galois permutation itself to have order four. Signed degree transport carries
the numerical constraints through the resulting row permutation.
Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), §3 and Table I.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
open scoped BigOperators
variable {I : Type*} [Fintype I]

/-- The row rotation induced by the inverse of `galoisColumn`. -/
def rotateTableIRow (a : TableIRow) : TableIRow :=
  ![a 0, a 1, a 3, a 4, a 5, a 2]

omit [Fintype I] in
/-- Positive z-values remove all relative signs from the Galois action. -/
theorem SignedGaloisSymmetry.unsigned_of_zValue_pos
    {d : GeneralizedDecompositionData I} {r : I → ℤ}
    (hg : d.SignedGaloisSymmetry r) (hzpos : ∀ j, 0 < d.zValue j) :
    ∃ σ : Equiv.Perm I, ∀ j, r (σ j) = r j ∧
      d.tableIRow (σ j) = rotateTableIRow (d.tableIRow j) := by
  obtain ⟨σ, hσ⟩ := hg
  refine ⟨σ, fun j => ?_⟩
  obtain ⟨ε, hε, hr, ht, hz⟩ := hσ j
  have hzsum : d.zValue j = ε * d.zValue (σ j) := by
    simp only [zValue, Fin.sum_univ_succ]
    simp [hz, galoisColumn]
    ring
  have he : ε = 1 := by
    rcases sq_eq_one_iff.mp hε with he | he
    · exact he
    · have h1 := hzpos j
      have h2 := hzpos (σ j)
      rw [he] at hzsum
      omega
  simp only [he, one_mul] at hr ht hz
  refine ⟨hr.symm, ?_⟩
  funext k
  fin_cases k
  · exact ht.symm
  · exact (hz 0).symm
  · exact (hz 2).symm
  · exact (hz 3).symm
  · exact (hz 4).symm
  · exact (hz 1).symm

/-- A printed degree labeling described by representatives and Galois steps.
Equal matrix rows must have the same step. Together with the representative,
that step determines the row index, retaining the multiplicities of equal rows. -/
structure GaloisLabeling (d : GeneralizedDecompositionData I)
    (principal : I) (L : Type*) where
  label : I → L
  representative : L → I
  step : I → ℕ
  row_eq : ∀ j, d.tableIRow j =
    rotateTableIRow^[step j] (d.tableIRow (representative (label j)))
  step_eq : ∀ j k, d.tableIRow j = d.tableIRow k → step j = step k
  coordinates_injective : ∀ j k, step j = step k →
    representative (label j) = representative (label k) → j = k
  principal_step : step principal = 0
  principal_representative : representative (label principal) = principal

namespace GaloisLabeling
variable {d : GeneralizedDecompositionData I} {principal : I} {L : Type*}

/-- Align all copies of each column orbit using the same Galois permutation.
This allows equal-column rows to be permuted independently of printed blocks. -/
theorem exists_normalizing_perm (a : GaloisLabeling d principal L)
    {r : I → ℤ} (hg : d.SignedGaloisSymmetry r) (hz : ∀ j, 0 < d.zValue j) :
    ∃ e : Equiv.Perm I, e principal = principal ∧
      ∀ j, d.tableIRow (e j) = d.tableIRow j ∧
        r (e j) = r (a.representative (a.label j)) := by
  classical
  obtain ⟨σ, hσ⟩ := hg.unsigned_of_zValue_pos hz
  have hi : ∀ n j, r ((σ : I → I)^[n] j) = r j ∧
      d.tableIRow ((σ : I → I)^[n] j) = rotateTableIRow^[n] (d.tableIRow j) := by
    intro n
    induction n with
    | zero => intro j; exact ⟨rfl, rfl⟩
    | succ n ih =>
      intro j
      simp only [Function.iterate_succ_apply']
      exact ⟨(hσ _).1.trans (ih j).1, (hσ _).2.trans (congrArg _ (ih j).2)⟩
  let f : I → I := fun j => (σ : I → I)^[a.step j] (a.representative (a.label j))
  have hf : ∀ j, d.tableIRow (f j) = d.tableIRow j :=
    fun j => (hi _ _).2.trans (a.row_eq j).symm
  have hinj : Function.Injective f := by
    intro j k hjk
    have hs : a.step j = a.step k := a.step_eq j k
      ((hf j).symm.trans ((congrArg d.tableIRow hjk).trans (hf k)))
    apply a.coordinates_injective j k hs
    apply σ.injective.iterate (a.step k)
    simpa only [f, hs] using hjk
  let e : Equiv.Perm I := Equiv.ofBijective f (⟨hinj, Finite.surjective_of_injective hinj⟩)
  refine ⟨e, ?_, fun j => ⟨hf j, (hi _ _).1⟩⟩
  change f principal = principal
  simp [f, a.principal_step, a.principal_representative]

/-- All three numerical constraint packages admit the printed repeated labels.
The coordinates are the degrees at the chosen representatives. -/
theorem normalize (a : GaloisLabeling d principal L)
    {r : I → ℤ} {g c z : ℕ} (hz : ∀ j, 0 < d.zValue j)
    (hd : d.DegreeConstraints principal r) (ho : d.OrderConstraints r g c z)
    (hp : d.PrimeConstraints r g) :
    ∃ x : L → ℤ, d.DegreeConstraints principal (fun j => x (a.label j)) ∧
      d.OrderConstraints (fun j => x (a.label j)) g c z ∧
      d.PrimeConstraints (fun j => x (a.label j)) g := by
  obtain ⟨e, he, hm⟩ := a.exists_normalizing_perm hd.galois_symmetry hz
  let x : L → ℤ := fun l => r (a.representative l)
  let h : SignedDegreeEquiv d d (fun j => x (a.label j)) r := {
    equiv := e
    sign := fun _ => 1
    sign_sq := fun _ => by norm_num
    degree_eq := fun j => by simpa [x] using (hm j).2
    t_eq := fun j => by simpa using congrFun (hm j).1 0
    z_eq := fun j i => by simpa using congrFun (hm j).1 i.succ }
  have he' : h.symm.equiv principal = principal := by
    change e.symm principal = principal
    exact e.symm_apply_eq.mpr he.symm
  refine ⟨x, ?_, h.symm.orderConstraints ho, h.symm.primeConstraints hp⟩
  have hh := h.symm.degreeConstraints (principal := principal) (by rfl) hd
  rw [he'] at hh
  exact hh

end GaloisLabeling
end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
