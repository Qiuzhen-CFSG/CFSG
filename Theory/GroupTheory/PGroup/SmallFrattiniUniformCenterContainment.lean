module
public import Theory.GroupTheory.PGroup.SmallFrattiniSingularCenter
public import Theory.GroupTheory.PGroup.SmallFrattiniSingularIndex
public import Theory.ElementaryAbelian.Join
public import Theory.Representation.UniformBinaryFiveSingularBound

/-!
# Center containment in large elementary subgroups of the uniform closure

For the marked five- or nine-point Frattini quadratic realization,
an elementary subgroup of index at most eight or sixteen contains the
whole center. The center is elementary by singularity of the radical.
If it is omitted, adjoining it halves the index. The five-point singular
subspace bound or the nine-point polar bound excludes this smaller index.
No central summand is removed and no group-order restriction is imposed.

This is the intrinsic input for the actual opposite G.2.3 subgroup in
the normal row of Aschbacher–Smith 14.2.16/F.1.12.
-/

public section
open Subgroup Module
open scoped IsMulCommutative
namespace SmallFrattini
variable {Q : Type*} [Group Q] [Finite Q]

private theorem index_join_center_double_le
    (A : Subgroup Q) (hne : ¬ center Q ≤ A) :
    2 * (A ⊔ center Q).index ≤ A.index := by
  let C := A ⊔ center Q
  have h0 : A.relIndex C ≠ 0 := (A.subgroupOf C).index_ne_zero_of_finite
  have h1 : A.relIndex C ≠ 1 := by
    intro he
    exact hne (le_sup_right.trans (relIndex_eq_one.mp he))
  have h2 : 2 ≤ A.relIndex C := by omega
  have hh := relIndex_mul_index (show A ≤ C from le_sup_left)
  nlinarith

/-- The literal uniform quadratic Frattini realization forces every
sufficiently large elementary subgroup to contain the entire center. -/
theorem center_le_elementary_of_uniform_quadratic_quotient
    (htwo : IsPGroup 2 Q) (hphi : Nat.card (frattini Q) = 2) (n : ℕ) :
    letI := quotientElementary htwo
    ∀ (f : UniformBinaryPolar.V n →ₗ[ZMod 2] Additive (Q ⧸ frattini Q)),
      Function.Surjective f →
      (quotientBilinearForm htwo hphi).comp f f = UniformBinaryPolar.form n →
      (∀ i, quotientQuadraticForm htwo hphi (f (Pi.single i 1)) = 0) →
      ∀ (A : Subgroup Q) [IsElementaryAbelian 2 A],
        ((n = 5 ∧ A.index ≤ 8) ∨ (n = 9 ∧ A.index ≤ 16)) → center Q ≤ A := by
  let := quotientElementary htwo
  intro f hf hp hcoord A hA hindex
  have hn : n = 5 ∨ n = 9 := hindex.imp And.left And.left
  let := center_elementary_of_uniform_quadratic_quotient htwo hphi n hn f hf hp hcoord
  let C := A ⊔ center Q
  let : IsElementaryAbelian 2 C :=
    IsElementaryAbelian.sup_of_le_centralizer (center_le_centralizer (A : Set Q))
  by_contra hne
  have hi := index_join_center_double_le A hne
  rcases hindex with ⟨rfl,hindex⟩ | ⟨rfl,hindex⟩
  · have hCindex : C.index ≤ 2^2 := by dsimp [C]; omega
    obtain ⟨E,hE,_,hd⟩ := exists_totallySingular_of_index htwo hphi C 2 hCindex
    have hpolar : (quotientQuadraticForm htwo hphi).polarBilin.compl₁₂ f f =
        UniformBinaryPolar.form 5 := by
      rw [quotientQuadraticForm_polar]
      exact hp
    have hh := UniformBinaryPolar.five_orbit_singular_codimension_ge_three
      (quotientQuadraticForm htwo hphi) f hpolar hcoord E hE
    omega
  · have hCindex : C.index ≤ 2^3 := by dsimp [C]; omega
    obtain ⟨E,_,hE,hd⟩ := exists_totallySingular_of_index htwo hphi C 3 hCindex
    have hh := UniformBinaryPolar.orbit_degree_bound
      (quotientBilinearForm htwo hphi) f
      (fun x y => (congrArg (fun B : LinearMap.BilinForm (ZMod 2)
        (UniformBinaryPolar.V 9) => B x y) hp).symm) E hE 3 hd
    omega
end SmallFrattini
