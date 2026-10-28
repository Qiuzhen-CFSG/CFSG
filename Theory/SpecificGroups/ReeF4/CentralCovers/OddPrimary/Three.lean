module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Model
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Order
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Lifting

/-!
# The Ree three-primary configuration from a marked monomial embedding

The full unitary diagonal matrices supply a two-generator three-torus.
Its coordinate cycle gives a subgroup of order 3|q+1|₃²; the explicit
Ree order makes this subgroup Sylow after an injective embedding.
The coordinate transposition swaps its generators, and the ambient inverse
action completes every field of `ThreeSylowData` on the literal Ree carrier.
The lifting theorem then excludes three from a perfect central kernel.

The only extra geometric premise is `Three.MonomialRealization m`, whose
exceptional-descent construction remains open. This module therefore does
not yet assert unconditional existence of `ThreeSylowData m`.

Sources: GLS3 Example 2.6.3, Table 4.7.3A, and §6.1;
Aschbacher–Smith I.1.1–4, printed pp.407–408 of `refs/quasithin.pdf`.
-/

public noncomputable section

namespace ReeF4.CentralCovers.OddPrimary
open Subgroup Three
open BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The full matrix monomial realization and the permitted Ree order
formula supply the actual Sylow-three configuration, with arbitrary valuation. -/
theorem nonempty_threeSylowData_of_monomialRealization (m : ℕ)
    (horder : Nat.card (Model m) =
      (2 ^ (2 * m + 1)) ^ 12 * ((2 ^ (2 * m + 1)) ^ 6 + 1) *
        ((2 ^ (2 * m + 1)) ^ 4 - 1) * ((2 ^ (2 * m + 1)) ^ 3 + 1) *
          (2 ^ (2 * m + 1) - 1))
    (D : MonomialRealization m) : Nonempty (ThreeSylowData m) := by
  let J := Three.form m
  have hJ : J.form = 1 := Three.form_matrix m
  let C := OddThreeMatrix.primary J
  let T := (Unitary.torus J hJ).map D.embedding
  let S := (Unitary.torus J hJ ⊔ zpowers (Unitary.cycle J hJ)).map D.embedding
  have hcard : Nat.card S = Nat.card C ^ 2 * 3 := by
    change Nat.card ((Unitary.torus J hJ ⊔ zpowers (Unitary.cycle J hJ)).map D.embedding) = _
    rw [Subgroup.card_map_of_injective D.injective, Unitary.torus_join_card]
  have hC : Nat.card C = 3 ^ (2 ^ (2 * m + 1) + 1).factorization 3 :=
    OddThreeMatrix.primary_card J (quadraticField_card m) (form_conj m)
  have hS : IsPGroup 3 S := by
    apply IsPGroup.of_card (n := 2 * (2 ^ (2 * m + 1) + 1).factorization 3 + 1)
    rw [hcard, hC, ← pow_mul, pow_succ]
    congr 2
    omega
  obtain ⟨d, hcd, hd⟩ := OddThreeMatrix.primary_complement J
    (quadraticField_card m) (form_conj m)
  have hi : ¬ 3 ∣ S.index := index_prime_to_three_of_order (fieldSize_mod_three m)
    (Nat.card_pos (α := C)) hcd hd horder S hcard
  let P : Sylow 3 (Model m) := hS.toSylow hi
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hjoin : T ⊔ zpowers (D.embedding (Unitary.cycle J hJ)) = S := by
    change _ = (Unitary.torus J hJ ⊔ zpowers (Unitary.cycle J hJ)).map D.embedding
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  refine ⟨{
    sylow := P
    torus := T
    first := D.embedding (Unitary.diagonal J hJ (g, 1))
    second := D.embedding (Unitary.diagonal J hJ (1, g))
    cycle := D.embedding (Unitary.cycle J hJ)
    swap := D.embedding (Unitary.swap J hJ)
    inverter := D.inverter
    torus_generated := ?_
    generators_commute := ((Commute.all (g, (1 : C)) (1, g)).map
      (Unitary.diagonal J hJ)).map D.embedding
    swap_first := ?_
    swap_second := ?_
    sylow_generated := hjoin
    cycle_normalizes := ?_
    inverts_torus := ?_
    fixes_cycle := D.fixes_cycle }⟩
  · have hgen := congrArg (fun H : Subgroup (Unitary.monomial J hJ) => H.map D.embedding)
      (Unitary.torus_generated J hJ g hg)
    simpa only [MonoidHom.map_closure, Set.image_pair] using hgen
  · rw [← map_inv, ← map_mul, ← map_mul, Unitary.swap_diagonal]
  · rw [← map_inv, ← map_mul, ← map_mul, Unitary.swap_diagonal]
  · exact (Unitary.torus J hJ).le_normalizer_map D.embedding
      ⟨_, Unitary.cycle_normalizes J hJ, rfl⟩
  · rintro t ⟨u, ⟨a, rfl⟩, rfl⟩
    change D.inverter * D.embedding (Unitary.normDiagonal J hJ _) * D.inverter⁻¹ =
      (D.embedding (Unitary.normDiagonal J hJ _))⁻¹
    rw [D.inverts, map_inv, map_inv]

/-- Application to the literal perfect central covering map. The geometric
realization remains explicit until exceptional descent constructs it. -/
theorem not_three_dvd_kernel_of_monomialRealization (m : ℕ)
    (horder : Nat.card (Model m) =
      (2 ^ (2 * m + 1)) ^ 12 * ((2 ^ (2 * m + 1)) ^ 6 + 1) *
        ((2 ^ (2 * m + 1)) ^ 4 - 1) * ((2 ^ (2 * m + 1)) ^ 3 + 1) *
          (2 ^ (2 * m + 1) - 1))
    (D : MonomialRealization m) {E : Type*} [Group E] [Finite E]
    (c : PerfectCentralCovering.Cover E (Model m)) :
    ¬ 3 ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨A⟩ := nonempty_threeSylowData_of_monomialRealization m horder D
  exact A.not_three_dvd_kernel c

end ReeF4.CentralCovers.OddPrimary
