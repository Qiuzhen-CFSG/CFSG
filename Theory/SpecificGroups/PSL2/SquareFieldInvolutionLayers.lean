module

public import GorensteinWalter.PGammaL2PureSemilinear
public import GorensteinWalter.PGammaL2OuterProduct
public import Theory.FieldTheory.FiniteAutomorphismOrder
/-!
# The quadratic semilinear involution layers

Projective Hilbert 90 conjugates a field involution to its pure
coefficient automorphism. The actual outer quotient makes its linear
part inner. Such an involution and any non-inner linear coordinate above
PSL₂ generate the full quadratic semilinear group.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
/-- A semilinear involution with nontrivial field part has inner linear part. -/
theorem semilinear_involution_left_mem_psl
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (x : PGammaL2 F)
    (hx : orderOf x = 2) (hfield : x.right ≠ 1) :
    x.left ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  let : Fact (IsOddPrimePower (Nat.card F)) := ⟨hF⟩
  let J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  have hc : Nat.card (PGL2 F ⧸ J) = 2 := pgl2_psl2Range_index_eq_two F hF
  let : IsCyclic (PGL2 F ⧸ J) := isCyclic_of_prime_card hc
  let : CommGroup (PGL2 F ⧸ J) := IsCyclic.commGroup
  let q : PGammaL2 F →* PGL2 F ⧸ J := (MonoidHom.fst _ _).comp (pGammaL2OuterProduct F)
  obtain ⟨c, he⟩ := projective_semilinear_involution_conj_inr hF x hx hfield
  have hq := congrArg q he
  have hqr : q (SemidirectProduct.inr x.right) = 1 := rfl
  rw [map_mul, map_mul, map_inv, hqr] at hq
  have hq0 : q x = 1 := by
    simpa only [mul_assoc, mul_left_comm, inv_mul_cancel, mul_one] using hq
  change QuotientGroup.mk' J x.left = 1 at hq0
  exact (QuotientGroup.eq_one_iff x.left).mp hq0
/-- A subgroup above PSL₂ in a quadratic semilinear group which contains both
a field involution and a non-inner linear coordinate is the full group. -/
theorem semilinear_subgroup_eq_top_of_field_involution_and_outer
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (A : Subgroup (PGammaL2 F)) (hA : pGammaL2PSLRange F ≤ A)
    (x : PGammaL2 F) (hxA : x ∈ A) (hx : orderOf x = 2) (hfield : x.right ≠ 1)
    (y : PGammaL2 F) (hyA : y ∈ A)
    (hy : y.left ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    A = ⊤ := by
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
  have hxinner := semilinear_involution_left_mem_psl hodd x hx hfield
  have hxin : (SemidirectProduct.inl x.left : PGammaL2 F) ∈ A := by
    obtain ⟨a, ha⟩ := hxinner
    exact hA ⟨a, congrArg SemidirectProduct.inl ha⟩
  have hxfield : (SemidirectProduct.inr x.right : PGammaL2 F) ∈ A := by
    have hh := A.mul_mem (A.inv_mem hxin) hxA
    nth_rw 2 [← SemidirectProduct.inl_left_mul_inr_right x] at hh
    simpa only [inv_mul_cancel_left] using hh
  have hfields (σ : F ≃+* F) : (SemidirectProduct.inr σ : PGammaL2 F) ∈ A := by
    by_cases hσ : σ = 1
    · simpa only [hσ, map_one] using A.one_mem
    · obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : F ≃+* F)).mp
        (FiniteField.card_ringAut_of_card_prime_pow (Fact.out : p.Prime) hF)
      have he : σ = x.right := (hz σ hσ).trans (hz x.right hfield).symm
      exact he ▸ hxfield
  let J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  let L := A.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hJL : J ≤ L := by
    rintro _ ⟨a, rfl⟩
    exact hA ⟨a, rfl⟩
  have hyL : y.left ∈ L := by
    have hh := A.mul_mem hyA (A.inv_mem (hfields y.right))
    nth_rw 1 [← SemidirectProduct.inl_left_mul_inr_right y] at hh
    rw [mul_inv_cancel_right] at hh
    exact hh
  have hne : J ≠ L := by
    intro he
    apply hy
    change y.left ∈ J
    rw [he]
    exact hyL
  have hidx : J.index = 2 := pgl2_psl2Range_index_eq_two F hodd
  have hlt : L.index < 2 := by
    simpa only [hidx] using index_strictAnti (lt_of_le_of_ne hJL hne)
  have hpos : 0 < L.index := Nat.card_pos
  have hL : L = ⊤ := index_eq_one.mp (by omega)
  apply top_unique
  intro a _
  rw [← SemidirectProduct.inl_left_mul_inr_right a]
  exact A.mul_mem (show a.left ∈ L from hL ▸ mem_top _) (hfields a.right)
end Theory.PSL2
