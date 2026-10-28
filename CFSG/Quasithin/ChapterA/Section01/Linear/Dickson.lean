module

public import Glauberman.DicksonClassification
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic


/-!
# Dickson's classification for Appendix A

This is Aschbacher–Smith A.1.3, printed p.20, with the exceptional-parameter
corrections from its cited Huppert II.8.27. The local English translation,
*Finite Groups I*, printed p.223, includes odd characteristic for A₄,
uses `p^(2*f) - 1` for S₄, and includes characteristic five for A₅.
The uncorrected restrictions printed in A.1.3 are not asserted here.

The proved Dickson classification supplies the actual exceptional and
subfield isomorphisms. Containment in a Sylow subgroup, whose order is the
field order, bounds the elementary abelian ranks. Here rank `m` is expressed
by order `p^m`. Complementary normal and cyclic subgroups give an actual
semidirect-product equivalence, not merely an extension-shape label.
The affine divisibilities are those of A.1.3(7), proved by the existing
Dickson development.
-/

namespace CFSG.Quasithin.ChapterA

open BenderSuzuki.MatrixGroups
open scoped Pointwise

private theorem pSubgroup_card_le
    {F : Type*} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (hH : IsPGroup p H) : Nat.card H ≤ p ^ f := by
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  obtain ⟨e⟩ := Glauberman.Dickson.huppert_II_8_2_a_sylow_equiv_additive hFcard Q
  calc
    Nat.card H ≤ Nat.card Q := Nat.card_le_card_of_injective
      (Subgroup.inclusion hQ) (Subgroup.inclusion_injective hQ)
    _ = Nat.card (Multiplicative F) := Nat.card_congr e.symm.toEquiv
    _ = p ^ f := hFcard

private theorem semidirect_equiv {G : Type*} [Group G]
    (N C : Subgroup G) [N.Normal] (hd : Disjoint N C) (hs : N ⊔ C = ⊤) :
    ∃ φ : C →* MulAut N, Nonempty (G ≃* N ⋊[φ] C) := by
  have hcompl : N.IsComplement' C :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd (by
      rw [← Subgroup.normal_mul N C, hs, Subgroup.coe_top])
  exact ⟨_, ⟨(SemidirectProduct.mulEquivSubgroup hcompl).symm⟩⟩

/-- A.1.3 with the Huppert exceptional-parameter corrections, the elementary
abelian rank bounds, and actual cyclic, dihedral, exceptional, semidirect
and subfield isomorphisms. This is an exhaustive list of necessary alternatives;
it does not assert existence for every parameter satisfying the restrictions. -/
public theorem lemma_A_1_3_corrected
    {F : Type*} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F)) :
    (IsElementaryAbelian p H ∧ ∃ m ≤ f, Nat.card H = p ^ m) ∨
      (∃ z : ℕ,
        (z ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∨
          z ∣ (p ^ f + 1) / Nat.gcd (p ^ f - 1) 2) ∧
        Nat.card H = z ∧ IsCyclic H ∧ Nonempty (H ≃* Multiplicative (ZMod z))) ∨
      (∃ z : ℕ,
        (z ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∨
          z ∣ (p ^ f + 1) / Nat.gcd (p ^ f - 1) 2) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
      ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
      (∃ m t : ℕ, m ≤ f ∧
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup H,
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤ ∧
          ∃ φ : C →* MulAut N, Nonempty (H ≃* N ⋊[φ] C)) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
        Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∨
      (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by
  have hclass := Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFcard H
  rw [hFcard] at hclass
  rcases hclass with he | hc | hd | ha4 | hs4 | ha5 | haff | hpsl | hpgl
  · let : IsElementaryAbelian p H := he
    have hpH := IsElementaryAbelian.isPGroup p H
    obtain ⟨m, hm⟩ := hpH.exists_card_eq
    have hb := pSubgroup_card_le hFcard H hpH
    rw [hm] at hb
    exact Or.inl ⟨he, m, (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hb, hm⟩
  · rcases hc with ⟨z, hz, hcard, hcyc⟩
    have hiso := (zmodCyclicMulEquiv hcyc).symm
    rw [hcard] at hiso
    exact Or.inr (Or.inl ⟨z, hz, hcard, hcyc, ⟨hiso⟩⟩)
  · exact Or.inr (Or.inr (Or.inl hd))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha5)))))
  · rcases haff with ⟨m, t, ht, htf, N, C, hNnorm, hNelem, hNcard, hCcyc, hCcard, hd, hs⟩
    let : N.Normal := hNnorm
    let : IsElementaryAbelian p N := hNelem
    have hb := pSubgroup_card_le hFcard (N.map H.subtype)
      ((IsElementaryAbelian.isPGroup p N).map H.subtype)
    have he := Nat.card_congr (N.equivMapOfInjective H.subtype Subtype.val_injective).toEquiv
    rw [← he, hNcard] at hb
    have hm := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hb
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, t, hm, ht, htf, N, C, hNnorm, hNelem, hNcard, hCcyc, hCcard, hd, hs,
        semidirect_equiv N C hd hs⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpsl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpgl)))))))

end CFSG.Quasithin.ChapterA
