module

public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Proper faithful extensions of prime-field PSL₂

For a field of prime order greater than three, the concrete PGL₂ conjugation
map is an isomorphism onto Aut(PSL₂), and the inner subgroup has index two.
The faithful action of a group on a normal PSL₂ subgroup contains those
inner automorphisms. If the subgroup is proper, its action image strictly
contains the inner group, hence equals the entire automorphism group.
The resulting PGL₂ equivalence preserves the given subgroup identification.

Source: the prime-field specialization of the semilinear automorphism
calculation used in Aschbacher--Smith F.6.18, printed p.310.
-/

public section
noncomputable section

open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- A proper normal prime-field PSL₂ subgroup with trivial centralizer
identifies the full ambient group with PGL₂, through the prescribed model. -/
theorem exists_pgl_equiv_of_proper_normal_prime_psl
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (hC : centralizer (K : Set G) = ⊥) (hproper : K ≠ ⊤)
    (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hF : Nat.card F = p) (eK : K ≃* PSL(2, F)) :
    ∃ eG : G ≃* PGL2 F, ∀ k : K,
      eG k = Matrix.ProjectiveSpecialLinearGroup.toPGL (eK k) := by
  let hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let hq : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, hodd, by decide, by simpa using hF⟩
  have hlarge : 3 < Nat.card F := by omega
  let eA : PGL2 F ≃* MulAut PSL(2, F) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 F hq hlarge)
      ⟨pgl2InnerAutPSL2_injective F hq hlarge,
        prime_card_pgl_coverage F hF hq hlarge⟩
  let a : G →* MulAut PSL(2, F) :=
    (MulAut.congr eK).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut K)
  have ha : Function.Injective a := (MulAut.congr eK).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hC)
  have haK (k : K) : a k = MulAut.conj (eK k) := by
    change MulAut.congr eK (MulAut.conjNormal (H := K) k.val) = _
    rw [MulAut.conjNormal_val, MulAut.congr_conj]
  let I := MulAut.innerSubgroup PSL(2, F)
  have hI : I ≤ a.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨eK.symm x, by rw [haK, eK.apply_symm_apply]⟩
  have hne : I ≠ a.range := by
    intro he
    apply hproper
    apply top_unique
    intro g _
    have hg : a g ∈ I := he.symm ▸ (show a g ∈ a.range from ⟨g, rfl⟩)
    obtain ⟨x, hx⟩ := hg
    have heq : a (eK.symm x : G) = a g := by
      rw [haK, eK.apply_symm_apply]
      exact hx
    exact (ha heq) ▸ (eK.symm x).property
  have hindex : I.index = 2 := prime_card_inner_index F hodd hp hF
  have hlt : a.range.index < 2 := by
    simpa only [hindex] using Subgroup.index_strictAnti (lt_of_le_of_ne hI hne)
  have hpos : 0 < a.range.index := Nat.card_pos
  have hsurj : Function.Surjective a := MonoidHom.range_eq_top.mp
    (Subgroup.index_eq_one.mp (by omega : a.range.index = 1))
  let e : G ≃* PGL2 F := (MulEquiv.ofBijective a ⟨ha, hsurj⟩).trans eA.symm
  refine ⟨e, fun k => ?_⟩
  apply eA.injective
  change eA (eA.symm (a k)) = eA (Matrix.ProjectiveSpecialLinearGroup.toPGL (eK k))
  rw [eA.apply_symm_apply, haK]
  exact (pgl2InnerAutPSL2_toPGL F hq hlarge (eK k)).symm

end Theory.PSL2
