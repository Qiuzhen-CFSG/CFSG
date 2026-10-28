module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.SquareSylow
public import Theory.SpecificGroups.PSL2.OddSylowFixers
public import Theory.FieldTheory.QuadraticFrobenius
public import Theory.SpecificGroups.PSL2.OuterSolvable.Actions

/-!
# The actual Frobenius extension in the split-sixteen branch

A central involution of the original Sylow outside the component fixes its
Sylow intersection pointwise. Faithful conjugation on the centerless
component makes its action a noninner involution. The actual semilinear
coverage and projective Hilbert 90 identify that action, after changing
the component marking, with the unique quadratic Frobenius. The selected
ambient involution and its generation of the extension are retained.

Source: Aschbacher--Smith F.6.18(8), printed p.310. The valid component
congruence is three or five modulo eight; no stronger residue is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

/-- The coefficient action is the actual prime Frobenius, on a marking of
the original normal component and an involution of the original Sylow. -/
theorem square_psl_component_frobenius_action
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hFstar : generalizedFitting G = K)
    (hquot : IsPGroup 2 (G ⧸ K))
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (j : K ≃* PSL(2,F)) :
    ∃ (eK : K ≃* PSL(2,F)) (σ : F ≃+* F) (t : G),
      (∀ x, σ x = x ^ p) ∧ t ∈ T ∧ orderOf t = 2 ∧ t ∉ K ∧
      K ⊔ zpowers t = ⊤ ∧
      ∀ k : K, eK (MulAut.conjNormal t k) = GorensteinWalter.psl2FieldAut F σ (eK k) := by
  have hm : ClassicalGroup.IsPSL K 2 (p ^ 2) :=
    ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩
  obtain ⟨t, ht, hto, htout, hgen, hfixT⟩ :=
    square_psl_component_central_involution T eT K hquot Fact.out ho hm
  have hZ : center K = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hz := (Subgroup.centerCongr j ⟨x, hx⟩).property
    change j x ∈ center PSL(2,F) at hz
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hz
    exact j.injective (hz.trans (map_one j).symm)
  have hC : centralizer (K : Set G) = ⊥ := by
    have hle : centralizer (K : Set G) ≤ K := by
      simpa only [hFstar] using centralizer_generalizedFitting_le G
    apply le_bot_iff.mp
    intro x hx
    have hz : (⟨x, hle hx⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    rw [hZ, mem_bot] at hz
    exact congrArg Subtype.val hz
  let a : G →* MulAut PSL(2,F) :=
    (MulAut.congr j).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut K)
  have ha : Function.Injective a := (MulAut.congr j).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hC)
  have hat : orderOf (a t) = 2 := (orderOf_injective a ha t).trans hto
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  let U := S.mapSurjective (f := j.toMonoidHom) j.surjective
  have hfix : ∀ x ∈ U, a t x = x := by
    rintro x ⟨k, hk, rfl⟩
    have hkT : (k : G) ∈ (T : Subgroup G) := by
      change k ∈ (T : Subgroup G).subgroupOf K
      exact hS ▸ hk
    have hkt : MulAut.conjNormal t k = k := by
      apply Subtype.ext
      change t * (k : G) * t⁻¹ = (k : G)
      rw [hfixT k hkT, mul_inv_cancel_right]
    change j (MulAut.conjNormal t (j.symm (j k))) = j k
    rw [j.symm_apply_apply, hkt]
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 2, Fact.out, ho, by decide, hF⟩
  have hlarge : 3 < Nat.card F := by
    have hp2 := (Fact.out : p.Prime).two_le
    rw [hF]
    nlinarith
  rcases Theory.PSL2.odd_sylow_fixed_involution_inner_or_field hodd hlarge U (a t) hat hfix
    with ⟨x, hx⟩ | ⟨σ, β, hσ, hβ⟩
  · have hk : a (j.symm x : G) = MulAut.conj x := by
      change MulAut.congr j (MulAut.conjNormal (H := K) (j.symm x).val) = _
      rw [MulAut.conjNormal_val, MulAut.congr_conj, j.apply_symm_apply]
    have htval := ha (hx.trans hk.symm)
    exact (htout (htval ▸ (j.symm x).property)).elim
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := 2) (by
      simpa [Nat.card_eq_fintype_card] using hF)
    have heq := FiniteField.involution_eq_frobenius_of_card_square hF σ hσ
    refine ⟨j.trans β, σ, t, ?_, ht, hto, htout, hgen, ?_⟩
    · intro x
      rw [heq]
      rfl
    · intro k
      have hh := DFunLike.congr_fun hβ (β (j k))
      change β (a t (β.symm (β (j k)))) = GorensteinWalter.psl2FieldAut F σ (β (j k)) at hh
      rw [β.symm_apply_apply] at hh
      change β (j (MulAut.conjNormal t (j.symm (j k)))) = _ at hh
      simpa only [j.symm_apply_apply, MulEquiv.trans_apply] using hh

end CFSG.Quasithin.ChapterF.SourceAssembly
