module

public import Theory.SpecificGroups.PSL2.SplitSubcentralizerLinearElementary
public import Theory.SpecificGroups.PSL2.SquareFieldSplitInnerMarking
public import Theory.GroupTheory.ElementaryCoreBoundTransport

/-!
# The complete intermediate semilinear centralizer bound

A field involution together with the source non-inner coordinate forces
the full quadratic semilinear group, whose actual centralizer bound is
proved. In the remaining case every elementary actor is linear, and the
inner square torus gives the same bound in the original intermediate
centralizer. No field-triviality or actor-placement conclusion is assumed.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
/-- The actual centralizer inside every source semilinear overgroup has the elementary bound. -/
theorem split_subcentralizer_elementary_card_le_two
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (A : Subgroup (PGammaL2 F)) (hA : pGammaL2PSLRange F ≤ A)
    (houter : ∃ y ∈ A, y.left ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    let C := centralizer ({(SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) : PGammaL2 F)} : Set (PGammaL2 F))
    let B := A.subgroupOf C
    ∀ T : Sylow 2 B, ∀ V : Subgroup B, V ≤ pCore 2 B →
      (T : Subgroup B) ≤ normalizer (V : Set B) → (∀ v ∈ V, v ^ 2 = 1) → Nat.card V ≤ 2 := by
  intro C B T V hV hVN hpow
  classical
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  let : Finite (PGammaL2 F) := Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right))
    (fun _ _ he => SemidirectProduct.ext (congrArg Prod.fst he) (congrArg Prod.snd he))
  by_cases hlinear : ∀ v ∈ V, v.val.val.right = 1
  · apply split_subcentralizer_linear_elementary_card_le_two ho hF hp A _ T V hV hVN hpow hlinear
    intro a
    obtain ⟨b, hb⟩ := full_split_torus_square_mem_psl a
    exact hA ⟨b, congrArg SemidirectProduct.inl hb⟩
  · push Not at hlinear
    obtain ⟨v, hv, hvf⟩ := hlinear
    have hvord : orderOf v.val.val = 2 := by
      apply orderOf_eq_prime
      · exact congrArg (fun a : B => a.val.val) (hpow v hv)
      · intro he
        exact hvf (congrArg SemidirectProduct.right he)
    obtain ⟨y, hy, hyo⟩ := houter
    have hAtop := semilinear_subgroup_eq_top_of_field_involution_and_outer ho hF A hA
      v.val.val v.property hvord hvf y hy hyo
    have hBtop : B = ⊤ := by
      change A.subgroupOf C = ⊤
      rw [hAtop, top_subgroupOf]
    let e : B ≃* C := (MulEquiv.subgroupCongr hBtop).trans topEquiv
    exact Theory.GroupTheory.elementary_core_bound_of_equiv e
      (split_centralizer_elementary_card_le_two ho hF hp) T V hV hVN hpow
end Theory.PSL2
