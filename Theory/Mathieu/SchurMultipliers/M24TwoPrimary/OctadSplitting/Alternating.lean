module

public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.Reduction
public import Theory.Alternating.theorem_5_2_3

/-!
# Splitting an alternating double extension at a root involution

An involutory lift of a double transposition forces the derived kernel of a
central double extension of A₈ to vanish. Conjugacy of the actual root
involutions and equality of squares in each central fiber give the root-square
hypothesis of the existing Schur calculation. The inverse of the derived
projection is a section. Finite universe reduction and point relabeling retain
the literal projection equation.

Source: GLS3, Theorem 5.2.3 and Proposition 5.2.4; the octad application is
part of Aschbacher–Smith I.1.3, printed p.407.
-/

public section
open Subgroup GLS3.Chapter5 GLS3.Chapter5.SchurPresentation
open Equiv Equiv.Perm
namespace Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
noncomputable section

private theorem square_eq_of_same_image {E A : Type*} [Group E] [Group A]
    (f : E →* A) (hc : f.ker ≤ center E) (hcard : Nat.card f.ker = 2)
    {x y : E} (hxy : f x = f y) : x ^ 2 = y ^ 2 := by
  have hk : x * y⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  have hcomm : Commute (x * y⁻¹) y := (mem_center_iff.mp (hc hk) y).symm
  have hpow := hcomm.mul_pow 2
  simpa only [inv_mul_cancel_right, mul_inv_cancel_right,
    DoubleCoverUniqueness.ker_pow_two_eq_one f hcard hk, one_mul] using hpow

private theorem alternating_eight_section_small {E : Type} [Group E] [Finite E]
    (f : E →* alternatingGroup (Fin 8)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hcard : Nat.card f.ker = 2)
    (x : E) (hx : x ^ 2 = 1) (hroot : (f x).val.support.card = 4) :
    ∃ s : alternatingGroup (Fin 8) →* E, f.comp s = MonoidHom.id _ := by
  let D := _root_.commutator E
  let fD := f.comp D.subtype
  have hdcard : Nat.card fD.ker ≤ 2 := by
    rw [← hcard]
    exact Nat.card_le_card_of_injective
      (fun z : fD.ker => (⟨z.val.val, z.property⟩ : f.ker))
      (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => z.val) h)))
  have hker : fD.ker = ⊥ := by
    apply derivedKernel_eq_bot_of_root_lifts_sq_one 3 f hf hc hdcard
    intro u hu
    let t : alternatingGroup (Fin 8) :=
      ⟨RootFourSubgroup.rho1 3, RootFourSubgroup.rho1_mem_alternating 3⟩
    have ht2 : t.val ^ 2 = 1 := by
      simpa only [t, pow_two] using RootFourSubgroup.rho1_sq 3
    have htcard : t.val.support.card = 4 := by decide +kernel
    have hconj : IsConj (f x) t := by
      apply alternating_involution_isConj_of_card_support_eq
      · exact congrArg Subtype.val (show f x ^ 2 = 1 by rw [← map_pow, hx, map_one])
      · exact ht2
      · intro he
        have : (f x).val.support.card = 0 := by rw [he]; simp
        omega
      · exact hroot.trans htcard.symm
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    obtain ⟨b, hb⟩ := hf a
    have he : f (b * x * b⁻¹) = f u.val := by
      rw [map_mul, map_mul, map_inv, hb]
      exact ha.trans hu.symm
    have hs := square_eq_of_same_image f hc hcard he
    have hy : (b * x * b⁻¹) ^ 2 = 1 := by
      change ((MulAut.conj b) x) ^ 2 = 1
      rw [← map_pow, hx, map_one]
    exact Subtype.ext (hs.symm.trans hy)
  have hfs : Function.Surjective fD := by
    have hm : D.map f = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
      exact Group.IsPerfect.commutator_eq_top
    intro a
    obtain ⟨y, hy, hya⟩ := (show a ∈ D.map f by rw [hm]; trivial)
    exact ⟨⟨y, hy⟩, hya⟩
  let e : D ≃* alternatingGroup (Fin 8) :=
    MulEquiv.ofBijective fD ⟨fD.ker_eq_bot_iff.mp hker, hfs⟩
  refine ⟨D.subtype.comp e.symm.toMonoidHom, ?_⟩
  exact MonoidHom.ext (fun a => e.apply_symm_apply a)

/-- An involutory double-transposition lift splits a central double extension
of the eight-point alternating group, in any universe. -/
theorem alternating_eight_section {E : Type*} [Group E] [Finite E]
    (f : E →* alternatingGroup (Fin 8)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hcard : Nat.card f.ker = 2)
    (x : E) (hx : x ^ 2 = 1) (hroot : (f x).val.support.card = 4) :
    ∃ s : alternatingGroup (Fin 8) →* E, f.comp s = MonoidHom.id _ := by
  obtain ⟨U, iU, finU, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} E
  let := iU
  let := finU
  let fU := f.comp e.symm.toMonoidHom
  have hU : Function.Surjective fU := hf.comp e.symm.surjective
  have hcU : fU.ker ≤ center U := by
    intro z hz
    rw [mem_center_iff]
    intro y
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact mem_center_iff.mp (hc hz) (e.symm y)
  let eker : fU.ker ≃ f.ker := {
    toFun := fun z => ⟨e.symm z, z.property⟩
    invFun := fun z => ⟨e z, by
      change f (e.symm (e z)) = 1
      rw [e.symm_apply_apply]
      exact z.property⟩
    left_inv := fun z => Subtype.ext (e.apply_symm_apply z)
    right_inv := fun z => Subtype.ext (e.symm_apply_apply z) }
  have hkU : Nat.card fU.ker = 2 := (Nat.card_congr eker).trans hcard
  obtain ⟨s, hs⟩ := alternating_eight_section_small fU hU hcU hkU (e x)
    (by rw [← map_pow, hx, map_one]) (by simpa [fU] using hroot)
  refine ⟨e.symm.toMonoidHom.comp s, ?_⟩
  exact hs

/-- The same splitting test on any specified eight-element point set. -/
theorem alternating_octad_section {E α : Type*} [Group E] [Finite E]
    [Fintype α] [DecidableEq α] (hα : Fintype.card α = 8)
    (f : E →* alternatingGroup α) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hcard : Nat.card f.ker = 2)
    (x : E) (hx : x ^ 2 = 1) (hroot : (f x).val.cycleType = {2, 2}) :
    ∃ s : alternatingGroup α →* E, f.comp s = MonoidHom.id _ := by
  let e : α ≃ Fin 8 := Fintype.equivFinOfCardEq hα
  let a := e.altCongrHom
  let F := a.toMonoidHom.comp f
  have hker : F.ker = f.ker := by
    ext z
    change a (f z) = 1 ↔ f z = 1
    exact map_eq_one_iff a a.injective
  have hsupp : (F x).val.support = (f x).val.support.map e.toEmbedding := by
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [F, a, Equiv.altCongrHom_apply_coe, Equiv.permCongr_apply, mem_support]
  have hrootF : (F x).val.support.card = 4 := by
    rw [hsupp, Finset.card_map, ← sum_cycleType, hroot]
    decide
  obtain ⟨s, hs⟩ := alternating_eight_section F (a.surjective.comp hf)
    (by rw [hker]; exact hc) (hker ▸ hcard) x hx hrootF
  refine ⟨s.comp a.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro y
  apply a.injective
  exact DFunLike.congr_fun hs (a y)

end
end Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
