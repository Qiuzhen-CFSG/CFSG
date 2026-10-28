module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Gluing an equivalence across a normal supplement

Compatible maps on a normal subgroup N and a supplement M descend from
N ⋊ M. Agreement on N ∩ M kills the kernel of the product map; the
exact inverse-image intersection proves injectivity. Generation on the
target gives surjectivity. Both maps are retained pointwise.

Application: the marked centralizer extension in Aschbacher,
“A 2-local characterization of M12”, Proposition 3.3, printed p.38.
-/

public section
open Subgroup
namespace NormalSupplementGluing
variable {G H : Type*} [Group G] [Group H]

/-- Glue the two prescribed maps without assuming a split intersection. -/
theorem exists_equiv (N M : Subgroup G) [N.Normal]
    (R : Subgroup H) (e : N ≃* R) (v : M →* H)
    (hgen : N ⊔ M = ⊤) (hgen' : R ⊔ v.range = ⊤)
    (hinter : ∀ m : M, v m ∈ R ↔ (m : G) ∈ N)
    (hagree : ∀ (m : M) (hm : (m : G) ∈ N), (e ⟨m, hm⟩ : H) = v m)
    (hconj : ∀ (m : M) (n : N),
      (e (MulAut.conjNormal (m : G) n) : H) = v m * e n * (v m)⁻¹) :
    ∃ E : G ≃* H, (∀ n : N, E n = e n) ∧ ∀ m : M, E m = v m := by
  let φ : M →* MulAut N := MulAut.conjNormal.comp M.subtype
  let p : N ⋊[φ] M →* G := SemidirectProduct.lift N.subtype M.subtype
    (by intro m; ext n; rfl)
  let u : N →* H := R.subtype.comp e.toMonoidHom
  let q : N ⋊[φ] M →* H := SemidirectProduct.lift u v
    (by intro m; ext n; exact hconj m n)
  have hp : Function.Surjective p := by
    intro g
    obtain ⟨n, hn, m, hm, he⟩ := mem_sup_of_normal_left.mp
      (show g ∈ N ⊔ M by rw [hgen]; trivial)
    exact ⟨⟨⟨n, hn⟩, ⟨m, hm⟩⟩, he⟩
  have hpq : p.ker ≤ q.ker := by
    rintro ⟨n, m⟩ ha
    change (n : G) * m = 1 at ha
    have hm : (m : G) ∈ N := by
      have he : (m : G) = (n : G)⁻¹ := (inv_eq_iff_mul_eq_one.mpr ha).symm
      rw [he]
      exact N.inv_mem n.property
    have hnm : n * (⟨m, hm⟩ : N) = 1 := Subtype.ext ha
    change (e n : H) * v m = 1
    rw [← hagree m hm, ← Subgroup.coe_mul, ← map_mul, hnm, map_one, Subgroup.coe_one]
  let F : G →* H := p.liftOfSurjective hp ⟨q, hpq⟩
  have hF (a : N ⋊[φ] M) : F (p a) = q a :=
    MonoidHom.liftOfRightInverse_comp_apply ..
  have hFn (n : N) : F n = e n := by
    simpa only [p, q, SemidirectProduct.lift_inl, u, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply] using hF (SemidirectProduct.inl n)
  have hFm (m : M) : F m = v m := by
    simpa only [p, q, SemidirectProduct.lift_inr, Subgroup.subtype_apply] using
      hF (SemidirectProduct.inr m)
  have hi : Function.Injective F := by
    apply (MonoidHom.ker_eq_bot_iff F).mp
    apply bot_unique
    intro g hg
    obtain ⟨⟨n, m⟩, rfl⟩ := hp g
    have he : (e n : H) * v m = 1 := (hF _).symm.trans hg
    have hmR : v m ∈ R := by
      have hm : v m = (e n : H)⁻¹ := (inv_eq_iff_mul_eq_one.mpr he).symm
      rw [hm]
      exact R.inv_mem (e n).property
    have hm : (m : G) ∈ N := (hinter m).mp hmR
    have hnm : n * (⟨m, hm⟩ : N) = 1 := by
      apply e.injective
      apply Subtype.ext
      simpa only [map_mul, Subgroup.coe_mul, hagree m hm, map_one, Subgroup.coe_one] using he
    exact congrArg Subtype.val hnm
  have hs : Function.Surjective F := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hgen']
    apply sup_le
    · intro r hr
      obtain ⟨n, hn⟩ := e.surjective ⟨r, hr⟩
      exact ⟨n, (hFn n).trans (congrArg Subtype.val hn)⟩
    · rintro h ⟨m, rfl⟩
      exact ⟨m, hFm m⟩
  exact ⟨MulEquiv.ofBijective F ⟨hi, hs⟩, hFn, hFm⟩
end NormalSupplementGluing
end
