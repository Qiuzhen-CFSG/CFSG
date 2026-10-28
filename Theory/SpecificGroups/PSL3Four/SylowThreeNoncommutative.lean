module
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Nonabelian Sylow three-subgroups over PSL₃(4)

Suppose a finite group has a normal PSL₃(4) subgroup with centralizer of
order prime to three. An ambient Sylow three-subgroup of order twenty-seven
is nonabelian: otherwise it acts faithfully and fixes its entire intersection
with the normal subgroup. That intersection is Sylow in PSL₃(4), whose
pointwise automorphism fixer has order dividing eighteen. The incompatible
orders give the contradiction. All actions are the original conjugations.

This supplies the nonabelian part of the marked extraspecial Sylow construction
in Aschbacher--Smith, 11.1.2, printed p.763. The source consumer obtains the
centralizer bound from quasithinness and the order from its actual PGL₃(4)
quotient; neither is presumed to hold for arbitrary extensions.
-/

open Subgroup
open scoped IsMulCommutative
public noncomputable section
namespace Matrix.PSL3Four
open ExtendedCentralizer.ProjectiveFixer
variable {H : Type*} [Group H] [Finite H]

theorem sylow_three_noncomm_of_normal_simple (K : Subgroup H) [K.Normal]
    (e : K ≃* PSL) (hcop : Nat.Coprime 3 (Nat.card (centralizer (K : Set H))))
    (P : Sylow 3 H) (hc : Nat.card P = 27) : ¬ IsMulCommutative P := by
  intro hcomm
  let : IsMulCommutative P := hcomm
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal K
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : H →* MulAut PSL := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hk : a.ker = centralizer (K : Set H) := by
    ext x
    change MulAut.congr e (MulAut.conjNormal x) = 1 ↔ _
    rw [(MulAut.congr e).map_eq_one_iff]
    constructor
    · intro hx k hk
      have hh := congrArg (fun f : MulAut K => (f ⟨k,hk⟩ : H)) hx
      change x * k * x⁻¹ = k at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hx
      ext k
      change x * (k : H) * x⁻¹ = (k : H)
      rw [← mem_centralizer_iff.mp hx k k.property,mul_inv_cancel_right]
  have hinj := injective_comp_subtype_of_coprime_ker a (hk ▸ hcop) P P.isPGroup'
  have hf : (P : Subgroup H).map a ≤ fixer R := by
    rintro _ ⟨x,hx,rfl⟩
    constructor
    · rw [PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (m := 2)
        (by decide) card_F]
      trivial
    · rintro ⟨y,hy⟩
      obtain ⟨k,hk,rfl⟩ := hy
      have hkP : (k : H) ∈ (P : Subgroup H) := by
        rw [hQ] at hk
        exact hk
      have hh : x * (k : H) = (k : H) * x := congrArg Subtype.val
        (mul_comm (⟨x,hx⟩ : P) ⟨k,hkP⟩)
      change e (MulAut.conjNormal x (e.symm (e k))) = e k
      rw [e.symm_apply_apply]
      congr 1
      apply Subtype.ext
      change x * (k : H) * x⁻¹ = (k : H)
      rw [hh,mul_inv_cancel_right]
  have hd : Nat.card (fixer R) ∣ 18 := by
    rw [sylow_fixer_card R,model_fixer_eq_candidate]
    exact candidate_card_dvd
  have hcard : Nat.card ((P : Subgroup H).map a) = 27 := by
    have hh := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp,range_subtype] at hh
    exact hh.symm.trans hc
  have hh := (card_dvd_of_le hf).trans hd
  rw [hcard] at hh
  norm_num at hh
end Matrix.PSL3Four
