module

public import Theory.SpecificGroups.Tits.Atlas1600Order

/-!
# A three-point base for the Atlas Tits group

At each level of the certified Schreier chain, distinct orbit representatives
give an injection from the product of the orbit and the next subgroup. The
certified cardinalities make this injection surjective. An element fixing the
base point therefore lies in the next subgroup. The third subgroup is trivial,
so equality at points 0, 1, 2 determines an Atlas group element.

Source: the Atlas degree-1600 order certificate and its original point maps.
-/

namespace Tits.ConverseLocalCoverage.DoubleCosetCertificate
open Atlas1600OrderCertificate Theory.GroupTheory

private theorem next_of_fix {V : Type*} [Finite V]
    (H K : Subgroup (Equiv.Perm V)) (hKH : K ≤ H)
    {m : Nat} (rep : Fin m → Equiv.Perm V) (base : V)
    (point : Fin m → V) (baseRep : Fin m)
    (hmem : ∀ r, rep r ∈ H) (hbase : rep baseRep = 1)
    (hpoint : ∀ r, rep r base = point r)
    (hinj : Function.Injective point) (hfix : ∀ k : K, k.val base = base)
    (hcard : Nat.card H = m * Nat.card K)
    {g : Equiv.Perm V} (hg : g ∈ H) (hgb : g base = base) : g ∈ K := by
  classical
  let cover : Fin m × K → H := fun x =>
    ⟨rep x.1 * x.2.val, H.mul_mem (hmem x.1) (hKH x.2.property)⟩
  have hc : Function.Injective cover := by
    rintro ⟨r, k⟩ ⟨r', k'⟩ he
    have hr : r = r' := by
      apply hinj
      have hp := congrArg (fun p : Equiv.Perm V => p base) (Subtype.ext_iff.mp he)
      simpa only [cover, Equiv.Perm.mul_apply, hfix, hpoint] using hp
    subst r'
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact mul_left_cancel (Subtype.ext_iff.mp he)
  have hs : Function.Surjective cover :=
    (hc.bijective_of_nat_card_le (by simpa using hcard.le)).2
  obtain ⟨⟨r, k⟩, he⟩ := hs ⟨g, hg⟩
  have hval : rep r * k.val = g := Subtype.ext_iff.mp he
  have hr : r = baseRep := by
    apply hinj
    rw [← hpoint, ← hpoint, hbase]
    have hp := congrArg (fun p : Equiv.Perm V => p base) hval
    simpa only [Equiv.Perm.mul_apply, hfix, hgb, Equiv.Perm.one_apply] using hp
  subst r
  rw [hbase, one_mul] at hval
  exact hval ▸ k.property

public theorem threePoint_eq_one (x : Atlas1600Group)
    (h0 : x.val 0 = 0) (h1 : x.val 1 = 1) (h2 : x.val 2 = 2) : x = 1 := by
  have hx : x.val ∈ H0 := by rw [H0_eq_atlas]; exact x.property
  have hx1 : x.val ∈ H1 := next_of_fix H0 H1 H1_le L0Rep 0 L0Point 0
    L0Rep_mem L0Rep_base L0Rep_point L0Point_injective H1_fix H0_card_step hx h0
  have hx2 : x.val ∈ H2 := next_of_fix H1 H2 H2_le L1Rep 1 L1Point 0
    L1Rep_mem L1Rep_base L1Rep_point L1Point_injective H2_fix H1_card_step hx1 h1
  have h3 : H3 = ⊥ := wordSubgroup_fin_zero_eq_bot L3Gen L3Inv L3Inv_spec
  have hx3 : x.val ∈ H3 := next_of_fix H2 H3 (by rw [h3]; exact bot_le)
    L2Rep 2 L2Point 0 L2Rep_mem L2Rep_base L2Rep_point L2Point_injective
    (by intro k; have hk : k.val = 1 := by simpa only [h3, Subgroup.mem_bot] using k.property
        rw [hk]; rfl)
    (by rw [H2_card, H3_card]) hx2 h2
  apply Subtype.ext
  change x.val = 1
  simpa only [h3, Subgroup.mem_bot] using hx3

public theorem threePoint_ext {x y : Atlas1600Group}
    (h0 : x.val 0 = y.val 0) (h1 : x.val 1 = y.val 1)
    (h2 : x.val 2 = y.val 2) : x = y := by
  have he : x⁻¹ * y = 1 := threePoint_eq_one _
    (by change x.val.symm (y.val 0) = 0; rw [← h0]; exact x.val.symm_apply_apply 0)
    (by change x.val.symm (y.val 1) = 1; rw [← h1]; exact x.val.symm_apply_apply 1)
    (by change x.val.symm (y.val 2) = 2; rw [← h2]; exact x.val.symm_apply_apply 2)
  exact inv_mul_eq_one.mp he

end Tits.ConverseLocalCoverage.DoubleCosetCertificate
