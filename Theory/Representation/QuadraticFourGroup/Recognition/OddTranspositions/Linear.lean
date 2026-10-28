module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.Recognition.ComponentSpectrum
public import Theory.GroupTheory.DihedralHalfOrderClasses
public import Theory.GroupTheory.Involution.Dihedral

/-!
# The dihedral fixed-space argument for odd transpositions

For a faithful binary action, an element `r` commuting with an involution `z`
and fixing `C_V(z)` has square one. Indeed `z - 1` maps into its own kernel.
Commutation then makes `r - 1` map into that same kernel, which `r - 1` kills.
Thus `(r - 1)^2 = 0`. This gives an explicit nonzero displacement on `C_V(z)`
when the square of the dihedral rotation is nonidentity.

If `Y` fixes the displacements by `a`, its conjugate fixes the displacements
by the corresponding conjugate of `a`. Generation for pairs whose product
is an involution forces their common displacement to be globally fixed.
The two reflection classes of the dihedral group then contradict the preceding
nonzero displacement. No dimension bound, Jordan form, or assumption that the
dihedral group is a two-group is needed.

The commutator lemma also proves the linear implication in Step 3: if
`K ≤ C_G(a)` and `[K,B] = K`, then `[V,a,B] = 0` implies `[V,a,K] = 0`.

Source: GLS, volume 2, Theorem 25.14, Steps 1 and 3. The generation hypothesis
here is explicit; its verification for the actual diagonal layer is separate.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem add_self_binary (v : V) : v + v = 0 := by
  have h := zero_smul (ZMod 2) v
  rw [show (0 : ZMod 2) = 1 + 1 by decide, add_smul, one_smul] at h
  exact h

private theorem neg_binary (v : V) : -v = v :=
  neg_eq_iff_add_eq_zero.mpr (add_self_binary v)

/-- Centralizing an involution and fixing its fixed space forces square one. -/
theorem square_eq_one_of_fixes_involution_fixedSpace
    (hfaithful : Function.Injective ρ) {z r : G} (hz : z ^ 2 = 1)
    (hrz : Commute r z) (hfix : ∀ v : V, ρ z v = v → ρ r v = v) :
    r ^ 2 = 1 := by
  have hzz (v : V) : ρ z (ρ z v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, hz, map_one]
    rfl
  have hc (v : V) : ρ z (ρ r v) = ρ r (ρ z v) := by
    rw [← Module.End.mul_apply, ← map_mul, hrz.eq.symm, map_mul, Module.End.mul_apply]
  have hδ (v : V) : ρ r (ρ z v - v) = ρ z v - v := by
    apply hfix
    rw [map_sub, hzz, sub_eq_add_neg, neg_binary, sub_eq_add_neg, neg_binary,
      add_comm]
  have hrδ (v : V) : ρ z (ρ r v - v) = ρ r v - v := by
    have he := hδ v
    rw [map_sub] at he
    rw [map_sub, hc]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp he
  apply hfaithful
  ext v
  have he := hfix (ρ r v - v) (hrδ v)
  rw [map_sub, sub_eq_add_neg, neg_binary, sub_eq_add_neg, neg_binary] at he
  have he' : ρ r (ρ r v) = v := add_right_cancel (he.trans (add_comm _ _))
  simpa only [pow_two, map_mul, Module.End.mul_apply, map_one,
    Module.End.one_apply] using he'

/-- The dihedral rotation has a nonzero displacement on the central-involution
fixed space whenever its square is nonidentity. -/
theorem exists_displacement_on_involution_fixedSpace
    (hfaithful : Function.Injective ρ) {z r : G} (hz : z ^ 2 = 1)
    (hrz : Commute r z) (hr : r ^ 2 ≠ 1) :
    ∃ v : V, ρ z v = v ∧ ρ r v - v ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hr (square_eq_one_of_fixes_involution_fixedSpace hfaithful hz hrz
    (fun v hv => sub_eq_zero.mp (hn v hv)))

private def vectorStabilizer (ρ : Representation (ZMod 2) G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change ρ (g * h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' {g} hg := by
    change ρ g⁻¹ v = v
    exact (ρ.inv_apply_eq_iff).mpr hg.symm

/-- Two subgroups fixing the displacements generate another such subgroup. -/
theorem FixesDisplacements.sup {a : G} {Y Z : Subgroup G}
    (hY : FixesDisplacements ρ a Y) (hZ : FixesDisplacements ρ a Z) :
    FixesDisplacements ρ a (Y ⊔ Z) := by
  intro g hg v
  have hle : Y ⊔ Z ≤ vectorStabilizer ρ (ρ a v - v) :=
    sup_le (fun y hy => hY y hy v) (fun z hz => hZ z hz v)
  exact hle hg

/-- Conjugation transports the displacement identity and its fixing subgroup. -/
theorem FixesDisplacements.conj {a : G} {Y : Subgroup G}
    (hY : FixesDisplacements ρ a Y) (g : G) :
    FixesDisplacements ρ (MulAut.conj g a) (Y.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨y, hy, rfl⟩ v
  obtain ⟨w, rfl⟩ := (ρ.apply_bijective g).surjective v
  simpa [MulAut.conj_apply, map_mul, Module.End.mul_apply, map_sub] using
    congrArg (ρ g) (hY y hy w)

/-- Commutators with elements centralizing the actor preserve its fixed
displacements. This uses the actual group commutator, not ambient normality. -/
theorem FixesDisplacements.commutator {a : G} {B K : Subgroup G}
    (hB : FixesDisplacements ρ a B)
    (hK : K ≤ centralizer ({a} : Set G)) :
    FixesDisplacements ρ a ⁅K, B⁆ := by
  intro g hg v
  have hc (k : G) (hk : k ∈ K) (w : V) :
      ρ k (ρ a w - w) = ρ a (ρ k w) - ρ k w := by
    rw [map_sub]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul,
      mem_centralizer_singleton_iff.mp (hK hk), map_mul, Module.End.mul_apply]
  have hle : ⁅K, B⁆ ≤ vectorStabilizer ρ (ρ a v - v) := by
    apply Subgroup.commutator_le.mpr
    intro k hk b hb
    change ρ ⁅k, b⁆ (ρ a v - v) = ρ a v - v
    simp only [commutatorElement_def, map_mul, Module.End.mul_apply]
    rw [hB b⁻¹ (B.inv_mem hb), hc k⁻¹ (K.inv_mem hk), hB b hb,
      ← hc k⁻¹ (K.inv_mem hk), ρ.self_inv_apply]
  exact hle hg

/-- The source commutator identity extends displacement fixation to `K`. -/
theorem FixesDisplacements.of_commutator_eq {a : G} {B K : Subgroup G}
    (hB : FixesDisplacements ρ a B)
    (hK : K ≤ centralizer ({a} : Set G)) (hcomm : ⁅K, B⁆ = K) :
    FixesDisplacements ρ a K := by
  rw [← hcomm]
  exact hB.commutator hK

private theorem fixed_of_twist {s z : G} {Y Z : Subgroup G}
    (hY : FixesDisplacements ρ s Y) (hZ : FixesDisplacements ρ (s * z) Z)
    (hgen : Y ⊔ Z = ⊤)
    (hfixed : ∀ v : V, (∀ g : G, ρ g v = v) → v = 0)
    {v : V} (hv : ρ z v = v) : ρ s v = v := by
  apply sub_eq_zero.mp
  apply hfixed
  intro g
  have hle : Y ⊔ Z ≤ vectorStabilizer ρ (ρ s v - v) := by
    refine sup_le (fun y hy => hY y hy v) ?_
    intro y hy
    change ρ y (ρ s v - v) = ρ s v - v
    simpa only [map_mul, Module.End.mul_apply, hv] using hZ y hy v
  exact hle (hgen ▸ mem_top g)

private theorem pair_generation {a : G} {Y : Subgroup G}
    (hgen : ∀ x : G, orderOf (a * (x⁻¹ * a * x)) = 2 →
      Y ⊔ Y.map (MulAut.conj x⁻¹).toMonoidHom = ⊤)
    {g h : G} (horder : orderOf (MulAut.conj g a * MulAut.conj h a) = 2) :
    Y.map (MulAut.conj g).toMonoidHom ⊔ Y.map (MulAut.conj h).toMonoidHom = ⊤ := by
  have he : MulAut.conj g (a * MulAut.conj (g⁻¹ * h) a) =
      MulAut.conj g a * MulAut.conj h a := by
    simp only [MulAut.conj_apply]
    group
  have ho : orderOf (a * ((h⁻¹ * g)⁻¹ * a * (h⁻¹ * g))) = 2 := by
    have hh := (MulAut.conj g).orderOf_eq (a * MulAut.conj (g⁻¹ * h) a)
    rw [he] at hh
    simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv] using hh.symm.trans horder
  have hm := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) (hgen (h⁻¹ * g) ho)
  rw [Subgroup.map_sup, Subgroup.map_map] at hm
  have hc : (MulAut.conj g).toMonoidHom.comp (MulAut.conj (h⁻¹ * g)⁻¹).toMonoidHom =
      (MulAut.conj h).toMonoidHom := by
    ext u
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hc, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at hm
  exact hm

/-- GLS2 Theorem 25.14, Step 1. It suffices to assume generation when the
product of the conjugate involutions has order two. -/
theorem hasOddTranspositions_of_generates [Finite G] {a : G} {Y : Subgroup G}
    (hfaithful : Function.Injective ρ) (ha : orderOf a = 2)
    (hfixed : ∀ v : V, (∀ g : G, ρ g v = v) → v = 0)
    (hY : FixesDisplacements ρ a Y)
    (hgen : ∀ x : G, orderOf (a * (x⁻¹ * a * x)) = 2 →
      Y ⊔ Y.map (MulAut.conj x⁻¹).toMonoidHom = ⊤) :
    HasOddTranspositions a := by
  intro x
  by_contra hn
  push Not at hn
  let b := x⁻¹ * a * x
  have hab : IsConj a b := isConj_iff.mpr ⟨x⁻¹, by simp [b]⟩
  have hb : orderOf b = 2 := by
    simpa only [b, MulAut.conj_apply, inv_inv] using
      ((MulAut.conj x⁻¹).orderOf_eq a).trans ha
  have haa : a * a = 1 := by simpa only [ha, pow_two] using pow_orderOf_eq_one a
  have hbb : b * b = 1 := by simpa only [hb, pow_two] using pow_orderOf_eq_one b
  have heven : Even (orderOf (a * b)) := Nat.not_odd_iff_even.mp hn.2
  have heven' : orderOf (a * b) % 2 = 0 := Nat.even_iff.mp heven
  let z := (a * b) ^ (orderOf (a * b) / 2)
  have habne : a ≠ b := by
    intro heq
    have : orderOf (a * b) = 1 := by rw [← heq, haa, orderOf_one]
    exact hn.2 (this ▸ (by decide : Odd 1))
  have hzdata := BenderSuzuki.External.Suzuki.V.suzuki_ch5_proposition_1_2_iii
    (⟨(fun heq => by simp [heq] at ha),
      (by simpa only [pow_two] using haa)⟩)
    (⟨(fun heq => by simp [heq] at hb),
      (by simpa only [pow_two] using hbb)⟩) habne
    (show orderOf (a * b) = 2 * (orderOf (a * b) / 2) by omega)
  have hz : orderOf z = 2 := by
    exact orderOf_eq_prime hzdata.1.sq_eq_one hzdata.1.ne_one
  have hza : IsConj a (a * z) := by
    by_cases hm : orderOf (a * b) % 4 = 0
    · simpa only [TwoInvolutionClassOrder.halfOrder_def] using
        (DihedralHalfOrderClasses.preserve ha hb hm).1
    · have hm' : orderOf (a * b) % 4 = 2 := by omega
      exact hab.trans (by simpa only [TwoInvolutionClassOrder.halfOrder_def] using
        (DihedralHalfOrderClasses.exchange ha hb hm').1)
  have hzb : IsConj a (b * z) := by
    by_cases hm : orderOf (a * b) % 4 = 0
    · exact hab.trans (by simpa only [TwoInvolutionClassOrder.halfOrder_def] using
        (DihedralHalfOrderClasses.preserve ha hb hm).2)
    · have hm' : orderOf (a * b) % 4 = 2 := by omega
      simpa only [TwoInvolutionClassOrder.halfOrder_def] using
        (DihedralHalfOrderClasses.exchange ha hb hm').2
  have hfix (s : G) (hs : IsConj a s) (hst : IsConj a (s * z))
      (hss : s * s = 1) (v : V) (hv : ρ z v = v) : ρ s v = v := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hs
    obtain ⟨t, ht⟩ := isConj_iff.mp hst
    have hg' : MulAut.conj g a = s := hg
    have ht' : MulAut.conj t a = s * z := ht
    have hjoin := pair_generation hgen (g := g) (h := t) (by
      rw [hg', ht', ← mul_assoc, hss, one_mul]
      exact hz)
    have hYg := hY.conj g
    have hYt := hY.conj t
    rw [hg'] at hYg
    rw [ht'] at hYt
    exact fixed_of_twist hYg hYt hjoin hfixed hv
  have hr2 : (a * b) ^ 2 ≠ 1 := by
    intro heq
    have hd : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one heq
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with hone | htwo
    · exact hn.2 (hone ▸ (by decide : Odd 1))
    · exact hn.1 htwo
  obtain ⟨v, hv, hmove⟩ := exists_displacement_on_involution_fixedSpace hfaithful
    hzdata.1.sq_eq_one ((Commute.refl (a * b)).pow_right _) hr2
  apply hmove
  rw [map_mul, Module.End.mul_apply, hfix b hab hzb hbb v hv,
    hfix a (IsConj.refl a) hza haa v hv, sub_self]

end Representation.QuadraticFourGroup

end
