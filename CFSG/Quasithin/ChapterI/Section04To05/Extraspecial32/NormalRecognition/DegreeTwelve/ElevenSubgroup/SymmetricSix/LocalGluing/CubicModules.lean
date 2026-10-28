module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.Transport
public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# The cubic moved four and its involution-fixed line

For the literal elementary eight `fusionCore r`, coprime splitting separates
its cubic fixed line `zpowers r` from the ambient commutator `movedFour r X`.
The product-order formula gives order four for that commutator, and the
splitting gives its trivial cubic fixed subgroup.

The inverting involution normalizes this moved four and acts nontrivially:
otherwise each cubic operator would have order dividing both two and three.
An involution acting nontrivially on a four-element group has exactly two
fixed elements, by parity and the subgroup-order bound. Identifying the
fixed subgroup with the literal ambient intersection gives `fixedLine`.
The final consumer applies the calculation at both source fusion eights.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.6, pp.40–41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {r q : G} {X : Subgroup G}

private theorem moved_split (h : CubicEightContext r q X) :
    movedFour r X ⊔ zpowers r = fusionCore r ∧
      movedFour r X ⊓ zpowers r = ⊥ := by
  let := h.elementary
  have hc : Nat.Coprime (Nat.card X) (Nat.card (fusionCore r)) := by
    rw [h.cubic_card, h.card]
    decide
  have hs := commutator_centralizer_decomposition_of_coprime_image
    (fusionCore r) X h.cubic_normalizes (hc.of_dvd_left (card_range_dvd _))
  simpa only [h.cubic_fixed, movedFour] using hs

private theorem moved_card (h : CubicEightContext r q X) :
    Nat.card (movedFour r X) = 4 := by
  obtain ⟨hs, hi⟩ := moved_split h
  have hn : zpowers r ≤ normalizer (movedFour r X : Set G) :=
    (zpowers_le.mpr h.base_mem).trans (normalizer_commutator_ge_left _ _)
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint (movedFour r X) (zpowers r)
    hn (disjoint_iff.mpr hi)
  rw [hs, h.card, Nat.card_zpowers, h.base_order] at hc
  omega

private theorem moved_fixed_free (h : CubicEightContext r q X) :
    movedFour r X ⊓ centralizer (X : Set G) = ⊥ := by
  have hle : movedFour r X ≤ fusionCore r :=
    le_normalizer_iff_commutator_le_left.mp h.cubic_normalizes
  calc
    movedFour r X ⊓ centralizer (X : Set G) =
        movedFour r X ⊓ (fusionCore r ⊓ centralizer (X : Set G)) := by
      rw [← inf_assoc, inf_eq_left.mpr hle]
    _ = ⊥ := by rw [h.cubic_fixed]; exact (moved_split h).2

omit [Finite G] in
private theorem involution_normalizes_moved (h : CubicEightContext r q X) :
    q ∈ normalizer (movedFour r X : Set G) := by
  have hX : X.map (MulAut.conj q).toMonoidHom = X := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change q * x * q⁻¹ ∈ X
      rw [h.inverts x hx]
      exact X.inv_mem hx
    · intro x hx
      refine ⟨x⁻¹, X.inv_mem hx, ?_⟩
      change q * x⁻¹ * q⁻¹ = x
      rw [h.inverts _ (X.inv_mem hx), inv_inv]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (movedFour r X).map (MulAut.conj q).toMonoidHom = movedFour r X
  have hA : (fusionCore r).map (MulAut.conj q).toMonoidHom = fusionCore r :=
    mem_normalizer_iff_map_conj_eq.mp h.involution_normalizes
  rw [movedFour, map_commutator, hA, hX]

private theorem line_card (h : CubicEightContext r q X) :
    Nat.card (fixedLine r q X) = 2 := by
  let B := movedFour r X
  let f := B.normalizerMonoidHom
  let t : normalizer (B : Set G) := ⟨q, involution_normalizes_moved h⟩
  let a : MulAut B := f t
  have ha2 : a ^ 2 = 1 := by
    rw [← map_pow]
    have ht2 : t ^ 2 = 1 := Subtype.ext (h.involution_order ▸ pow_orderOf_eq_one q)
    rw [ht2, map_one]
  have hne : a ≠ 1 := by
    intro ha
    have hBX : B ≤ centralizer (X : Set G) := by
      intro b hb x hx
      let s : normalizer (B : Set G) :=
        ⟨x, normalizer_commutator_ge_right (fusionCore r) X hx⟩
      have hst : t * s * t⁻¹ = s⁻¹ := Subtype.ext (h.inverts x hx)
      have hs3 : s ^ 3 = 1 := by
        apply Subtype.ext
        change x ^ 3 = 1
        have hp := pow_card_eq_one' (x := (⟨x, hx⟩ : X))
        simpa only [Subgroup.coe_pow, Subgroup.coe_one, h.cubic_card] using congrArg Subtype.val hp
      have hinv : f s = (f s)⁻¹ := by
        have he := congrArg f hst
        rw [map_mul, map_mul, map_inv, map_inv] at he
        change a * f s * a⁻¹ = (f s)⁻¹ at he
        simpa only [ha, one_mul, inv_one, mul_one] using he
      have hs2 : (f s) ^ 2 = 1 := by
        calc
          (f s) ^ 2 = (f s)⁻¹ * f s := by
            rw [pow_two]
            exact congrArg (fun b => b * f s) hinv
          _ = 1 := inv_mul_cancel _
      have hfs3 : (f s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
      have hfs : f s = 1 := by
        calc
          f s = (f s) ^ 3 * ((f s) ^ 2)⁻¹ := by group
          _ = 1 := by rw [hs2, hfs3]; simp
      have hbfix := congrArg (fun e : MulAut B => e ⟨b, hb⟩) hfs
      have he := congrArg Subtype.val hbfix
      change x * b * x⁻¹ = b at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have hB0 : B = ⊥ := by
      rw [← moved_fixed_free h]
      exact (inf_eq_left.mpr hBX).symm
    have hc := moved_card h
    change Nat.card B = 4 at hc
    have hc1 : Nat.card B = 1 := Subgroup.card_eq_one.mpr hB0
    omega
  have hcB : Nat.card B = 4 := moved_card h
  have hpos : 0 < Nat.card a.fixedSubgroup := Nat.card_pos
  have hbound : Nat.card a.fixedSubgroup ≤ 4 := by
    exact (Nat.card_le_card_of_injective _ a.fixedSubgroup.subtype_injective).trans_eq hcB
  have hnotfour : Nat.card a.fixedSubgroup ≠ 4 := by
    intro hc
    have htop : a.fixedSubgroup = ⊤ := a.fixedSubgroup.eq_top_of_card_eq (hc.trans hcB.symm)
    apply hne
    apply MulEquiv.ext
    intro b
    exact (MulAut.mem_fixedSubgroup a b).mp (htop ▸ mem_top b)
  have hmod := MulAut.fixedSubgroup_card_mod_two a ha2
  have hc : Nat.card a.fixedSubgroup = 2 := by rw [hcB] at hmod; omega
  have hmem (b : B) : b ∈ a.fixedSubgroup ↔ (b : G) ∈ centralizer ({q} : Set G) := by
    rw [MulAut.mem_fixedSubgroup, Subtype.ext_iff, mem_centralizer_singleton_iff]
    change q * (b : G) * q⁻¹ = b ↔ (b : G) * q = q * b
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  have he : Nat.card a.fixedSubgroup = Nat.card (fixedLine r q X) := by
    apply Nat.card_congr
    exact {
      toFun := fun b => ⟨b.val.val, b.val.property, (hmem b.val).mp b.property⟩
      invFun := fun b => ⟨⟨b.val, b.property.1⟩, (hmem _).mpr b.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact he.symm.trans hc

/-- The elementary eight and its actual cubic/involution action determine
all six clauses of the source's moved-four calculation. -/
public theorem cubicFourData_of_cubicEightContext (h : CubicEightContext r q X) :
    CubicFourData r q X := by
  let := h.elementary
  have hle : movedFour r X ≤ fusionCore r :=
    le_normalizer_iff_commutator_le_left.mp h.cubic_normalizes
  exact {
    elementary := IsElementaryAbelian.of_le hle
    card := moved_card h
    normalizes := normalizer_commutator_ge_right _ _
    fixed_free := moved_fixed_free h
    decomposition := (sup_comm (zpowers r) (movedFour r X)).trans (moved_split h).1
    line_card := line_card h }

/-- Both source fusion eights satisfy the moved-four and fixed-line conclusions,
with the literal cubics supplied by `CommutingCubicData`. -/
public theorem cubicFourData_pair {z : G} (h : Hypotheses z) (d : FusionEightData z)
    {a : SourceGeometry h} (c : CommutingCubicData h a) :
    CubicFourData z c.u (cubicInG h) ∧ CubicFourData c.u z c.X1 := by
  obtain ⟨h₁, h₂⟩ := cubicEightContexts h d c
  exact ⟨cubicFourData_of_cubicEightContext h₁, cubicFourData_of_cubicEightContext h₂⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing
