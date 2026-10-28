module

public import Theory.GroupTheory.PStar.Basic
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Residual reduction for the p-star extension criterion

Suppose G = N C_G(P), where P is a Sylow p-subgroup of the normal subgroup N.
Writing R = O^p(N) and Y = O^p(G), the Sylow supplement N = RP shows that
R C_G(P) is normal with p-group quotient, hence contains Y. Put K = N ∩ Y.
Then O^p(K) = R and Y = R C_Y(P ∩ K). The quotient Y/K is G/N when that
quotient is p-perfect. Thus the stronger GLS extension criterion applies to
Y and K, and the idempotence of the residual gives the desired conclusion.

The extension criterion is an explicit universal input from GLS II, Chapter B,
Lemma 5.3. This module proves the residual reduction needed in the proof of
Theorem 5.9; it does not assume the false implication G = R C_G(P).
-/

public section

open Subgroup Theory.GroupTheory
universe u
namespace Theory.GroupTheory
variable {p : ℕ} [Fact p.Prime]

/-- The universal form of the earlier extension criterion; the ambient universe
is shared with its subgroup and quotient applications. -/
abbrev SylowBoundExtensionCriterion : Prop :=
  ∀ (Y : Type u) [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal] (P : Sylow p N),
    IsPStar p (Y ⧸ N) → IsPStar p (pResidual p N) →
    (pResidual p N).map N.subtype ⊔
      centralizer ((P : Subgroup N).map N.subtype : Set Y) = ⊤ →
    IsPStar p (pResidual p Y)

variable {G : Type u} [Group G] [Finite G]

private theorem residual_le_residual_sup_centralizer
    (N : Subgroup G) [N.Normal] (P : Sylow p N)
    (hgen : N ⊔ centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤) :
    pResidual p G ≤ (pResidual p N).map N.subtype ⊔
      centralizer ((P : Subgroup N).map N.subtype : Set G) := by
  let R := (pResidual p N).map N.subtype
  let T := (P : Subgroup N).map N.subtype
  let C := centralizer (T : Set G)
  have hRT : R ⊔ T = N := by
    have h := congrArg (Subgroup.map N.subtype) (pResidual_sup_sylow_eq_top P)
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] using h
  have hTC : T ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (le_rfl : C ≤ centralizer (T : Set G))).trans
      (centralizer_le_normalizer (C : Set G))
  have hwhole : (R ⊔ C) ⊔ T = ⊤ := by
    rw [sup_right_comm, hRT]
    exact hgen
  let _ : (R ⊔ C).Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hwhole]
    exact sup_le (R ⊔ C).le_normalizer
      ((le_inf le_normalizer_of_normal hTC).trans
        (normalizer_inf_normalizer_le_normalizer_sup R C))))
  exact sInf_le ⟨inferInstance,
    isPGroup_quotient_of_sup_eq_top (R ⊔ C) T (P.isPGroup'.map N.subtype) hwhole⟩

/-- Residual reduction upgrades an ordinary Sylow-centralizer supplement to the
stronger supplement required by GLS II 5.3, inside the ambient residual. -/
theorem isPStar_pResidual_of_sylow_supplement
    (hext : SylowBoundExtensionCriterion.{u} (p := p))
    (N : Subgroup G) [N.Normal] (P : Sylow p N)
    (hquot : IsPStar p (G ⧸ N)) (hN : IsPStar p (pResidual p N))
    (hgen : N ⊔ centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤) :
    IsPStar p (pResidual p G) := by
  let Y := pResidual p G
  let R := (pResidual p N).map N.subtype
  let C := centralizer ((P : Subgroup N).map N.subtype : Set G)
  let K := N.subgroupOf Y
  let J := Y.subgroupOf N
  have hRY : R ≤ Y := map_pResidual_le p N.subtype
  have hYRC : Y ≤ R ⊔ C := residual_le_residual_sup_centralizer N P hgen
  let f : Y →* G ⧸ N := (QuotientGroup.mk' N).comp Y.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    exact (map_pResidual_of_surjective p (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans hquot.1
  have hk : f.ker = K := by
    ext x
    exact QuotientGroup.eq_one_iff (x : G)
  have hKquot : IsPStar p (Y ⧸ K) := hquot.of_equiv
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk))
  let i : K →* N :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hresK : (pResidual p K).map K.subtype = R.subgroupOf Y := by
    apply le_antisymm
    · rintro x ⟨k, hk, rfl⟩
      exact mem_map.mpr ⟨i k, map_pResidual_le p i (mem_map.mpr ⟨k, hk, rfl⟩), rfl⟩
    · intro x hx
      obtain ⟨n, hn, he⟩ := mem_map.mp hx
      let a : pResidual p N := ⟨n, hn⟩
      let j : pResidual p N →* K :=
        { toFun := fun n => ⟨⟨n.val.val, hRY (mem_map.mpr ⟨n.val, n.property, rfl⟩)⟩,
            n.val.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have ha : a ∈ pResidual p (pResidual p N) := by rw [hN.1]; trivial
      have hj : j a ∈ pResidual p K := map_pResidual_le p j (mem_map.mpr ⟨a, ha, rfl⟩)
      exact mem_map.mpr ⟨j a, hj, Subtype.ext he⟩
  have hKstar : IsPStar p (pResidual p K) := by
    let eR := (pResidual p N).equivMapOfInjective N.subtype N.subtype_injective
    let eK := (pResidual p K).equivMapOfInjective K.subtype K.subtype_injective
    exact (((hN.of_equiv eR).of_equiv (subgroupOfEquivOfLe hRY).symm).of_equiv
      (MulEquiv.subgroupCongr hresK).symm).of_equiv eK.symm
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal J
  let e : K ≃* J :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let Q : Sylow p K := S.comapOfInjective e.toMonoidHom e.injective
    (by rw [e.toMonoidHom.range_eq_top_of_surjective e.surjective]; exact le_top)
  have hQ : ∀ k ∈ (Q : Subgroup K), i k ∈ (P : Subgroup N) := by
    intro k hk
    change e k ∈ (S : Subgroup J) at hk
    rw [hS] at hk
    exact hk
  have hstrong : (pResidual p K).map K.subtype ⊔
      centralizer ((Q : Subgroup K).map K.subtype : Set Y) = ⊤ := by
    rw [hresK]
    apply top_unique
    intro y _
    obtain ⟨r, hr, c, hc, he⟩ := mem_sup_of_normal_left.mp (hYRC y.property)
    have hcY : c ∈ Y := by
      have h : r⁻¹ * (y : G) ∈ Y := Y.mul_mem (Y.inv_mem (hRY hr)) y.property
      simpa only [← he, inv_mul_cancel_left] using h
    have hcQ : (⟨c, hcY⟩ : Y) ∈ centralizer ((Q : Subgroup K).map K.subtype : Set Y) := by
      rintro z ⟨k, hk, rfl⟩
      apply Subtype.ext
      exact hc (i k : G) (mem_map.mpr ⟨i k, hQ k hk, rfl⟩)
    exact mem_sup_of_normal_left.mpr
      ⟨⟨r, hRY hr⟩, hr, ⟨c, hcY⟩, hcQ, Subtype.ext he⟩
  have h := hext Y K Q hKquot hKstar hstrong
  exact h.of_equiv ((MulEquiv.subgroupCongr
    ((pResidual_eq_top_iff p Y).mpr (isPPerfect_pResidual p))).trans Subgroup.topEquiv)
end Theory.GroupTheory
