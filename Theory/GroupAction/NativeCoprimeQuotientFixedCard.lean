module
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Fixed subgroups of a supplied native quotient action

Let P normalize N≤R in a finite ambient group, and let A≤P have order
coprime to the solvable group R. Retain the supplied normality witness
for N inside R and the supplied P→Aut(R/N) homomorphism with its literal
conjugation formula. For the precise A-action obtained by composing this
homomorphism with the inclusion A→P, the quotient fixed subgroup is the
image of C_R(A). The restricted quotient map gives normality of C_N(A)
in C_R(A), an isomorphism C_R(A)/C_N(A) to that same fixed subgroup, and
the resulting equality of orders.

Use the native conjugation action on R and coprime fixed-point lifting.
On each quotient representative the canonical action agrees with the
supplied formula; this comparison is used locally for lifting, without
changing the public action instance. The restricted quotient map has
kernel exactly C_N(A), so the first isomorphism theorem supplies both
the isomorphism and count. The companion applies native coprime
centralizer decomposition: if [R,A] together with N does not generate R,
the same quotient action has a nontrivial fixed subgroup.

Source: Stellmacher (10.1), Journal of Algebra190 (1997), printed p.64,
the fixed factors Qi=C_U(Ai), Wi=C_V(Ai) and their quotient orders in
the proof of (19). The isomorphism also transfers elementary abelian
structure to those literal centralizer quotients.
-/

namespace Subgroup

public theorem native_coprime_quotient_fixed_card
    {G : Type*} [Group G] [Finite G] (P R N A : Subgroup G)
    (hNR : N≤R) (hPR : P≤normalizer (R:Set G)) (hPN : P≤normalizer (N:Set G))
    (hAP : A≤P) (hsolv : Group.IsSolvable R)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hN : (N.subgroupOf R).Normal) :
    let _ := hN
    ∀ action : P→*MulAut (R ⧸ N.subgroupOf R),
      (∀ p:P,∀ r:R,action p (QuotientGroup.mk' (N.subgroupOf R) r)=
        QuotientGroup.mk' (N.subgroupOf R)
          ⟨(p:G)*(r:G)*(p:G)⁻¹,(mem_normalizer_iff.mp (hPR p.property) r).mp r.property⟩) →
      let _ : MulDistribMulAction A (R ⧸ N.subgroupOf R) :=
        MulDistribMulAction.compHom _ (action.comp (inclusion hAP))
      let C := R⊓centralizer (A:Set G)
      let D := N⊓centralizer (A:Set G)
      FixedPoints.subgroup A (R ⧸ N.subgroupOf R)=
          (C.subgroupOf R).map (QuotientGroup.mk' (N.subgroupOf R)) ∧
        ∃ hD : (D.subgroupOf C).Normal,
          let _ := hD
          Nonempty ((C ⧸ D.subgroupOf C) ≃* FixedPoints.subgroup A (R ⧸ N.subgroupOf R)) ∧
            Nat.card (C ⧸ D.subgroupOf C)=Nat.card (FixedPoints.subgroup A (R ⧸ N.subgroupOf R)) := by
  classical
  let _ := hN
  dsimp only
  intro action haction
  let X := R ⧸ N.subgroupOf R
  let π : R→*X := QuotientGroup.mk' (N.subgroupOf R)
  let _ : MulDistribMulAction A X := MulDistribMulAction.compHom X (action.comp (inclusion hAP))
  let C := R⊓centralizer (A:Set G)
  let D := N⊓centralizer (A:Set G)
  let nativeAction := conjMulDistribMulActionOfLeNormalizer A R (hAP.trans hPR)
  let _ : MulDistribMulAction A R := nativeAction
  let _ : SMul A R := nativeAction.toSMul
  let _ : MulAction A R := nativeAction.toMulAction
  have hInv : IsInvariant A R (N.subgroupOf R) := by
    constructor
    intro a r
    change (r:G)∈N ↔ (a:G)*(r:G)*(a:G)⁻¹∈N
    exact mem_normalizer_iff.mp (hPN (hAP a.property)) r
  have hfixedNative : FixedPoints.subgroup A R=C.subgroupOf R := by
    ext r
    constructor
    · intro hr
      refine ⟨r.property,mem_centralizer_iff.mpr ?_⟩
      intro a ha
      have hh := congrArg Subtype.val (hr ⟨a,ha⟩)
      change a*(r:G)*a⁻¹=(r:G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hr a
      apply Subtype.ext
      change (a:G)*(r:G)*(a:G)⁻¹=(r:G)
      have hh := mem_centralizer_iff.mp hr.2 a a.property
      change (a:G)*(r:G)=(r:G)*(a:G) at hh
      rw [hh,mul_inv_cancel_right]
  have himage : FixedPoints.subgroup A X=(C.subgroupOf R).map π := by
    apply le_antisymm
    · intro x hx
      let _ : MulDistribMulAction A X := quotientMulDistribMulAction (A:=A) (N.subgroupOf R) hInv
      have hxCanonical : x∈FixedPoints.subgroup A X := by
        intro a
        obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) x
        change π (a • r)=π r
        have hh := hx a
        change action (inclusion hAP a) (π r)=π r at hh
        rw [haction] at hh
        exact hh
      rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hsolv hcop
        (N.subgroupOf R) hInv,hfixedNative] at hxCanonical
      exact hxCanonical
    · rintro _ ⟨r,hr,rfl⟩ a
      change action (inclusion hAP a) (π r)=π r
      rw [haction]
      apply congrArg π
      apply Subtype.ext
      change (a:G)*(r:G)*(a:G)⁻¹=(r:G)
      have hh := mem_centralizer_iff.mp hr.2 a a.property
      change (a:G)*(r:G)=(r:G)*(a:G) at hh
      rw [hh,mul_inv_cancel_right]
  have hCR : C≤R := inf_le_left
  have hDC : D≤C := inf_le_inf hNR le_rfl
  let f : C→*X := π.comp (inclusion hCR)
  have hker : f.ker=D.subgroupOf C := by
    ext c
    change ((inclusion hCR c : R) : R ⧸ N.subgroupOf R)=1 ↔ (c:G)∈D
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hc
      exact ⟨hc,c.property.2⟩
    · intro hc
      exact hc.1
  have hD : (D.subgroupOf C).Normal := hker ▸ inferInstance
  let _ := hD
  have hrange : f.range=FixedPoints.subgroup A X := by
    rw [himage]
    ext x
    constructor
    · rintro ⟨c,rfl⟩
      exact ⟨inclusion hCR c,c.property,rfl⟩
    · rintro ⟨r,hr,rfl⟩
      exact ⟨⟨r,hr⟩,rfl⟩
  let equiv : (C ⧸ D.subgroupOf C) ≃* FixedPoints.subgroup A X :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  exact ⟨himage,hD,⟨equiv⟩,Nat.card_congr equiv.toEquiv⟩

public theorem native_coprime_quotient_fixed_ne_bot_of_not_full
    {G : Type*} [Group G] [Finite G] (P R N A : Subgroup G)
    (hNR : N≤R) (hPR : P≤normalizer (R:Set G)) (hPN : P≤normalizer (N:Set G))
    (hAP : A≤P) (hsolv : Group.IsSolvable R)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hN : (N.subgroupOf R).Normal) :
    let _ := hN
    ∀ action : P→*MulAut (R ⧸ N.subgroupOf R),
      (∀ p:P,∀ r:R,action p (QuotientGroup.mk' (N.subgroupOf R) r)=
        QuotientGroup.mk' (N.subgroupOf R)
          ⟨(p:G)*(r:G)*(p:G)⁻¹,(mem_normalizer_iff.mp (hPR p.property) r).mp r.property⟩) →
      let _ : MulDistribMulAction A (R ⧸ N.subgroupOf R) :=
        MulDistribMulAction.compHom _ (action.comp (inclusion hAP))
      R≠⁅R,A⁆⊔N → FixedPoints.subgroup A (R ⧸ N.subgroupOf R)≠⊥ := by
  let _ := hN
  dsimp only
  intro action haction
  let X := R ⧸ N.subgroupOf R
  let π : R→*X := QuotientGroup.mk' (N.subgroupOf R)
  let _ : MulDistribMulAction A X := MulDistribMulAction.compHom X (action.comp (inclusion hAP))
  intro hnot hbot
  have himage := (native_coprime_quotient_fixed_card P R N A
    hNR hPR hPN hAP hsolv hcop hN action haction).1
  have hcentral : R⊓centralizer (A:Set G)≤N := by
    intro r hr
    have hh : π (⟨r,hr.1⟩:R)∈FixedPoints.subgroup A X := by
      rw [himage]
      exact mem_map_of_mem π hr
    rw [hbot,mem_bot] at hh
    change (⟨r,hr.1⟩:R)∈N.subgroupOf R
    exact (QuotientGroup.eq_one_iff _).mp hh
  apply hnot
  apply le_antisymm
  · have hdecomp := eq_commutator_sup_centralizer_of_solvable_coprime R A (hAP.trans hPR) hsolv hcop
    exact hdecomp.le.trans (sup_le le_sup_left (hcentral.trans le_sup_right))
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp (hAP.trans hPR)) hNR
end Subgroup
