module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.F918
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.InH
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComplementAction
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer

/-!
# The noncyclic odd complement automizer

The two commuting, disjoint dihedral factors in original 14.6.12 give a
four-group in H/O₂(H), so its Sylow two-subgroup is not cyclic. The literal
quotient map intertwines conjugation on O²(H)/O₂(O²(H)) with conjugation on
the residual in H/O₂(H). Residual self-centralization identifies their
kernels. The existing complement-action equivalence therefore makes the
actual complement automizer noncyclic.

The invariant source sieves use this at both three and five to exclude
the symplectic row of 1.3.4, without
assuming any part of the closure classification. The original exchanged
factor input is supplied by qt-e-14612-singleton.

Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033, citing 14.6.12.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

private theorem not_cyclic_sylow_of_dihedral_pair
    {n : ℕ} [NeZero n] (A B : Subgroup G) (hd : Disjoint A B)
    (hc : A ≤ centralizer (B : Set G)) (eA : A ≃* DihedralGroup n)
    (eB : B ≃* DihedralGroup n) (S : Sylow 2 G) : ¬ IsCyclic S := by
  intro hs
  let := hs
  let R : Subgroup (DihedralGroup n) := zpowers (DihedralGroup.sr 0)
  have hR : Nat.card R = 2 := by
    rw [Nat.card_zpowers,DihedralGroup.orderOf_sr]
  let i : R × R →* DihedralGroup n × DihedralGroup n := R.subtype.prodMap R.subtype
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  let f : R × R →* G := (A ⊔ B).subtype.comp
    ((e.toMonoidHom.comp (eA.symm.prodCongr eB.symm).toMonoidHom).comp i)
  have hf : Function.Injective f := (A ⊔ B).subtype_injective.comp
    (e.injective.comp ((eA.symm.prodCongr eB.symm).injective.comp (by
      intro x y hxy
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hxy)
      · exact Subtype.ext (congrArg Prod.snd hxy))))
  have hp : IsPGroup 2 (R × R) := IsPGroup.of_card (n := 2)
    (by rw [Nat.card_prod,hR]; norm_num)
  obtain ⟨S',hS'⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let : IsCyclic S' := isCyclic_of_injective (S'.equiv S).toMonoidHom (S'.equiv S).injective
  let : IsCyclic f.range := Subgroup.isCyclic_of_le hS'
  let : IsCyclic (R × R) := isCyclic_of_injective (MonoidHom.ofInjective hf).toMonoidHom
    (MonoidHom.ofInjective hf).injective
  have hh : (Nat.card R).Coprime (Nat.card R) := coprime_card_of_isCyclic_prod (M := R) (N := R)
  rw [hR] at hh
  norm_num at hh

/-- The literal quotient Sylow has a noncyclic four-subgroup from the two
commuting dihedral factors. This uses only the exchanged-factor setup. -/
theorem exchanged_odd_quotient_sylow_not_cyclic
    {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    ¬ IsCyclic ((T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
  let : NeZero p := ⟨by rcases d.prime with h | h <;> omega⟩
  obtain ⟨e1⟩ := d.first_model
  obtain ⟨e2⟩ := d.second_model
  exact not_cyclic_sylow_of_dihedral_pair (actorImage H H1) (actorImage H H2)
    d.actors_disjoint (fun x hx y hy => (d.actors_commute x hx y hy).symm) e1 e2 _

/-- On a two-core-free quotient with odd residual, the Sylow conjugation
action on that residual has the same kernel as the literal quotient map. -/
theorem odd_residual_quotient_action_kernel
    (H : Subgroup G) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (p : ℕ) [Fact p.Prime] (ho : Odd p) (hprim : PrimitiveResidual H p)
    (hn : (T : Subgroup G) ≤ normalizer (residual H : Set G)) :
    let α := (quotientAut (pCore 2 (residual H))).comp
      ((residual H).normalizerMonoidHom.comp (inclusion hn))
    let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hTH)
    α.ker = f.ker := by
  let R := pResidual 2 (H ⧸ pCore 2 H)
  let := hprim.elementary
  obtain ⟨e,he⟩ := residual_quotient_equiv ho H
    (IsElementaryAbelian.isPGroup p R)
  let α := (quotientAut (pCore 2 (residual H))).comp
    ((residual H).normalizerMonoidHom.comp (inclusion hn))
  let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hTH)
  have heq (t : T) (v : XiQuotient (residual H)) :
      (e (α t v) : H ⧸ pCore 2 H) = f t * (e v : H ⧸ pCore 2 H) * (f t)⁻¹ := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (residual H)) v
    change (e (quotientAut (pCore 2 (residual H)) _
      (QuotientGroup.mk' (pCore 2 (residual H)) x)) : H ⧸ pCore 2 H) = _
    rw [quotientAut_apply_mk,he,he]
    dsimp only [f,MonoidHom.comp_apply]
    rw [←map_inv,←map_mul,←map_mul]
    rfl
  have hdis : Disjoint f.range R := by
    exact (T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective).disjoint_of_coprime
      (IsElementaryAbelian.isPGroup p R) (Nat.coprime_two_left.mpr ho)
  ext t
  change α t = 1 ↔ f t = 1
  constructor
  · intro ht
    have hc : f t ∈ centralizer (R : Set (H ⧸ pCore 2 H)) := by
      intro r hr
      obtain ⟨v,hv⟩ := e.surjective ⟨r,hr⟩
      have hh := heq t v
      rw [ht] at hh
      have hv' : (e v : H ⧸ pCore 2 H) = r := congrArg Subtype.val hv
      change (e v : H ⧸ pCore 2 H) = f t * (e v : H ⧸ pCore 2 H) * (f t)⁻¹ at hh
      rw [hv'] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    exact hdis.le_bot ⟨⟨t,rfl⟩,
      centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2) hc⟩
  · intro ht
    apply MulEquiv.ext
    intro v
    apply e.injective
    apply Subtype.ext
    change (e (α t v) : H ⧸ pCore 2 H) = (e v : H ⧸ pCore 2 H)
    simpa only [ht,one_mul,inv_one,mul_one] using heq t v

/-- The complement automizer in the original odd-prime input is noncyclic.
The actual quotient map intertwines its action with the faithful quotient
Sylow action, whose dihedral pair contains a four-group. -/
theorem exchanged_odd_automizer_not_cyclic
    {H U Z Mc P : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ∈ Chapter1.H G) (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (h : LocalInput p (T : Subgroup G) (residual H) P Mc) :
    ¬ IsCyclic (automizer (T : Subgroup G) P) := by
  intro hc
  let : Fact p.Prime := ⟨h.prime⟩
  have ho : Odd p := by rcases d.prime with h | h <;> rw [h] <;> decide
  have hXi := residual_mem_Xi T H hTH hH ho hprim d.residual_card
  obtain ⟨P',hP'⟩ := h.sylow
  have hgen : residual H ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
    simpa only [GenerationOne.residual,Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  have hSyl : IsSylowIn 2 (T : Subgroup G) (residual H ⊔ (T : Subgroup G)) := by
    rw [hgen]
    exact ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  let α := (quotientAut (pCore 2 (residual H))).comp
    ((residual H).normalizerMonoidHom.comp (inclusion hXi.invariant))
  let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hTH)
  let e := Chapter15.Section04.LocalSetup.complement_automizer_equiv_quotient_action
    hXi hSyl ho h.quotient P'
  have hcy : IsCyclic α.range := by
    have hc' : IsCyclic (automizer (T : Subgroup G) ((P' : Subgroup (residual H)).map (residual H).subtype)) :=
      hP'.symm ▸ hc
    let := hc'
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  let := hcy
  have hk : α.ker = f.ker := odd_residual_quotient_action_kernel H T hTH p ho hprim hXi.invariant
  let er := (QuotientGroup.quotientKerEquivRange α).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange f))
  have hcf : IsCyclic f.range := isCyclic_of_surjective er.toMonoidHom er.surjective
  apply exchanged_odd_quotient_sylow_not_cyclic a T hTH p H0 H1 H2 d
  have he : f.range = ((T.subtype hTH).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 H)) : Subgroup (H ⧸ pCore 2 H)) := by
    change f.range = ((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
    rw [MonoidHom.range_comp,inclusion_range]
  exact he ▸ hcf

/-- The original cubic specialization, retaining its public interface. -/
theorem exchanged_quotient_sylow_not_cyclic
    {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2) :
    ¬ IsCyclic ((T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) :=
  exchanged_odd_quotient_sylow_not_cyclic a T hTH 3 H0 H1 H2 d

/-- The original cubic specialization, retaining its public interface. -/
theorem residual_quotient_action_kernel
    (H : Subgroup G) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (hprim : PrimitiveResidual H 3)
    (hn : (T : Subgroup G) ≤ normalizer (residual H : Set G)) :
    let α := (quotientAut (pCore 2 (residual H))).comp
      ((residual H).normalizerMonoidHom.comp (inclusion hn))
    let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hTH)
    α.ker = f.ker :=
  odd_residual_quotient_action_kernel H T hTH 3 (by decide) hprim hn

/-- The original cubic specialization, retaining its public interface. -/
theorem exchanged_cubic_automizer_not_cyclic
    {H U Z Mc P : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ∈ Chapter1.H G) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (h : LocalInput 3 (T : Subgroup G) (residual H) P Mc) :
    ¬ IsCyclic (automizer (T : Subgroup G) P) :=
  exchanged_odd_automizer_not_cyclic a T hTH hH 3 H0 H1 H2 hprim d h
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
