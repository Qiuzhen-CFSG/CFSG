module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.Basic

/-!
# The disjoint-intersection branch of contrary fusion

For disjoint factors, two commuting conjugates of a factor involution have
their transporter in H. Their elementary two-subgroup lies in H; Sylow
conjugacy inside H places both in S, where the pair action and hypothesis (*)
apply. An outside fusion of an involution would then place every involution
of A₁ in an outside conjugate of H. Applying clause (c) to an actual
four-subgroup of A₁ gives the contradiction. The fused element may belong
to either factor.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the paragraph “Assume first A₁ ∩ A₂ = 1”.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

private theorem into_sylow {H E : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) (hE : IsPGroup 2 E) (hEH : E ≤ H) :
    ∃ k ∈ H, conjugate E k ≤ (S : Subgroup G) := by
  have hp : IsPGroup 2 (E.subgroupOf H) :=
    hE.of_equiv (subgroupOfEquivOfLe hEH).symm
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H Q (S.subtype hSH)
  refine ⟨(k : G)⁻¹, H.inv_mem k.property, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hy : MulAut.conj k (⟨x, hEH hx⟩ : H) ∈ S.subtype hSH := by
    rw [← hk]
    change MulAut.conj k (⟨x, hEH hx⟩ : H) ∈
      (Q : Subgroup H).map (MulAut.conj k).toMonoidHom
    exact mem_map_of_mem _ (hQ hx)
  change (k : G) * x * (k : G)⁻¹ ∈ S at hy
  change (k : G) * x * (k : G)⁻¹ ∈ (S : Subgroup G) at hy
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, inv_inv] using hy

omit [Finite G] in
private theorem commuting_pair_isPGroup {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : Commute a b) :
    IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup G) := by
  have hp (x : G) (hx : orderOf x = 2) : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by simpa [Nat.card_zpowers] using hx)
  apply (hp a ha).to_sup_of_normal_left' (hp b hb)
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  apply zpowers_le.mpr
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact (hab.zpow_left n).eq

private theorem normalizes_of_commuting_disjoint (l : LocalControl S A₁ A₂)
    (hd : A₁ ⊓ A₂ = ⊥) {a b : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hb : b ∈ S) (hab : Commute a b) :
    b ∈ normalizer (A₁ : Set G) := by
  rcases l.permutes_pair b hb with hn | hs
  · exact (mem_normalizer_iff_conjugate_eq _ _).mpr hn.1
  · exfalso
    have he : b⁻¹ * a * b = a := by
      rw [mul_assoc, hab.eq, inv_mul_cancel_left]
    have hx : a ∈ A₁ ⊓ A₂ := by
      rcases ha with ha | ha
      · refine ⟨ha, ?_⟩
        rw [← hs.1]
        exact mem_map.mpr ⟨a, ha, by simpa using he⟩
      · refine ⟨?_, ha⟩
        rw [← hs.2]
        exact mem_map.mpr ⟨a, ha, by simpa using he⟩
    rw [hd, mem_bot] at hx
    exact ha1 hx

theorem LocalControl.transporter_mem_of_commuting_of_disjoint
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    (hd : A₁ ⊓ A₂ = ⊥) {a k : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hc : Commute a (k⁻¹ * a * k)) : k ∈ intersectionGenerated A₁ A₂ := by
  let H := intersectionGenerated A₁ A₂
  let b := k⁻¹ * a * k
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
  have hb2 : orderOf b = 2 := by
    simpa only [b, MulAut.conj_apply, inv_inv] using (MulAut.conj k⁻¹).orderOf_eq a |>.trans ha2
  have haH : a ∈ H := h.union_subset_generated ha
  have hbH : b ∈ H := h.centralizer_le_generated ha ha1
    (mem_centralizer_singleton_iff.mpr hc.symm.eq)
  have hEH : zpowers a ⊔ zpowers b ≤ H :=
    sup_le (zpowers_le.mpr haH) (zpowers_le.mpr hbH)
  obtain ⟨s, hs, hEs⟩ := into_sylow (l.sylow_le_generated h)
    (commuting_pair_isPGroup ha2 hb2 hc) hEH
  have has : s⁻¹ * a * s ∈ S := hEs (mem_map.mpr
    ⟨a, (le_sup_left : zpowers a ≤ zpowers a ⊔ zpowers b) (mem_zpowers a), by simp⟩)
  have hbs : s⁻¹ * b * s ∈ S := hEs (mem_map.mpr
    ⟨b, (le_sup_right : zpowers b ≤ zpowers a ⊔ zpowers b) (mem_zpowers b), by simp⟩)
  have hasU : s⁻¹ * a * s ∈ (A₁ : Set G) ∪ A₂ :=
    h.closed_in_generated.2 a ha s hs
      ⟨H.mul_mem (H.mul_mem (H.inv_mem hs) haH) hs, has⟩
  have has1 : s⁻¹ * a * s ≠ 1 := by
    intro he
    apply ha1
    have hh := congrArg (MulAut.conj s) he
    simpa [MulAut.conj_apply, mul_assoc] using hh
  have hc' : Commute (s⁻¹ * a * s) (s⁻¹ * b * s) := by
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv] using hc.map (MulAut.conj s⁻¹).toMonoidHom
  have hnorm := normalizes_of_commuting_disjoint l hd hasU has1 hbs hc'
  change s⁻¹ * b * s ∈ (S : Subgroup G) at hbs
  have hks : k * s ∈ H := h.transporter_mem_of_left_normalizer ha ha1 (by
    change _ ∈ (S : Subgroup G) ∧ _ ∈ normalizer (A₁ : Set G)
    simpa only [b, mul_inv_rev, mul_assoc] using And.intro hbs hnorm)
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using H.mul_mem hks (H.inv_mem hs)

theorem LocalControl.involution_transporters_of_disjoint
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    (hd : A₁ ⊓ A₂ = ⊥) {a g : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hag : g⁻¹ * a * g ∈ S) : g ∈ intersectionGenerated A₁ A₂ := by
  by_contra hg
  let t := g⁻¹ * a * g
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
  have hswap := l.swap_of_outside_transporter h ha ha1 hg hag
  have ht2 : orderOf t = 2 := by
    simpa only [t, MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq a |>.trans ha2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1)
  obtain ⟨E, hE, hEsq⟩ := h.left_rank
  let X := E.map A₁.subtype
  have hXA : X ≤ A₁ := map_subtype_le E
  have hXcard : Nat.card X = 4 :=
    (card_map_of_injective A₁.subtype_injective).trans hE
  have hXg : conjugate X g⁻¹ ≤ intersectionGenerated A₁ A₂ := by
    rintro _ ⟨v, hv, rfl⟩
    by_cases hv1 : v = 1
    · simp [hv1]
    have hvsq : v ^ 2 = 1 := by
      obtain ⟨w, hw, rfl⟩ := hv
      exact congrArg (fun x : E => ((x : A₁) : G)) (hEsq ⟨w, hw⟩)
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hvsq)
    have hvt : t⁻¹ * v * t ∈ A₂ := by
      rw [← hswap.1]
      exact mem_map.mpr ⟨v, hXA hv, by simp [t, mul_assoc]⟩
    have hcomm : v * (t⁻¹ * v * t) = (t⁻¹ * v * t) * v :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h.commute (hXA hv)) _ hvt).symm
    have hct : Commute t (v⁻¹ * t * v) := by
      change t * (v⁻¹ * t * v) = (v⁻¹ * t * v) * t
      simpa only [htinv, hvinv, mul_assoc] using hcomm.symm
    have hc : Commute a ((g * v * g⁻¹)⁻¹ * a * (g * v * g⁻¹)) := by
      have hh := hct.map (MulAut.conj g).toMonoidHom
      simpa only [t, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MulAut.conj_apply, inv_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left,
        inv_mul_cancel_left, mul_inv_cancel, mul_one] using hh
    have hh := l.transporter_mem_of_commuting_of_disjoint h hd ha ha2 hc
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv] using hh
  have hgi := (l.unique_large X (Or.inl hXA) (by omega)).2 g⁻¹ |>.mp hXg
  exact hg ((intersectionGenerated A₁ A₂).inv_mem_iff.mp hgi)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
