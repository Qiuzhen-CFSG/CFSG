module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceFusion
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.CosetIdentification
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# The Sylow involution calculation in Corollary 16.6

The literal omega containment Ω₁(T₁) ≤ Q⟨u⟩ and transitivity on Q minus
identity give the three centralizer classes. Together with global fusion,
the same containment forces every four-group to meet the distinguished set:
two elements in its complementary coset multiply into Q.

Source: GLS IV, Chapter 2, Corollary 16.6(c,d). The earlier omega containment
and Q-conjugacy remain explicit source inputs, not an asserted completion
of the centralizer recognition argument.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

public theorem source16_centralizer_census_of_sylow_omega
    (h : IsProductDisconnected Z M) {u z : G}
    (hu : PFAppendixIII.IsInvolution u) (hz : z ∈ Z)
    (T : Sylow 2 (centralizer ({u} : Set G))) (Q : Subgroup G)
    (hQB : Q ≤ centralizer ({u} : Set G))
    (hOmega : ∀ w : T, PFAppendixIII.IsInvolution ((w : centralizer ({u} : Set G)) : G) →
      ((w : centralizer ({u} : Set G)) : G) ∈ Q ⊔ zpowers u)
    (hQclass : ∀ q ∈ Q, q ≠ 1 →
      ∃ b ∈ centralizer ({u} : Set G), MulAut.conj b q = z) :
    ∀ v ∈ centralizer ({u} : Set G), PFAppendixIII.IsInvolution v →
      v = u ∨ v ∈ Z ∨ IsConj (u * z) v := by
  intro v hvB hv
  let B := centralizer ({u} : Set G)
  let vB : B := ⟨v, hvB⟩
  have hvord : orderOf vB = 2 ^ 1 := by
    rw [← Subgroup.orderOf_coe]
    simpa only [pow_one] using orderOf_eq_prime hv.sq_eq_one hv.ne_one
  obtain ⟨w, hw⟩ := T.exists_isConj_of_orderOf_eq_prime_pow hvord
  let x : G := (w : B)
  have hvx : IsConj v x := B.subtype.map_isConj hw
  obtain ⟨b, hb⟩ := isConj_iff.mp hw
  have hbval : MulAut.conj (b : G) v = x := congrArg B.subtype hb
  have hxi : PFAppendixIII.IsInvolution x := by
    have hh := IsInvolution.map_of_injective hv (MulAut.conj (b : G)).toMonoidHom
      (MulAut.conj (b : G)).injective
    change PFAppendixIII.IsInvolution (MulAut.conj (b : G) v) at hh
    rwa [hbval] at hh
  have hbu : MulAut.conj (b : G) u = u := by
    rw [MulAut.conj_apply, mem_centralizer_singleton_iff.mp b.property, mul_assoc, mul_inv_cancel, mul_one]
  have hdist (q : G) (hq : q ∈ Q) (hqn : q ≠ 1) : q ∈ Z := by
    obtain ⟨c, hcB, hc⟩ := hQclass q hq hqn
    have hh := h.invariant c⁻¹ z hz
    rw [← hc] at hh
    simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hh
  rcases LocalCosetIdentification.mem_sup_involution_cosets hu hQB (hOmega w hxi) with hxQ | huxQ
  · right; left
    have hxZ := hdist x hxQ hxi.ne_one
    have hh := h.invariant (b : G)⁻¹ x hxZ
    rw [← hbval] at hh
    simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hh
  · by_cases hux : u * x = 1
    · left
      have hxu : x = u := by
        exact (eq_inv_of_mul_eq_one_right hux).trans hu.inv_eq_self
      exact (MulAut.conj (b : G)).injective (hbval.trans (hxu.trans hbu.symm))
    · right; right
      obtain ⟨c, hcB, hc⟩ := hQclass (u*x) huxQ hux
      have hcu : MulAut.conj c u = u := by
        rw [MulAut.conj_apply, mem_centralizer_singleton_iff.mp hcB,
          mul_assoc, mul_inv_cancel, mul_one]
      have hcx : MulAut.conj c x = u*z := by
        have hh := congrArg (fun a : G => u*a) hc
        rw [map_mul, hcu, ← mul_assoc, show u*u=1 from by simpa only [pow_two] using hu.sq_eq_one,
          one_mul] at hh
        exact hh
      exact (hvx.trans (isConj_iff.mpr ⟨c,hcx⟩)).symm

public theorem source16_four_meets_distinguished
    (h : IsProductDisconnected Z M) {u : G} (hu : PFAppendixIII.IsInvolution u)
    (hclasses : ∀ v : G, PFAppendixIII.IsInvolution v → v ∈ Z ∨ IsConj u v)
    (T : Sylow 2 (centralizer ({u} : Set G))) (Q : Subgroup G)
    (hQB : Q ≤ centralizer ({u} : Set G))
    (hOmega : ∀ w : T, PFAppendixIII.IsInvolution ((w : centralizer ({u} : Set G)) : G) →
      ((w : centralizer ({u} : Set G)) : G) ∈ Q ⊔ zpowers u)
    (hQZ : ∀ q ∈ Q, q ≠ 1 → q ∈ Z)
    (E : Subgroup G) (hE : Nat.card E = 4) (hEsq : ∀ x : E, x ^ 2 = 1) :
    ∃ z ∈ E, z ∈ Z := by
  by_contra hnone
  have hEZ : ∀ x : E, (x : G) ∉ Z := fun x hx => hnone ⟨x, x.property, hx⟩
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : E)
  have hai : PFAppendixIII.IsInvolution (a : G) :=
    ⟨fun he => ha (Subtype.ext he), congrArg E.subtype (hEsq a)⟩
  have hua := (hclasses a hai).resolve_left (hEZ a)
  obtain ⟨g, hg⟩ := isConj_iff.mp hua.symm
  let e := MulAut.conj g
  have hea : e (a : G) = u := hg
  let B := centralizer ({u} : Set G)
  have hEB (x : E) : e (x : G) ∈ B := by
    apply mem_centralizer_singleton_iff.mpr
    have hc : Commute (x : G) (a : G) := congrArg E.subtype
      (Commute.of_orderOf_dvd_two (fun y : E => orderOf_dvd_of_pow_eq_one (hEsq y)) x a).eq
    have hh := hc.map e.toMonoidHom
    change Commute (e (x : G)) (e (a : G)) at hh
    simpa only [hea] using hh.eq
  let f₁ : E →* B := (e.toMonoidHom.comp E.subtype).codRestrict B hEB
  have hf₁ : Function.Injective f₁ := by
    intro x y he
    exact Subtype.ext (e.injective (congrArg B.subtype he))
  have hPE : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by simpa using hE)
  obtain ⟨P, hP⟩ := (hPE.of_surjective f₁.rangeRestrict f₁.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B P T
  let f : E →* G := B.subtype.comp ((MulAut.conj b).toMonoidHom.comp f₁)
  have hfinj : Function.Injective f := B.subtype_injective.comp
    ((MulAut.conj b).injective.comp hf₁)
  have hfT (x : E) : MulAut.conj b (f₁ x) ∈ (T : Subgroup B) := by
    rw [← hb, Sylow.coe_subgroup_smul]
    exact Set.mem_smul_set.mpr ⟨f₁ x, hP ⟨x, rfl⟩, rfl⟩
  have hfZ (x : E) : f x ∉ Z := by
    intro hx
    have hback := h.invariant g⁻¹ (MulAut.conj (b : G)⁻¹ (f x))
      (h.invariant (b : G)⁻¹ (f x) hx)
    apply hEZ x
    simpa only [f, f₁, e, MonoidHom.comp_apply, MonoidHom.codRestrict_apply,
      Subgroup.subtype_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hback
  have hcoset (x : E) (hx : x ≠ 1) : u * f x ∈ Q := by
    have hfi : PFAppendixIII.IsInvolution (f x) :=
      ⟨fun he => hx (hfinj (he.trans f.map_one.symm)), by rw [← map_pow, hEsq x, map_one]⟩
    rcases LocalCosetIdentification.mem_sup_involution_cosets hu hQB (hOmega ⟨MulAut.conj b (f₁ x), hfT x⟩ hfi)
      with hQ | hQ
    · exact False.elim (hfZ x (hQZ _ hQ hfi.ne_one))
    · exact hQ
  have haord : orderOf a = 2 := orderOf_eq_prime (hEsq a) ha
  have hnle : ¬ (⊤ : Subgroup E) ≤ zpowers a := by
    intro hh
    have hc := card_le_of_le hh
    rw [Subgroup.card_top, Nat.card_zpowers, haord, hE] at hc
    omega
  obtain ⟨c, _, hc⟩ := SetLike.not_le_iff_exists.mp hnle
  have hc1 : c ≠ 1 := fun he => hc (he ▸ (zpowers a).one_mem)
  have hca : c ≠ a := fun he => hc (he ▸ mem_zpowers a)
  have hac : a*c ≠ 1 := by
    intro he
    have he' : c = a⁻¹ := eq_inv_of_mul_eq_one_right he
    exact hca (he'.trans (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hEsq a)))
  have hfca : Commute (f a) u := mem_centralizer_singleton_iff.mp ((MulAut.conj b (f₁ a)).property)
  have hprod : f (a*c) ∈ Q := by
    have hm := Q.mul_mem (hcoset a ha) (hcoset c hc1)
    have he : (u * f a) * (u * f c) = f (a*c) := by
      calc
        (u * f a) * (u * f c) = u * (f a * u) * f c := by group
        _ = u * (u * f a) * f c := by rw [hfca.eq]
        _ = (u*u) * (f a * f c) := by group
        _ = f (a*c) := by
          rw [show u*u=1 from by simpa only [pow_two] using hu.sq_eq_one, one_mul, map_mul]
    rwa [he] at hm
  exact hfZ (a*c) (hQZ _ hprod (fun he => hac (hfinj (he.trans f.map_one.symm))))

end BenderSuzuki.ZD
