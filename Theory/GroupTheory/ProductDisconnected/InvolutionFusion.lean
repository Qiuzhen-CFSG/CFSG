module
public import Theory.GroupTheory.ProductDisconnected
public import Mathlib.GroupTheory.Sylow

/-!
# Product disconnection from involution fusion and local centralizers

Let a subgroup contain an ambient Sylow two-subgroup and control fusion of
involutions. Assume it contains the centralizer of a distinguished involution,
and the centralizers of products of that involution with its distinct commuting
conjugates inside the subgroup. Then its distinguished ambient conjugacy class
is product-disconnected. Sylow conjugacy moves every commuting pair inside;
fusion and a centralizer correction return the conjugator to the subgroup.

Source application: the last paragraphs of Aschbacher--Smith 13.4.9,
printed pp.906--907. The fusion and local centralizers remain mathematical
inputs here; this criterion does not assert the Sp6 source calculations.
-/

public section
namespace Theory.GroupTheory
open Subgroup BenderSuzuki.PFAppendixIII
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conjugate_involution (g : G) {x : G} (hx : IsInvolution x) :
    IsInvolution (MulAut.conj g x) := by
  refine ⟨fun hh => hx.1 ((MulAut.conj g).injective (hh.trans (map_one _).symm)), ?_⟩
  rw [← map_pow, hx.2, map_one]

omit [Finite G] in
private theorem centralizer_conj_le (E : Subgroup G) {g x : G} (hg : g ∈ E)
    (hc : centralizer ({x} : Set G) ≤ E) :
    centralizer ({MulAut.conj g x} : Set G) ≤ E := by
  intro a ha
  have hback : MulAut.conj g⁻¹ a ∈ centralizer ({x} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj g⁻¹) (mem_centralizer_singleton_iff.mp ha)
    simpa [MulAut.conj_apply, mul_assoc] using hh
  have hh := E.mul_mem (E.mul_mem hg (hc hback)) (E.inv_mem hg)
  simpa [MulAut.conj_apply, mul_assoc] using hh

omit [Finite G] in
private theorem conjugator_mem_of_fusion (E : Subgroup G) {x y g : G}
    (hx : x ∈ E) (hy : y ∈ E) (hi : IsInvolution x)
    (hf : ∀ a ∈ E, ∀ b ∈ E, IsInvolution a → IsConj a b →
      ∃ c ∈ E, MulAut.conj c a = b)
    (hc : centralizer ({x} : Set G) ≤ E) (hg : MulAut.conj g x = y) : g ∈ E := by
  obtain ⟨c,hcE,hcx⟩ := hf x hx y hy hi (isConj_iff.mpr ⟨g,hg⟩)
  have hcg : c⁻¹ * g ∈ centralizer ({x} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have he : MulAut.conj (c⁻¹*g) x = x := by
      calc
        MulAut.conj (c⁻¹*g) x = MulAut.conj c⁻¹ (MulAut.conj g x) := by
          simp only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]
        _ = MulAut.conj c⁻¹ (MulAut.conj c x) := by rw [hg,hcx]
        _ = x := by simp [MulAut.conj_apply, mul_assoc]
    exact (mul_inv_eq_iff_eq_mul.mp he)
  have hh := E.mul_mem hcE (hc hcg)
  simpa only [mul_assoc,mul_inv_cancel_left] using hh

private theorem commuting_pair_into_sylow (T : Sylow 2 G) {x y : G}
    (hx : IsInvolution x) (hy : IsInvolution y) (hc : Commute x y) :
    ∃ g : G, MulAut.conj g x ∈ T ∧ MulAut.conj g y ∈ T := by
  have hpx : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx.2)
  have hpy : IsPGroup 2 (zpowers y) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hy.2)
  have hp : IsPGroup 2 (zpowers x ⊔ zpowers y : Subgroup G) := by
    apply hpx.to_sup_of_normal_right' hpy
    apply le_trans _ (centralizer_le_normalizer (zpowers y : Set G))
    apply zpowers_le.mpr
    apply mem_centralizer_iff.mpr
    rintro _ ⟨n,rfl⟩
    exact (hc.zpow_right n).eq.symm
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S T
  refine ⟨g, ?_, ?_⟩
  · rw [← hg]
    exact ⟨x,hS (mem_sup_left (mem_zpowers x)),rfl⟩
  · rw [← hg]
    exact ⟨y,hS (mem_sup_right (mem_zpowers y)),rfl⟩

/-- The literal one-class product-disconnection criterion, including products
whose two factors initially lie outside the subgroup. -/
theorem productDisconnected_of_involution_fusion (E : Subgroup G) (T : Sylow 2 G)
    (hTE : (T : Subgroup G) ≤ E) (hE : E ≠ ⊤) (d : G) (hd : IsInvolution d)
    (hdE : d ∈ E)
    (hf : ∀ a ∈ E, ∀ b ∈ E, IsInvolution a → IsConj a b →
      ∃ c ∈ E, MulAut.conj c a = b)
    (hc : centralizer ({d} : Set G) ≤ E)
    (hp : ∀ e ∈ E, IsConj d e → Commute d e → e ≠ d →
      centralizer ({d*e} : Set G) ≤ E) :
    IsProductDisconnected {x : G | IsConj d x} E := by
  have hinv {x : G} (hx : IsConj d x) : IsInvolution x := by
    obtain ⟨g,rfl⟩ := isConj_iff.mp hx
    exact conjugate_involution g hd
  have hcent {x : G} (hx : IsConj d x) (hxE : x ∈ E) :
      centralizer ({x} : Set G) ≤ E := by
    obtain ⟨g,hg,hgx⟩ := hf d hdE x hxE hd hx
    rw [← hgx]
    exact centralizer_conj_le E hg hc
  have hpair {x y : G} (hx : IsConj d x) (hy : IsConj d y)
      (hxE : x ∈ E) (hyE : y ∈ E) (hxy : IsInvolution (x*y)) :
      centralizer ({x*y} : Set G) ≤ E := by
    have hix := hinv hx
    have hiy := hinv hy
    have hcomm : Commute x y := by
      have hh := hxy.inv_eq_self
      rw [mul_inv_rev,hix.inv_eq_self,hiy.inv_eq_self] at hh
      exact hh.symm
    obtain ⟨g,hg,hgx⟩ := hf x hxE d hdE hix hx.symm
    let e := MulAut.conj g y
    have heE : e ∈ E := E.mul_mem (E.mul_mem hg hyE) (E.inv_mem hg)
    have hde : IsConj d e := hy.trans (isConj_iff.mpr ⟨g,rfl⟩)
    have hdecomm : Commute d e := by
      rw [← hgx]
      exact hcomm.map (MulAut.conj g).toMonoidHom
    have hne : e ≠ d := by
      intro he
      have hyx : y=x := (MulAut.conj g).injective (he.trans hgx.symm)
      apply hxy.1
      rw [hyx,← pow_two,hix.2]
    have hh := hp e heE hde hdecomm hne
    have hprod : MulAut.conj g (x*y) = d*e := by rw [map_mul,hgx]
    have hback := centralizer_conj_le E (E.inv_mem hg) hh
    have heq : MulAut.conj g⁻¹ (d*e) = x*y := by
      rw [← hprod]
      simp [MulAut.conj_apply, mul_assoc]
    rwa [heq] at hback
  refine ⟨fun _ hx => hinv hx, ?_, hE, ⟨d,isConj_iff.mpr ⟨1, by simp⟩,hdE⟩, ?_, ?_⟩
  · intro g x hx
    exact hx.trans (isConj_iff.mpr ⟨g,rfl⟩)
  · intro x hx hxE g
    constructor
    · intro hgx
      exact conjugator_mem_of_fusion E hxE hgx (hinv hx) hf (hcent hx hxE) rfl
    · intro hg
      exact E.mul_mem (E.mul_mem hg hxE) (E.inv_mem hg)
  · intro x hx y hy hxy hxyE
    have hix := hinv hx
    have hiy := hinv hy
    have hcomm : Commute x y := by
      have hh := hxy.inv_eq_self
      rw [mul_inv_rev,hix.inv_eq_self,hiy.inv_eq_self] at hh
      exact hh.symm
    obtain ⟨g,hgx,hgy⟩ := commuting_pair_into_sylow T hix hiy hcomm
    have hcx : IsConj d (MulAut.conj g x) := hx.trans (isConj_iff.mpr ⟨g,rfl⟩)
    have hcy : IsConj d (MulAut.conj g y) := hy.trans (isConj_iff.mpr ⟨g,rfl⟩)
    have hiq := conjugate_involution g hxy
    rw [map_mul] at hiq
    have hq := hpair hcx hcy (hTE hgx) (hTE hgy) hiq
    have hqE := E.mul_mem (hTE hgx) (hTE hgy)
    obtain ⟨c,hcE,hcp⟩ := hf (MulAut.conj g x*MulAut.conj g y) hqE (x*y) hxyE
      hiq (isConj_iff.mpr ⟨g⁻¹,by
        rw [← map_mul]
        simp [MulAut.conj_apply, mul_assoc]⟩)
    have hback := centralizer_conj_le E hcE hq
    rwa [hcp] at hback

end Theory.GroupTheory
