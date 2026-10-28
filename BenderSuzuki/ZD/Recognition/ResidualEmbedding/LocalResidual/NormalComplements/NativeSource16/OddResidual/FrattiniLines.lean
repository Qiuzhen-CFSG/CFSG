module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.CoprimeGeneration
public import Theory.GroupAction.OddFixedPlane
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Fixed lines in the odd Frattini quotient

For an involution on an odd elementary group, its fixed and inverted subgroups
form a direct product. If both are cyclic and the group is noncyclic, each is
of order p and the group has order p². This supplies the cardinal conclusions
in GLS IV, Chapter 2, Proposition 16.5 from cyclicity of the literal fixed
commutator subgroups, rather than assuming a two-dimensional quotient.
-/

namespace BenderSuzuki.ZD.Source16OddResidual
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

private theorem fixed_product_card {E : Type*} [Group E] [Finite E]
    [IsMulCommutative E] (ho : Odd (Nat.card E)) (a τ : MulAut E)
    (ha : Function.Involutive a) (hτ : ∀x, τ x=x⁻¹) :
    Nat.card E = Nat.card a.fixedSubgroup * Nat.card (τ*a).fixedSubgroup := by
  have hinv (x : E) : x ∈ (τ*a).fixedSubgroup ↔ a x=x⁻¹ := by
    rw [MulAut.mem_fixedSubgroup]
    change τ (a x)=x ↔ _
    rw [hτ, inv_eq_iff_eq_inv]
  have hd : Disjoint a.fixedSubgroup (τ*a).fixedSubgroup := by
    apply disjoint_def.mpr
    intro x hx hy
    have he : x=x⁻¹ := ((MulAut.mem_fixedSubgroup _ _).mp hx).symm.trans ((hinv x).mp hy)
    have hs : x^2=1 := by rw [pow_two,eq_inv_iff_mul_eq_one.mp he]
    have hi := Nat.eq_one_of_dvd_coprimes ho.coprime_two_right
      (orderOf_dvd_natCard x) (orderOf_dvd_of_pow_eq_one hs)
    exact orderOf_eq_one_iff.mp hi
  have ht : a.fixedSubgroup ⊔ (τ*a).fixedSubgroup=⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨⟨y,z⟩,⟨hy,hz,he⟩,_⟩ := existsUnique_fixed_inverted_mul_of_odd_card ho a ha x
    rw [←he]
    exact (a.fixedSubgroup ⊔ (τ*a).fixedSubgroup).mul_mem
      ((show a.fixedSubgroup ≤ a.fixedSubgroup ⊔ (τ*a).fixedSubgroup from le_sup_left) ((MulAut.mem_fixedSubgroup _ _).mpr hy)) ((show (τ*a).fixedSubgroup ≤ a.fixedSubgroup ⊔ (τ*a).fixedSubgroup from le_sup_right) ((hinv z).mpr hz))
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint a.fixedSubgroup (τ*a).fixedSubgroup
    le_normalizer_of_normal hd
  simpa only [ht, Nat.card_congr (topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv] using hc

private theorem cyclic_elementary_card_le {E : Type*} [Group E] [Finite E]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p E] [IsCyclic E] : Nat.card E ≤ p := by
  have hd := IsElementaryAbelian.exponent_dvd_p p E
  rw [IsCyclic.exponent_eq_card] at hd
  exact Nat.le_of_dvd (Fact.out : p.Prime).pos hd

/-- Cyclic complementary fixed subgroups in a noncyclic elementary group
are actual p-lines, so their product has order p². -/
public theorem fixed_lines_of_cyclic {E : Type*} [Group E] [Finite E]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p E]
    (hp : Odd p) (a τ : MulAut E) (ha : Function.Involutive a)
    (hτ : ∀x, τ x=x⁻¹) (hc : IsCyclic a.fixedSubgroup)
    (hcτ : IsCyclic (τ*a).fixedSubgroup) (hn : ¬IsCyclic E) :
    Nat.card E=p^2 ∧ Nat.card a.fixedSubgroup=p ∧ Nat.card (τ*a).fixedSubgroup=p := by
  let := hc
  let := hcτ
  have hpG := IsElementaryAbelian.isPGroup p E
  obtain ⟨k,hk⟩ := hpG.exists_card_eq
  have hk2 : 2≤k := by
    by_contra hlt
    have hcases : k=0 ∨ k=1 := by omega
    rcases hcases with rfl | rfl
    · have : Subsingleton E := Nat.card_eq_one_iff_unique.mp (by simpa using hk) |>.1
      exact hn (by infer_instance)
    · apply hn
      exact isCyclic_of_prime_card (by simpa using hk)
  have hge : p^2≤Nat.card E := by rw [hk]; exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk2
  have ho : Odd (Nat.card E) := by rw [hk]; exact hp.pow
  have he := fixed_product_card ho a τ ha hτ
  have hsub (H : Subgroup E) : IsElementaryAbelian p H := by
    refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) (x:E)
  let := hsub a.fixedSubgroup
  let := hsub (τ*a).fixedSubgroup
  have h1 : Nat.card a.fixedSubgroup≤p := cyclic_elementary_card_le
  have h2 : Nat.card (τ*a).fixedSubgroup≤p := cyclic_elementary_card_le
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  have hEq : Nat.card E=p^2 := Nat.le_antisymm (by rw [he,pow_two]; exact Nat.mul_le_mul h1 h2) hge
  refine ⟨hEq,?_,?_⟩ <;> nlinarith

end BenderSuzuki.ZD.Source16OddResidual
