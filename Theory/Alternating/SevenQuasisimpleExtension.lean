module

public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.GeneralizedFitting.InnerAutomorphisms
public import Mathlib.GroupTheory.Sylow

/-!
# Ambient extensions of quasisimple covers of A₇

Conjugation on the literal central quotient embeds an ambient extension,
modulo the embedded component center, in Aut(A₇) = S₇. Self-centralization
of the generalized Fitting subgroup identifies the inverse image of A₇
with the component. A proper extension maps onto S₇, and its commutator
subgroup is the original perfect component. For the triple cover, the
proved outer action on the cubic Schur multiplier gives inversion of
every element of the actual kernel.

Source: GLS3 5.2.1 and 5.2.7, and Aschbacher–Smith F.6.18(9), printed p.310.
The record below retains the source quotient and sign action and does not
assert that an arbitrary cubic extension splits.
-/

public section
open Subgroup Theory.GroupTheory Equiv
noncomputable section
namespace Theory.AlternatingSevenExtension
variable {G : Type*} [Group G] [Finite G]

/-- The genuine conjugation equivalence S₇ ≃ Aut(A₇). -/
noncomputable def autEquiv : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))

/-- Conjugation on the original component central quotient, as permutations. -/
noncomputable def action (K : Subgroup G) [K.Normal]
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) : G →* Perm (Fin 7) :=
  autEquiv.symm.toMonoidHom.comp ((MulAut.centralQuotientAction e).comp MulAut.conjNormal)

omit [Finite G] in
/-- Component elements act as their literal images in A₇. -/
lemma action_on_subgroup (K : Subgroup G) [K.Normal]
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) (k : K) :
    action K e k = (e (QuotientGroup.mk' (center K) k) : Perm (Fin 7)) := by
  apply autEquiv.injective
  change autEquiv (autEquiv.symm _) = MulAut.conjNormal _
  rw [autEquiv.apply_symm_apply, MonoidHom.comp_apply, MulAut.conjNormal_val, MulAut.centralQuotientAction_conj,
    MulAut.conjNormal_val]

/-- The inverse image of the alternating subgroup is the original component. -/
lemma action_preimage (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hF : generalizedFitting G = K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) :
    (alternatingGroup (Fin 7)).comap (action K e) = K := by
  have hC : centralizer (K : Set G) ≤ K := hF ▸ centralizer_generalizedFitting_le G
  ext g
  constructor
  · intro hg
    let a : alternatingGroup (Fin 7) := ⟨action K e g, hg⟩
    have ha : MulAut.centralQuotientAction e (MulAut.conjNormal g : MulAut K) = MulAut.conj a := by
      have hh := autEquiv.apply_symm_apply
        (MulAut.centralQuotientAction e (MulAut.conjNormal g : MulAut K))
      change MulAut.conjNormal (action K e g) = _ at hh
      exact hh.symm.trans (MulAut.conjNormal_val (h := a))
    obtain ⟨k, hk⟩ := (MulAut.centralQuotientAction_inner_iff e _).mp ⟨a, ha⟩
    have hi : g ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal := ⟨k, hk.symm⟩
    rw [MulAut.conjNormal_comap_innerSubgroup] at hi
    exact (sup_le le_rfl hC) hi
  · intro hg
    change action K e (⟨g, hg⟩ : K) ∈ alternatingGroup (Fin 7)
    rw [action_on_subgroup]
    exact (e (QuotientGroup.mk' (center K) ⟨g, hg⟩)).property

/-- The action kernel is exactly the center of the component inside G. -/
lemma action_ker (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hF : generalizedFitting G = K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) :
    (action K e).ker = (center K).map K.subtype := by
  have hC : centralizer (K : Set G) ≤ K := hF ▸ centralizer_generalizedFitting_le G
  rw [action, MonoidHom.ker_comp_of_injective _ _ autEquiv.symm.injective,
    MonoidHom.ker_comp_of_injective _ _ (MulAut.centralQuotientAction_injective e),
    MulAut.conjNormal_ker_eq_centralizer]
  ext g
  constructor
  · intro hg
    refine ⟨⟨g, hC hg⟩, ?_, rfl⟩
    change (⟨g, hC hg⟩ : K) ∈ center K
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hg k k.property)
  · rintro ⟨k, hk, rfl⟩ l hl
    exact congrArg Subtype.val (mem_center_iff.mp hk ⟨l, hl⟩)

/-- A proper extension has the full symmetric group as its image. -/
lemma action_surjective (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hF : generalizedFitting G = K) (hne : K ≠ ⊤)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) :
    Function.Surjective (action K e) := by
  let f := action K e
  have heven : ∀ a : alternatingGroup (Fin 7), ∃ k : K, f k = a := by
    intro a
    obtain ⟨q, hq⟩ := e.surjective a
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (center K) q
    exact ⟨k, (action_on_subgroup K e k).trans (congrArg Subtype.val (by rw [hk, hq]))⟩
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ K := by
    by_contra! h
    exact hne (top_unique (fun g _ => h g))
  have hodd : Perm.sign (f g) = -1 := by
    rcases Int.units_eq_one_or (Perm.sign (f g)) with he | he
    · exfalso
      apply hg
      rw [← action_preimage K hF e]
      exact he
    · exact he
  intro σ
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
  · obtain ⟨k, hk⟩ := heven ⟨σ, hs⟩
    exact ⟨k, hk⟩
  · have hpar : σ * (f g)⁻¹ ∈ alternatingGroup (Fin 7) := by
      change Perm.sign (σ * (f g)⁻¹) = 1
      rw [map_mul, map_inv, hs, hodd]
      decide
    obtain ⟨k, hk⟩ := heven ⟨σ * (f g)⁻¹, hpar⟩
    refine ⟨k * g, ?_⟩
    rw [map_mul, hk, inv_mul_cancel_right]

/-- The original perfect component is the full ambient derived subgroup. -/
lemma derived_eq (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hF : generalizedFitting G = K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) :
    commutator G = K := by
  have hker : (Perm.sign.comp (action K e)).ker = K := action_preimage K hF e
  apply le_antisymm
  · rw [← hker]
    exact Abelianization.commutator_subset_ker _
  · rw [← Subgroup.commutator_eq_self (H := K)]
    exact Subgroup.commutator_mono le_top le_top


open GLS3.Chapter5 GLS3.Chapter5.OddCentralCovers

/-- Every outer automorphism of the concrete triple cover inverts its center. -/
lemma tripleSeven_center_inverted (x : MulAut TripleSeven)
    (hout : ∀ k : TripleSeven, x ≠ MulAut.conj k) :
    ∀ z : TripleSeven, z ∈ center TripleSeven → x z = z⁻¹ := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let e : TripleSeven ⧸ center TripleSeven ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq
      tripleSevenCovering.ker_eq_center_of_isSimple.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        tripleSevenCovering.toMonoidHom tripleSevenCovering.surjective)
  obtain ⟨c, _, _, hc, _, horder, hxc⟩ :=
    a7_outer_exists_center_orderThree_inverted tripleSevenCovering
      (Or.inl tripleSevenCovering_kernel_card) x (MulAut.centralQuotientAction e x)
      (fun k => (MulAut.centralQuotientAction_apply e x k).symm) hout
  let cZ : center TripleSeven := ⟨c, hc⟩
  have htop : zpowers cZ = ⊤ := by
    apply eq_top_of_card_eq
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, horder, tripleSeven_center_card]
  intro z hz
  have hm : (⟨z, hz⟩ : center TripleSeven) ∈ zpowers cZ := htop ▸ mem_top _
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hm
  have hn' : c ^ n = z := congrArg Subtype.val hn
  rw [← hn', map_zpow, hxc, inv_zpow]

/-- Center inversion transports to an actual triple-cover model in any universe. -/
lemma center_inverted_of_tripleSeven_model
    {L : Type*} [Group L] (j : L ≃* TripleSeven) (x : MulAut L)
    (hout : ∀ k : L, x ≠ MulAut.conj k) :
    ∀ z : L, z ∈ center L → x z = z⁻¹ := by
  let y : MulAut TripleSeven := MulAut.congr j x
  have hy : ∀ k : TripleSeven, y ≠ MulAut.conj k := by
    intro k hk
    apply hout (j.symm k)
    apply (MulAut.congr j).injective
    rw [MulAut.congr_conj, j.apply_symm_apply]
    exact hk
  intro z hz
  apply j.injective
  simpa only [y, MulAut.congr_apply, MulEquiv.trans_apply, j.symm_apply_apply, map_inv] using
    tripleSeven_center_inverted y hy (j z) ((centerCongr j ⟨z, hz⟩).property)


/-- The literal hatted symmetric extension, retaining its actual kernel and sign action. -/
structure TripleSymmetricExtension (D : Type*) [Group D] where
  kernel : Subgroup D
  [normal : kernel.Normal]
  kernelEquiv : kernel ≃* Multiplicative (ZMod 3)
  quotientEquiv : (D ⧸ kernel) ≃* Perm (Fin 7)
  kernel_le : kernel ≤ commutator D
  derived_perfect : Group.IsPerfect (commutator D)
  derived_center : Nonempty (center (commutator D) ≃* Multiplicative (ZMod 3))
  derived_quotient : Nonempty ((commutator D) ⧸ center (commutator D) ≃*
    alternatingGroup (Fin 7))
  center_eq : (center (commutator D)).map (commutator D).subtype = kernel
  inverse_action : ∀ g : D,
    Perm.sign (quotientEquiv (QuotientGroup.mk' kernel g)) = -1 →
      ∀ z : kernel, g * (z : D) * g⁻¹ = (z : D)⁻¹

attribute [instance] TripleSymmetricExtension.normal

/-- Construct all the literal triple symmetric extension data from the component. -/
noncomputable def tripleExtension (K : Subgroup G) [K.Normal] [IsQuasisimple K]
    (hF : generalizedFitting G = K) (hne : K ≠ ⊤)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7))
    (hc : Nat.card (center K) = 3) : TripleSymmetricExtension G := by
  let f := action K e
  have hf := action_surjective K hF hne e
  have hk := action_ker K hF e
  have hd := derived_eq K hF e
  let q : (G ⧸ f.ker) ≃* Perm (Fin 7) := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hkerCard : Nat.card f.ker = 3 := by
    rw [hk, card_map_of_injective K.subtype_injective, hc]
  have hderivedCard : Nat.card (center (commutator G)) = 3 := by rwa [hd]
  refine {
    kernel := f.ker
    kernelEquiv := mulEquivOfPrimeCardEq hkerCard (by simp)
    quotientEquiv := q
    kernel_le := by rw [hd, hk]; exact map_subtype_le _
    derived_perfect := hd ▸ inferInstance
    derived_center := ⟨mulEquivOfPrimeCardEq hderivedCard (by simp)⟩
    derived_quotient := by cases hd; exact ⟨e⟩
    center_eq := by rw [hd, hk]
    inverse_action := ?_ }
  intro g hg z
  have hout : ∀ k : K, (MulAut.conjNormal g : MulAut K) ≠ MulAut.conj k := by
    intro k hk'
    have hm : g ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal := ⟨k, hk'.symm⟩
    rw [MulAut.conjNormal_comap_innerSubgroup] at hm
    have hC : centralizer (K : Set G) ≤ K := hF ▸ centralizer_generalizedFitting_le G
    have hgK : g ∈ K := (sup_le le_rfl hC) hm
    have heven : Perm.sign (f g) = 1 := by
      change f g ∈ alternatingGroup (Fin 7)
      rw [← action_preimage K hF e] at hgK
      exact hgK
    change Perm.sign (f g) = -1 at hg
    exact (by decide : (1 : ℤˣ) ≠ -1) (heven.symm.trans hg)
  obtain ⟨j⟩ := triple_seven_equiv e hc
  have hz : (z : G) ∈ (center K).map K.subtype := hk ▸ z.property
  obtain ⟨k, hkc, hkz⟩ := hz
  have hi := center_inverted_of_tripleSeven_model j (MulAut.conjNormal g) hout k hkc
  have hiv := congrArg Subtype.val hi
  change g * (k : G) * g⁻¹ = (k : G)⁻¹ at hiv
  change (k : G) = (z : G) at hkz
  rwa [hkz] at hiv


omit [Finite G] in
/-- An odd central cover of A₇ has two-part eight and is proper under a Sylow of order sixteen. -/
lemma proper_of_sylow_sixteen (T : Sylow 2 G) (hT : Nat.card T = 16)
    (K : Subgroup G) (hc : Odd (Nat.card (center K)))
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) : K ≠ ⊤ := by
  intro hK
  have hd : 16 ∣ Nat.card G := hT ▸ (T : Subgroup G).card_subgroup_dvd_card
  have hcK : Nat.card K = 2520 * Nat.card (center K) := by
    rw [(center K).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have heq : Nat.card G = Nat.card K := by rw [hK, Nat.card_congr topEquiv.toEquiv]
  rw [heq, hcK] at hd
  have hcop : Nat.Coprime 16 (Nat.card (center K)) := by
    simpa using hc.coprime_two_left.pow_left 4
  have : 16 ∣ 2520 := hcop.dvd_mul_right.mp hd
  norm_num at this

end Theory.AlternatingSevenExtension
