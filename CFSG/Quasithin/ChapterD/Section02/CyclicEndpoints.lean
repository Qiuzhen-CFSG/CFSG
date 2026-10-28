module

public import Stellmacher.SectionOne.InvolutionPGroupSmallIndexClassification
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Theory.GroupAction.FourElementInvolutionLines

/-!
# The p-group-by-involution endpoints in D.2.17

For a faithful action on an elementary abelian two-group, assume that a
nontrivial normal odd p-subgroup R and an involution t generate G, that
[R,t]=R and [V,R]=V, and that the fixed-point index of t is at most four.
The alternatives are C₃ on rank two or four, C₅ or E₉ on rank four, and an
extraspecial group of order 27 and exponent three on rank six.

The audited small-index classification of Stellmacher supplies the kernel
models and dimensions. The abelian kernels are inverted, giving S₃, D₁₀,
and the inversion extension of E₉. In the extraspecial case the involution
fixes the center; fixed/inverted factorization proves exponent three and
inversion on the Frattini quotient. Actual semidirect-product equivalences
retain the action of the order-two generator. The index is two in the
rank-two case and four in every other case.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Theorem D.2.17(1)--(4), printed pp.188--192 (`refs/quasithin.pdf`,
PDF pp.199--203). This module does not assert the global reduction to
G=R⟨t⟩; its consumer must supply that premise. It does not use
Stellmacher's placeholder `lemma_one_six`.
-/

@[expose] public section

open scoped IsMulCommutative
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.Section02
universe u
variable {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
  [IsElementaryAbelian 2 V] [MulDistribMulAction G V]

private theorem rank_of_card {n : ℕ} (hV : Nat.card V = 2 ^ n) :
    Module.finrank (ZMod 2) (Additive V) = n := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  exact (h.trans (by rw [Nat.card_zmod])).symm.trans hV

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem index_of_card_eq (t : G) {n : ℕ}
    (h : Nat.card V = n * Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V)) :
    (FixedPoints.subgroup (Subgroup.zpowers t) V).index = n := by
  have hh := (FixedPoints.subgroup (Subgroup.zpowers t) V).card_mul_index
  rw [h, mul_comm n] at hh
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh

private theorem index_two_of_card_four (t : G) (ht : IsInvolution t)
    (hV : Nat.card V = 4) (hf : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    (FixedPoints.subgroup (Subgroup.zpowers t) V).index = 2 := by
  have hc : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ht.2 ht.1]
  have hn : commutatorAction (Subgroup.zpowers t) V ≠ ⊥ := by
    intro hb
    have htriv := actsTrivially_of_commutatorAction_eq_bot hb
    have hh : t ∈ fixingSubgroup G (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro v _
      exact htriv ⟨t, Subgroup.mem_zpowers t⟩ v
    rw [hf] at hh
    exact ht.1 (Subgroup.mem_bot.mp hh)
  have hh := (four_element_action_fixed_commutator_card_two hc hV hn).1
  apply index_of_card_eq t
  rw [hV, hh]

private theorem extraspecial_endpoint_data
    (R : Subgroup G) [R.Normal] (hR : IsExtraspecial 3 R) (hcard : Nat.card R = 3 ^ 3)
    (t : G) (ht : IsInvolution t) (hne : R ≠ ⊥)
    (hcomm : ⁅R, Subgroup.zpowers t⁆ = R)
    (hZ : ⁅(Subgroup.center R).map R.subtype, Subgroup.zpowers t⁆ = ⊥) :
    Monoid.exponent R = 3 ∧
      ∀ r : R, QuotientGroup.mk' (frattini R) (MulAut.conjNormal t r) =
        (QuotientGroup.mk' (frattini R) r)⁻¹ := by
  let : IsExtraspecial 3 R := hR
  let a : MulAut R := MulAut.conjNormal t
  have ha : Function.Involutive a := by
    intro r
    change (((MulAut.conjNormal : G →* MulAut R) t * MulAut.conjNormal t) : MulAut R) r = r
    rw [← map_mul, ← pow_two, ht.2, map_one]
    rfl
  have han : a ≠ 1 := by
    intro h
    have hz : R ≤ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
      intro r hr
      have hh := congrArg Subtype.val (DFunLike.congr_fun h (⟨r,hr⟩ : R))
      have htr : Commute t r := by
        change t * r * t⁻¹ = r at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨n,rfl⟩ := hz
      exact (htr.zpow_left n).eq
    exact hne (hcomm.symm.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hz))
  have hcenter : ∀ z ∈ Subgroup.center R, a z = z := by
    intro z hz
    have hzC := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZ)
      (show (z : G) ∈ (Subgroup.center R).map R.subtype from ⟨z,hz,rfl⟩)
    have htcomm := Subgroup.mem_centralizer_iff.mp hzC t (Subgroup.mem_zpowers t)
    apply Subtype.ext
    change t * (z : G) * t⁻¹ = (z : G)
    rw [htcomm, mul_inv_cancel_right]
  exact IsExtraspecial.exponent_and_frattini_inversion_of_card27 hcard a ha han hcenter

/-- The cyclic-three endpoint, including the rank-one and rank-two offenders. -/
structure CyclicThreeEndpoint (R : Subgroup G) (t : G) : Prop where
  kernel_equiv : Nonempty (R ≃* Multiplicative (ZMod 3))
  ambient_equiv : Nonempty (G ≃* Equiv.Perm (Fin 3))
  inverts : ∀ r : R, t * (r : G) * t⁻¹ = (r : G)⁻¹
  dimensions :
    (Nat.card V = 4 ∧ Module.finrank (ZMod 2) (Additive V) = 2 ∧
      (FixedPoints.subgroup (Subgroup.zpowers t) V).index = 2) ∨
    (Nat.card V = 16 ∧ Module.finrank (ZMod 2) (Additive V) = 4 ∧
      (FixedPoints.subgroup (Subgroup.zpowers t) V).index = 4)

/-- The cyclic-five endpoint is the dihedral group of order ten. -/
structure CyclicFiveEndpoint (R : Subgroup G) (t : G) : Prop where
  kernel_equiv : Nonempty (R ≃* Multiplicative (ZMod 5))
  ambient_equiv : Nonempty (G ≃* DihedralGroup 5)
  inverts : ∀ r : R, t * (r : G) * t⁻¹ = (r : G)⁻¹
  card_module : Nat.card V = 16
  rank_module : Module.finrank (ZMod 2) (Additive V) = 4
  fixed_index : (FixedPoints.subgroup (Subgroup.zpowers t) V).index = 4

/-- The order-eighteen endpoint, with the inversion action on the concrete `E₉` model. -/
structure ElementaryNineEndpoint (R : Subgroup G) (t : G) : Prop where
  kernel_equiv : Nonempty (R ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
  kernel_elementary : IsElementaryAbelian 3 R
  card_kernel : Nat.card R = 9
  inverts : ∀ r : R, t * (r : G) * t⁻¹ = (r : G)⁻¹
  split : ∃ φ : Multiplicative (ZMod 2) →*
      MulAut (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)),
    (∀ r, φ (Multiplicative.ofAdd 1) r = r⁻¹) ∧
    Nonempty (G ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) ⋊[φ]
      Multiplicative (ZMod 2))
  card_module : Nat.card V = 16
  rank_module : Module.finrank (ZMod 2) (Additive V) = 4
  fixed_index : (FixedPoints.subgroup (Subgroup.zpowers t) V).index = 4

/-- The extraspecial endpoint; the actual extension action fixes the center and
inverts the Frattini quotient. Its base has order 27 and exponent three. -/
structure ExtraspecialEndpoint (R : Subgroup G) [R.Normal] (t : G) : Prop where
  kernel_extraspecial : IsExtraspecial 3 R
  card_kernel : Nat.card R = 27
  exponent_kernel : Monoid.exponent R = 3
  frattini_eq_center : frattini R = Subgroup.center R
  fixes_center : ⁅(Subgroup.center R).map R.subtype, Subgroup.zpowers t⁆ = ⊥
  inverts_frattini : ∀ r : R,
    QuotientGroup.mk' (frattini R) (MulAut.conjNormal t r) =
      (QuotientGroup.mk' (frattini R) r)⁻¹
  split : ∃ φ : Multiplicative (ZMod 2) →* MulAut R,
    (∀ r, φ (Multiplicative.ofAdd 1) r = MulAut.conjNormal t r) ∧
    Nonempty (G ≃* R ⋊[φ] Multiplicative (ZMod 2))
  card_module : Nat.card V = 64
  rank_module : Module.finrank (ZMod 2) (Additive V) = 6
  fixed_index : (FixedPoints.subgroup (Subgroup.zpowers t) V).index = 4

private theorem cyclic_three_model
    (R : Subgroup G) [R.Normal] (e : R ≃* Multiplicative (ZMod 3))
    (hodd : Nat.Coprime 2 (Nat.card R)) (t : G) (ht : IsInvolution t)
    (hgen : R ⊔ Subgroup.zpowers t = ⊤) (hc : ⁅R, Subgroup.zpowers t⁆ = R) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) ∧
      ∀ r : R, t * (r : G) * t⁻¹ = (r : G)⁻¹ := by
  let : IsCyclic R := e.isCyclic.mpr inferInstance
  have hR : Nat.card R = 3 := by
    simpa using Nat.card_congr e.toEquiv
  obtain ⟨d⟩ := odd_involution_dihedral R hodd t ht hgen hc
  rw [hR] at d
  obtain ⟨s⟩ := nonempty_dihedralThreeEquivPerm
  exact ⟨⟨d.trans s⟩, inverts_abelian_of_full_commutator R t ht hc⟩

/-- The p-group-by-involution endpoints of D.2.17(1)--(4), under the explicit
local generation and full-commutator premises. No global reduction or q̂
hypothesis is asserted here. -/
theorem smallSupportClassification
    (R : Subgroup G) [R.Normal] (hne : R ≠ ⊥)
    (p : ℕ) [Fact p.Prime] (hp : IsPGroup p R)
    (hodd : Nat.Coprime 2 (Nat.card R)) (t : G) (ht : IsInvolution t)
    (hgen : R ⊔ Subgroup.zpowers t = ⊤) (hc : ⁅R, Subgroup.zpowers t⁆ = R)
    (hV : commutatorAction R V = ⊤)
    (hi : Nat.card V ≤ 4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V))
    (hf : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    CyclicThreeEndpoint (V := V) R t ∨ CyclicFiveEndpoint (V := V) R t ∨
      ElementaryNineEndpoint (V := V) R t ∨ ExtraspecialEndpoint (V := V) R t := by
  obtain hs | hs | hs := Stellmacher.SectionOne.involutionPGroup_smallIndex_classification
    R inferInstance hne p hp hodd t ht hgen hc hV hi hf
  · obtain ⟨hcard, ⟨e⟩⟩ := hs
    obtain ⟨he, hinv⟩ := cyclic_three_model R e hodd t ht hgen hc
    exact Or.inl ⟨⟨e⟩, he, hinv, Or.inl ⟨hcard, rank_of_card hcard,
      index_two_of_card_four t ht hcard hf⟩⟩
  · obtain ⟨hcard, hindex, h3 | h5 | h9⟩ := hs
    · obtain ⟨e⟩ := h3
      obtain ⟨he, hinv⟩ := cyclic_three_model R e hodd t ht hgen hc
      exact Or.inl ⟨⟨e⟩, he, hinv, Or.inr ⟨hcard, rank_of_card hcard,
        index_of_card_eq t hindex⟩⟩
    · obtain ⟨e⟩ := h5
      let : IsCyclic R := e.isCyclic.mpr inferInstance
      have hR : Nat.card R = 5 := by simpa using Nat.card_congr e.toEquiv
      have he := odd_involution_dihedral R hodd t ht hgen hc
      rw [hR] at he
      exact Or.inr (Or.inl ⟨⟨e⟩, he, inverts_abelian_of_full_commutator R t ht hc,
        hcard, rank_of_card hcard, index_of_card_eq t hindex⟩)
    · obtain ⟨e⟩ := h9
      let : IsMulCommutative R := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
      have hinv := inverts_abelian_of_full_commutator R t ht hc
      have hR : Nat.card R = 9 := by simpa using Nat.card_congr e.toEquiv
      have hel : IsElementaryAbelian 3 R := by
        refine { exponent_dvd_p := ?_ }
        apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        intro r
        apply e.injective
        rw [map_pow, map_one]
        exact (show ∀ x : Multiplicative (ZMod 3) × Multiplicative (ZMod 3),
          x ^ 3 = 1 by decide +kernel) (e r)
      obtain ⟨φ,hφ,he⟩ := odd_involution_semidirect_model R hodd t ht hgen e
      have hinvφ : ∀ r, φ (Multiplicative.ofAdd 1) r = r⁻¹ := by
        intro r
        obtain ⟨x,rfl⟩ := e.surjective r
        rw [hφ, ← map_inv]
        apply congrArg e
        exact Subtype.ext (hinv x)
      exact Or.inr (Or.inr (Or.inl ⟨⟨e⟩, hel, hR, hinv, ⟨φ,hinvφ,he⟩,
        hcard, rank_of_card hcard, index_of_card_eq t hindex⟩))
  · obtain ⟨hcard,hindex,hZ,hR,hRc⟩ := hs
    obtain ⟨hexp,hinv⟩ := extraspecial_endpoint_data R hR hRc t ht hne hc hZ
    let : IsExtraspecial 3 R := hR
    obtain ⟨φ,hφ,he⟩ := odd_involution_semidirect_model R hodd t ht hgen (MulEquiv.refl R)
    exact Or.inr (Or.inr (Or.inr ⟨hR,hRc,hexp,IsExtraspecial.frattini_eq_center_three,
      hZ,hinv,⟨φ,hφ,he⟩,hcard,rank_of_card hcard,index_of_card_eq t hindex⟩))

/-- Index formulation of the endpoint classification. -/
theorem smallSupportClassification_of_index_le_four
    (R : Subgroup G) [R.Normal] (hne : R ≠ ⊥)
    (p : ℕ) [Fact p.Prime] (hp : IsPGroup p R)
    (hodd : Nat.Coprime 2 (Nat.card R)) (t : G) (ht : IsInvolution t)
    (hgen : R ⊔ Subgroup.zpowers t = ⊤) (hc : ⁅R, Subgroup.zpowers t⁆ = R)
    (hV : commutatorAction R V = ⊤)
    (hi : (FixedPoints.subgroup (Subgroup.zpowers t) V).index ≤ 4)
    (hf : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    CyclicThreeEndpoint (V := V) R t ∨ CyclicFiveEndpoint (V := V) R t ∨
      ElementaryNineEndpoint (V := V) R t ∨ ExtraspecialEndpoint (V := V) R t := by
  apply smallSupportClassification R hne p hp hodd t ht hgen hc hV _ hf
  calc
    Nat.card V = Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V) *
        (FixedPoints.subgroup (Subgroup.zpowers t) V).index :=
      (FixedPoints.subgroup (Subgroup.zpowers t) V).card_mul_index.symm
    _ ≤ Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V) * 4 :=
      Nat.mul_le_mul_left _ hi
    _ = _ := Nat.mul_comm _ _

end CFSG.Quasithin.ChapterD.Section02
