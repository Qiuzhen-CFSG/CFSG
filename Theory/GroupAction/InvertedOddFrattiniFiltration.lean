module

public import Theory.GroupAction.InvertedOddFixedSubgroup
public import Theory.GroupAction.OddTwoGroupFiltration
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.Frattini.PGroup

/-!
# An inverted odd action on an index-two filtration

Let an odd group of automorphisms of a finite two-group S be inverted by w.
Suppose V is characteristic of index two in S and w acts trivially on
V modulo S′. Then the odd group acts trivially on S.

Work first on S/Φ(S). The inverter fixes the image of V, so the inverted
odd group fixes that image too. All automorphisms act trivially on S/V,
which has order two. The odd-action filtration lemma therefore makes the
action on S/Φ(S) trivial. The Frattini automorphism kernel is a two-group,
so it contains no nontrivial odd subgroup.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p.676, the filtration S ≥ Ω₁(S) ≥ S′ in the J−E fusion case.
The centralizer geometry needed for that application is not assumed here.
-/

open Subgroup

namespace MulAut

/-- An inverted odd automorphism group is trivial when the inverter fixes
a characteristic index-two subgroup modulo the derived subgroup. -/
public theorem odd_subgroup_eq_bot_of_inverted_index_two_filtration
    {S : Type*} [Group S] [Finite S] (hS : IsPGroup 2 S)
    (V : Subgroup S) [V.Characteristic] (hindex : V.index = 2)
    (R : Subgroup (MulAut S)) (hodd : Odd (Nat.card R))
    (w : MulAut S) (hinverts : ∀ r ∈ R, w * r * w⁻¹ = r⁻¹)
    (hdisplacement : ∀ v ∈ V, v⁻¹ * w v ∈ _root_.commutator S) : R = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 S) := ⟨hS⟩
  let P := frattini S
  let q := QuotientGroup.mk' P
  let U := V.map q
  let f := quotientAut P
  let : MulDistribMulAction (MulAut S) (S ⧸ P) :=
    MulDistribMulAction.compHom (S ⧸ P) f
  have heval (a : MulAut S) (s : S) : a • q s = q (a s) :=
    quotientAut_apply_mk P a s
  have hstable (a : MulAut S) (v : S) (hv : v ∈ V) : a v ∈ V :=
    (MulAut.characteristic V a ⟨v, hv⟩).property
  have hfixedU : ∀ r ∈ R, ∀ u ∈ U, r • u = u := by
    apply inverted_odd_fixes_invariant_subgroup R hodd w hinverts U
    · intro r _ u hu
      obtain ⟨v, hv, rfl⟩ := hu
      rw [heval]
      exact mem_map_of_mem q (hstable r v hv)
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := hu
      rw [heval]
      exact (QuotientGroup.eq.mpr
        (commutator_le_frattini_of_isPGroup (p := 2) (hdisplacement v hv))).symm
  have htop (a : MulAut S) (s : S) : s⁻¹ * a s ∈ V := by
    rw [V.mul_mem_iff_of_index_two hindex, V.inv_mem_iff]
    constructor
    · exact hstable a s
    · intro hs
      simpa using hstable a⁻¹ (a s) hs
  have htrivial : ∀ r : R, ∀ u : S ⧸ P, r • u = u := by
    apply MulDistribMulAction.trivial_of_odd_of_two_group_filtration hodd
      (hS.to_quotient P) ⊥ U bot_le
    · intro r u hu
      have hu1 : u = 1 := hu
      rw [hu1, smul_one]
    · intro r u hu
      change u⁻¹ * ((r : MulAut S) • u) = 1
      rw [hfixedU r r.property u hu, inv_mul_cancel]
    · intro r u
      obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective P u
      change (q s)⁻¹ * ((r : MulAut S) • q s) ∈ U
      rw [heval, ← map_inv, ← map_mul]
      exact mem_map_of_mem q (htop r s)
  have hker : R ≤ f.ker := by
    intro r hr
    apply MulEquiv.ext
    intro u
    exact htrivial ⟨r, hr⟩ u
  have hRtwo : IsPGroup 2 R :=
    (isPGroup_quotientAut_frattini_kernel hS).to_le hker
  apply bot_unique
  intro r hr
  obtain ⟨n, hn⟩ := hRtwo.exists_orderOf_dvd_pow (⟨r, hr⟩ : R)
  have ho : orderOf (⟨r, hr⟩ : R) = 1 := Nat.eq_one_of_dvd_coprimes
    (hodd.coprime_two_right.pow_right n) (orderOf_dvd_natCard _) hn
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp ho)

end MulAut

namespace Subgroup

/-- Ambient conjugation form of the inverted odd filtration argument.
Both the odd subgroup and its inverter act on the supplied subgroup S. -/
public theorem le_centralizer_of_inverted_odd_index_two_filtration
    {G : Type*} [Group G] [Finite G]
    (S R : Subgroup G) (hS : IsPGroup 2 S)
    (V : Subgroup S) [V.Characteristic] (hindex : V.index = 2)
    (hR : R ≤ normalizer (S : Set G)) (hodd : Odd (Nat.card R))
    (w : normalizer (S : Set G))
    (hinverts : ∀ r ∈ R, (w : G) * r * (w : G)⁻¹ = r⁻¹)
    (hdisplacement : ∀ v ∈ V,
      v⁻¹ * S.normalizerMonoidHom w v ∈ _root_.commutator S) :
    R ≤ centralizer (S : Set G) := by
  let f : R →* MulAut S := S.normalizerMonoidHom.comp (inclusion hR)
  have hinv : ∀ a ∈ f.range,
      S.normalizerMonoidHom w * a * (S.normalizerMonoidHom w)⁻¹ = a⁻¹ := by
    rintro a ⟨r, rfl⟩
    change S.normalizerMonoidHom w * S.normalizerMonoidHom (inclusion hR r) *
      (S.normalizerMonoidHom w)⁻¹ = (S.normalizerMonoidHom (inclusion hR r))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    apply congrArg S.normalizerMonoidHom
    apply Subtype.ext
    exact hinverts r r.property
  have hbot := MulAut.odd_subgroup_eq_bot_of_inverted_index_two_filtration
    hS V hindex f.range (hodd.of_dvd_nat (card_range_dvd f))
    (S.normalizerMonoidHom w) hinv hdisplacement
  intro r hr s hs
  have ha : f ⟨r, hr⟩ = 1 := hbot.le ⟨⟨r, hr⟩, rfl⟩
  have hh := congrArg (fun a : MulAut S => (a ⟨s, hs⟩ : G)) ha
  change r * s * r⁻¹ = s at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end Subgroup
