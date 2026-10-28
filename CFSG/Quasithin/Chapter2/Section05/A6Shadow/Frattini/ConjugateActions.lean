module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Transport
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed
public import Theory.GroupTheory.DihedralTwoCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Actions of conjugates of z on the A₆ component

For `a = g⁻¹ z g ∈ S`, the earlier-source input `C_{G_t}(a) ∈ He`
passes to `C_K(a)` by the relative normality of K in G_t and 1.1.3(1).
The compatible action identifies this centralizer with the literal fixed
subgroup in A₆. Trivial action would make A₆ characteristic two, while an
involution outside the natural S₆ has fixed subgroup D₁₀. Neither group
has characteristic two. Thus the action lies in the actual natural S₆,
and simplicity of K forces its nontrivial commutator with a to be all of K.

The source premise from 1.1.3(2) remains explicit; the section assembly
must produce it. No natural-action or commutator conclusion is assumed.
Right conjugation defines a, and the action still uses left conjugation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.22(1), printed p.567.
-/

public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini

private theorem not_two_group_of_odd_prime_dvd {X : Type*} [Group X] [Finite X]
    (q : ℕ) (hq : q.Prime) (hne : q ≠ 2) (hd : q ∣ Nat.card X) :
    ¬ IsPGroup 2 X := by
  intro hp
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at hd
  have hq2 := hq.dvd_of_dvd_pow hd
  exact hne ((Nat.dvd_prime Nat.prime_two).mp hq2 |>.resolve_left hq.ne_one)

private theorem a6_not_characteristicTwo : ¬ HasCharacteristicTwo A6 := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  have hp : ¬ IsPGroup 2 A6 :=
    not_two_group_of_odd_prime_dvd 3 (by decide) (by decide) (by rw [card_A6]; decide)
  have hcore : pCore 2 A6 = ⊥ := by
    rcases (inferInstance : (pCore 2 A6).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hp ((show IsPGroup 2 (⊤ : Subgroup A6) from h ▸ pCore_isPGroup).of_equiv
        Subgroup.topEquiv)).elim
  intro hc
  change centralizer (pCore 2 A6 : Set A6) ≤ pCore 2 A6 at hc
  rw [hcore] at hc
  have hct : centralizer (↑(⊥ : Subgroup A6) : Set A6) = ⊤ :=
    centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup A6) ≤ center A6 from bot_le)
  rw [hct] at hc
  exact top_ne_bot (le_bot_iff.mp hc)

private theorem d10_not_characteristicTwo : ¬ HasCharacteristicTwo (DihedralGroup 5) := by
  have hc := dihedralProduct_twoCore_le_center (DihedralGroup 5) PUnit 5 (by decide)
    ⟨(MulEquiv.prodUnique (M := DihedralGroup 5) (N := PUnit)).symm⟩
  intro h
  have htop : pCore 2 (DihedralGroup 5) = ⊤ := top_unique
    ((centralizer_eq_top_iff_subset.mpr hc).symm ▸ h)
  have hp : IsPGroup 2 (DihedralGroup 5) :=
    (show IsPGroup 2 (⊤ : Subgroup (DihedralGroup 5)) from htop ▸ pCore_isPGroup).of_equiv
      Subgroup.topEquiv
  exact not_two_group_of_odd_prime_dvd 5 (by decide) (by decide)
    (by rw [DihedralGroup.nat_card]; decide) hp

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
namespace EarlierSetup
variable (d : EarlierSetup κ G)

/-- The earlier characteristic-two input descends using normality in G_t. -/
theorem conjugateCentralizer_mem_He (a : G)
    (hc : (centralizer ({d.t} : Set G) ⊓ centralizer ({a} : Set G)) ∈ Chapter1.He G) :
    (d.K ⊓ centralizer ({a} : Set G)) ∈ Chapter1.He G := by
  let N := d.K ⊓ centralizer ({a} : Set G)
  let C := centralizer ({d.t} : Set G) ⊓ centralizer ({a} : Set G)
  have hNC : N ≤ C := inf_le_inf (d.k_le_h.trans d.h_le_centralizer_t) le_rfl
  have hn : (N.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf (inf_le_left.trans d.centralizer_t_normalizes_K)
      (inf_le_right.trans (centralizer ({a} : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf)
  by_cases hN : N = ⊥
  · change N ∈ Chapter1.He G
    rw [hN]
    apply Chapter1.mem_He_iff.mpr
    intro x _
    have hx : x = 1 := Subsingleton.elim _ _
    rw [hx]
    exact one_mem _
  · exact Chapter1.lemma_1_1_3_1 hc hN hNC hn.isSubnormal

/-- Compatibility identifies fixed model elements with ambient centralizing elements. -/
theorem action_fixed_iff_centralizes (a : d.H) (k : d.K) :
    d.action a (d.modelK k) = d.modelK k ↔
      (k : G) ∈ centralizer ({(a : G)} : Set G) := by
  constructor
  · intro hf
    have hh := congrArg (fun y : A6 => (d.modelK.symm y : G)) hf
    rw [d.action_compatible, d.modelK.symm_apply_apply] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hc
    apply d.modelK.symm.injective
    apply Subtype.ext
    rw [d.action_compatible, d.modelK.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc).symm

/-- The actual fixed-subgroup isomorphism induced by the given marking of K as A₆. -/
def centralizerActionEquiv (a : d.H) :
    (d.K ⊓ centralizer ({(a : G)} : Set G) : Subgroup G) ≃*
      GLS3.Chapter5.automorphismFixedSubgroup (d.action a) where
  toFun k := ⟨d.modelK ⟨k, k.property.1⟩,
    (d.action_fixed_iff_centralizes a ⟨k, k.property.1⟩).mpr k.property.2⟩
  invFun k := ⟨d.modelK.symm k, (d.modelK.symm k).property,
    (d.action_fixed_iff_centralizes a (d.modelK.symm k)).mp (by
      simpa only [d.modelK.apply_symm_apply] using
        (show d.action a k = k from k.property))⟩
  left_inv k := by
    apply Subtype.ext
    change (d.modelK.symm (d.modelK ⟨k, k.property.1⟩) : G) = (k : G)
    exact congrArg (fun x : d.K => (x : G)) (d.modelK.symm_apply_apply _)
  right_inv k := by apply Subtype.ext; exact d.modelK.apply_symm_apply _
  map_mul' k l := by
    apply Subtype.ext
    exact d.modelK.map_mul (⟨k, k.property.1⟩ : d.K) (⟨l, l.property.1⟩ : d.K)

/-- Trivial action would give characteristic two to the nonabelian simple A₆. -/
theorem action_ne_one_of_centralizer_mem_He (a : d.H)
    (hc : (d.K ⊓ centralizer ({(a : G)} : Set G)) ∈ Chapter1.He G) :
    d.action a ≠ 1 := by
  intro he
  have hCK : d.K ⊓ centralizer ({(a : G)} : Set G) = d.K := by
    apply inf_eq_left.mpr
    intro k hk
    apply (d.action_fixed_iff_centralizes a ⟨k, hk⟩).mp
    rw [he]
    rfl
  rw [hCK] at hc
  exact a6_not_characteristicTwo
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 d.modelK).mp (Chapter1.mem_He_iff.mp hc))

/-- An involutory action with characteristic-two fixed subgroup is natural:
the exceptional involution's actual D₁₀ fixed subgroup is excluded. -/
theorem action_mem_natural_of_centralizer_mem_He (a : d.H) (ha2 : a ^ 2 = 1)
    (hc : (d.K ⊓ centralizer ({(a : G)} : Set G)) ∈ Chapter1.He G) :
    d.action a ∈ natural := by
  have ho : orderOf (d.action a) = 2 := orderOf_eq_prime_iff.mpr
    ⟨by rw [← map_pow, ha2, map_one], d.action_ne_one_of_centralizer_mem_He a hc⟩
  by_contra hn
  obtain ⟨e⟩ := outside_natural_involution_fixed_equiv_dihedral (d.action a) ho hn
  exact d10_not_characteristicTwo
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 ((d.centralizerActionEquiv a).trans e)).mp
      (Chapter1.mem_He_iff.mp hc))

/-- Simplicity makes every nontrivial compatible action generate all of K by commutators. -/
theorem commutator_eq_of_action_ne_one (a : d.H) (ha : d.action a ≠ 1) :
    ⁅d.K, zpowers (a : G)⁆ = d.K := by
  have hNK : d.H ≤ normalizer (d.K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer d.k_le_h).mp d.normalK
  have hle : ⁅d.K, zpowers (a : G)⁆ ≤ d.K :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr (hNK a.property))
  have hn : (⁅d.K, zpowers (a : G)⁆.subgroupOf d.K).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left _ _)
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup d.K := d.modelK.isSimpleGroup
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have hb' : ⁅d.K, zpowers (a : G)⁆ = ⊥ := by
      rw [← map_subgroupOf_eq_of_le hle, hb, Subgroup.map_bot]
    have hcentral := commutator_eq_bot_iff_le_centralizer.mp hb'
    exfalso
    apply ha
    ext k : 1
    obtain ⟨k, rfl⟩ := d.modelK.surjective k
    apply (d.action_fixed_iff_centralizes a k).mpr
    exact centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers (a : G)))
      (hcentral k.property)
  · exact le_antisymm hle (subgroupOf_eq_top.mp ht)

/-- Source 2.5.22(1), retaining precisely its earlier 1.1.3(2) input. -/
theorem conjugate_z_commutator_and_natural (g : G)
    (ha : g⁻¹ * d.z * g ∈ d.S)
    (hc : (centralizer ({d.t} : Set G) ⊓
      centralizer ({g⁻¹ * d.z * g} : Set G)) ∈ Chapter1.He G) :
    d.K = ⁅d.K, zpowers (g⁻¹ * d.z * g)⁆ ∧
      d.action ⟨g⁻¹ * d.z * g, d.s_le_h ha⟩ ∈ natural := by
  let a : d.H := ⟨g⁻¹ * d.z * g, d.s_le_h ha⟩
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    change (g⁻¹ * d.z * g) ^ 2 = 1
    have hz2 : d.z ^ 2 = 1 := by simpa only [d.z_order] using pow_orderOf_eq_one d.z
    calc
      (g⁻¹ * d.z * g) ^ 2 = g⁻¹ * d.z ^ 2 * g := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hz2]; simp
  have hCK := d.conjugateCentralizer_mem_He (a : G) hc
  exact ⟨(d.commutator_eq_of_action_ne_one a
    (d.action_ne_one_of_centralizer_mem_He a hCK)).symm,
    d.action_mem_natural_of_centralizer_mem_He a ha2 hCK⟩

end EarlierSetup
end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
