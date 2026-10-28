module

public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import Theory.GroupTheory.ClassTwoCommutator
public import Theory.GroupTheory.SylowCentralizerConjugacy
public import Mathlib.Tactic.Group

/-!
# Central commutators and nonfusion for J.2.3

Ru1 makes the commutator row S → S a homomorphism with image
[⟨t⟩,S] ≤ V and kernel C_S(t). Since |V| = 8 and |S| = 2048,
the centralizer index is at most eight. A full commutator image gives
|C_S(t)| = 256 and the actual quotient C_S(t)/V ≃ E₃₂. The square
map lands in V, so S and all its element centralizers have exponent
dividing four.

The source's cubic subgroup is embedded from Syl₃(O²(C_L(Z))).
`SingerChoice` specifies its invariant order-seven subgroup; it does not
assert the existence of that choice. An order-seven subgroup centralizing
s excludes fusion of s with the generator z of Z, because C_G(z)=H has
order 2¹⁴·15. The chosen cubic subgroup also normalizes S₀=C_S(B₇).

These are proved deductions and conditional numerical consequences, not
an assertion that all nine clauses are complete. The full commutator
image, the construction of the Singer choice, its centralizer structure,
and quaternion recognition remain for the J.2.3 assembly. The |Z|=2
premise comes from J.2.1, owned by the preceding parabolic development.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3, printed pp.433–434 (PDF pp.444–445).
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G]

namespace RuOne
variable {L V : Subgroup G} (r : RuOne L V)
include r

theorem central_V : V ≤ centralizer (L.pCoreIn 2 : Set G) := by
  rw [← r.center_eq]
  rintro v ⟨x,hx,rfl⟩ s hs
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨s,hs⟩)

theorem classTwo : _root_.commutator (L.pCoreIn 2) ≤ center (L.pCoreIn 2) := by
  have he : _root_.commutator (L.pCoreIn 2) = center (L.pCoreIn 2) :=
    (map_injective (L.pCoreIn 2).subtype_injective) (r.derived_eq.trans r.center_eq.symm)
  exact he.le

theorem square_mem_V (s : L.pCoreIn 2) : (s : G) ^ 2 ∈ V := by
  have he : r.steinberg.coordinates (s ^ 2) = 1 := by
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    change 2 • (r.steinberg.coordinates s).toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  simpa only [coe_pow] using (r.steinberg.coordinates_eq_one_iff (s ^ 2)).mp he

theorem pow_four (s : L.pCoreIn 2) : s ^ 4 = 1 := by
  have hv := r.square_mem_V s
  have hs := r.natural.square_eq_one_of_trivial_kernel rfl ⟨(s : G)^2, hv⟩
  apply Subtype.ext
  change (s : G)^4 = 1
  simpa only [Subtype.ext_iff, coe_pow, coe_one, ← pow_mul] using
    congrArg (fun v : V => (v : G)) hs

theorem exponent_dvd_four : Monoid.exponent (L.pCoreIn 2) ∣ 4 :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr r.pow_four

/-- The exponent upper bound in J.2.3(3), before excluding the abelian case. -/
theorem coreCentralizer_exponent_dvd_four (s : G) :
    Monoid.exponent (L.pCoreIn 2 ⊓ centralizer ({s} : Set G) : Subgroup G) ∣ 4 := by
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro c
  apply Subtype.ext
  change (c : G) ^ 4 = 1
  exact congrArg (fun x : L.pCoreIn 2 => (x : G)) (r.pow_four ⟨c,c.property.1⟩)

omit r in
theorem commutator_map (s : L.pCoreIn 2) :
    (⁅zpowers s, ⊤⁆ : Subgroup (L.pCoreIn 2)).map (L.pCoreIn 2).subtype =
      ⁅zpowers (s : G), L.pCoreIn 2⁆ := by
  rw [map_commutator, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype]
  rfl

theorem commutator_le_V (s : L.pCoreIn 2) :
    ⁅zpowers (s : G), L.pCoreIn 2⁆ ≤ V := by
  rw [← r.derived_eq, map_subtype_commutator]
  exact commutator_mono (zpowers_le.mpr s.property) le_rfl

theorem centralizer_index_eq (s : L.pCoreIn 2) :
    (centralizer ({s} : Set (L.pCoreIn 2))).index =
      Nat.card (⁅zpowers (s : G), L.pCoreIn 2⁆ : Subgroup G) := by
  rw [ClassTwo.centralizer_index r.classTwo, ← commutator_map s,
    card_map_of_injective (L.pCoreIn 2).subtype_injective]

variable [Finite G]

theorem centralizer_index_le_eight (s : L.pCoreIn 2) :
    (centralizer ({s} : Set (L.pCoreIn 2))).index ≤ 8 := by
  rw [r.centralizer_index_eq s, ← r.card_V]
  exact card_le_of_le (r.commutator_le_V s)

omit [Finite G] in
theorem centralizer_card_of_full_commutator (s : L.pCoreIn 2)
    (hfull : ⁅zpowers (s : G), L.pCoreIn 2⁆ = V) :
    Nat.card (L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) = 256 := by
  have hc := (centralizer ({s} : Set (L.pCoreIn 2))).index_mul_card
  rw [r.centralizer_index_eq s, hfull, r.card_V, r.card_S] at hc
  have he : Nat.card (L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) =
      Nat.card (centralizer ({s} : Set (L.pCoreIn 2))) := by
    rw [← map_subtype_centralizer_singleton, card_map_of_injective (L.pCoreIn 2).subtype_injective]
  rw [he]
  omega

omit [Finite G] in
theorem V_le_coreCentralizer (s : L.pCoreIn 2) :
    V ≤ L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G) := by
  intro v hv
  exact ⟨r.steinberg.kernel_le hv,
    mem_centralizer_singleton_iff.mpr (r.central_V hv s s.property).symm⟩

omit [Finite G] in
theorem coreCentralizer_kernel_normal (s : L.pCoreIn 2) :
    (V.subgroupOf (L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G))).Normal := by
  refine ⟨?_⟩
  intro v hv g
  change (g : G) * (v : G) * (g : G)⁻¹ ∈ V
  have he : (g : G) * (v : G) = (v : G) * (g : G) :=
    r.central_V hv g g.property.1
  rw [he, mul_inv_cancel_right]
  exact hv

/-- The centralizer quotient in J.2.3(6) is literally E₃₂ once the
full-commutator assertion has been proved. -/
theorem coreCentralizer_quotient_equiv (s : L.pCoreIn 2)
    [(V.subgroupOf (L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G))).Normal]
    (hfull : ⁅zpowers (s : G), L.pCoreIn 2⁆ = V) :
    Nonempty (((L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) ⧸
      V.subgroupOf (L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G))) ≃*
        Multiplicative (Fin 5 → ZMod 2)) := by
  let C := L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G)
  let A := C ⧸ V.subgroupOf C
  have hpow (x : A) : x ^ 2 = 1 := by
    obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf C) x
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    change (c : G) ^ 2 ∈ V
    exact r.square_mem_V ⟨c,c.property.1⟩
  let _ : IsElementaryAbelian 2 A := {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  have hcard : Nat.card A = 32 := by
    have hc := card_eq_card_quotient_mul_card_subgroup (V.subgroupOf C)
    have hvcard : Nat.card (V.subgroupOf C) = 8 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (r.V_le_coreCentralizer s)).toEquiv,
        r.card_V]
    have hccard : Nat.card C = 256 := r.centralizer_card_of_full_commutator s hfull
    change Nat.card C = Nat.card A * Nat.card (V.subgroupOf C) at hc
    rw [hvcard, hccard] at hc
    omega
  have hdim : Module.finrank (ZMod 2) (Additive A) = 5 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    change Nat.card A = _ at hc
    simpa only [Nat.card_zmod, hcard, show 2 ^ 5 = 32 by decide] using hc.symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive A) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

end RuOne
end CFSG.Quasithin.ChapterJ

namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- The chosen Sylow three-subgroup, embedded in G. -/
def cubicSubgroup (d : TypeRuSetup G) (B : Sylow 3 d.L₁) : Subgroup G :=
  (B : Subgroup d.L₁).map d.L₁.subtype

/-- Data for the source's B-invariant choice of an order-seven subgroup. -/
structure SingerChoice (d : TypeRuSetup G) (B : Sylow 3 d.L₁) where
  B7 : Subgroup G
  le_L : B7 ≤ d.L
  card_seven : Nat.card B7 = 7
  normalized : cubicSubgroup d B ≤ normalizer B7

/-- S₀ is the literal centralizer inside S. -/
def fixedCore (d : TypeRuSetup G) (B7 : Subgroup G) : Subgroup G :=
  d.S ⊓ centralizer (B7 : Set G)

/-- The noncentral factor in C_S(s). -/
def movingCore (d : TypeRuSetup G) (B7 : Subgroup G) (s : G) : Subgroup G :=
  ⁅d.S ⊓ centralizer ({s} : Set G), B7⁆

/-- For a nonidentity generator of Z, C_G(z) is exactly the specified H. -/
theorem centralizer_generator (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2)
    (z : G) (hz : z ∈ d.Z) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) = d.H := by
  have hu := (Nat.card_eq_two_iff' (1 : d.Z)).mp hZ
  have hzu : (⟨z,hz⟩ : d.Z) ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  apply le_antisymm
  · intro g hg v hv
    by_cases hv1 : v = 1
    · simp [hv1]
    · have he : (⟨v,hv⟩ : d.Z) = ⟨z,hz⟩ :=
        hu.unique (fun he => hv1 (congrArg Subtype.val he)) hzu
      have hvz : v = z := congrArg Subtype.val he
      rw [hvz]
      exact (mem_centralizer_singleton_iff.mp hg).symm
  · intro g hg
    exact mem_centralizer_singleton_iff.mpr (hg z hz).symm

/-- J.2.3(2): an element fixed by an order-seven subgroup cannot be fused to z. -/
theorem not_isConj_of_mem_fixedCore (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2)
    (B7 : Subgroup G) (h7 : Nat.card B7 = 7)
    (z : G) (hz : z ∈ d.Z) (hz1 : z ≠ 1) (s : G)
    (hs : s ∈ fixedCore d B7) : ¬ IsConj z s := by
  intro hconj
  have hc : Nat.card (centralizer ({s} : Set G)) = Nat.card d.H := by
    rw [← centralizer_generator d hZ z hz hz1]
    obtain ⟨g,hg⟩ := isConj_iff.mp hconj
    let f := MulAut.conj g
    have hfz : f z = s := hg
    apply (Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)).symm
    intro a
    change a ∈ centralizer ({z} : Set G) ↔ f a ∈ centralizer ({s} : Set G)
    simp only [mem_centralizer_singleton_iff]
    constructor
    · intro ha
      simpa only [map_mul, hfz] using congrArg f ha
    · intro ha
      apply f.injective
      simpa only [map_mul, hfz] using ha
  have hle : B7 ≤ centralizer ({s} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (hs.2 b hb)
  have hd := card_dvd_of_le hle
  rw [h7, hc, d.ru2.card_H hZ] at hd
  norm_num at hd

/-- The source cubic subgroup lies in L via the actual two-residual. -/
theorem cubicSubgroup_le_L (d : TypeRuSetup G) (B : Sylow 3 d.L₁) :
    cubicSubgroup d B ≤ d.L := by
  rintro b ⟨b,hb,rfl⟩
  obtain ⟨l,hl,he⟩ := b.property
  change (b : G) ∈ d.L
  change (l : G) = (b : G) at he
  exact he ▸ l.property.1

/-- The part of J.2.3(4) that follows directly from the B-invariant choice. -/
theorem SingerChoice.normalizes_fixedCore (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) :
    cubicSubgroup d B ≤ normalizer (fixedCore d c.B7) := by
  have hc : normalizer (c.B7 : Set G) ≤ normalizer (centralizer (c.B7 : Set G)) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp
      (normal_subgroupOf_centralizer_normalizer _)
  exact (le_inf ((cubicSubgroup_le_L d B).trans d.ru1.steinberg.normalized)
    (c.normalized.trans hc)).trans inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.ChapterJ.SpecialCore
