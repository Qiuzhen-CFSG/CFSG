module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedGeometry
public import Theory.GroupAction.EightCubicNormalizer

/-!
# A marked cubic and its cyclic-four centralizer in the HS normalizer core

The actual overlap of the two local groups contains a cubic. Its action on
V is nontrivial, since C_G(V) is a two-group, so it fixes precisely the
original involution z. On the full homocyclic core P=O₂(N_G(V)), squaring
bounds the cubic centralizer by four. The cubic norm of a square root of z
is a fixed square root of z, giving the matching lower bound and an actual
cyclic-four generator in the original P.

These are consequences of HS1--HS2, Aschbacher--Smith I.4.8, printed p.418.
They supply marked local cubic geometry for the subgroup construction; no
PSL₃(4) amalgam or ambient recognition is an input or conclusion.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private noncomputable def coreEquiv (h : TypeAt z V) :
    (normalizer (V : Set G)).pCoreIn 2 ≃* (Fin 3 → Multiplicative (ZMod 4)) :=
  ((pCore 2 (normalizer (V : Set G))).equivMapOfInjective
    (normalizer (V : Set G)).subtype (normalizer (V : Set G)).subtype_injective).symm.trans
    ((MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans h.normalizer_core.some)

private theorem core_comm (h : TypeAt z V) :
    IsMulCommutative ((normalizer (V : Set G)).pCoreIn 2) :=
  ⟨⟨fun a b => (coreEquiv h).injective (by simp only [map_mul, mul_comm])⟩⟩

private theorem core_fourth (h : TypeAt z V)
    (a : (normalizer (V : Set G)).pCoreIn 2) : a ^ 4 = 1 := by
  apply (coreEquiv h).injective
  rw [map_pow, map_one]
  have he : ∀ t : Multiplicative (ZMod 4), t ^ 4 = 1 := by decide +kernel
  exact funext (fun i => he ((coreEquiv h a) i))

private theorem core_square_one (h : TypeAt z V) (a : G)
    (ha : a ∈ (normalizer (V : Set G)).pCoreIn 2) : a ^ 2 = 1 ↔ a ∈ V := by
  let M := normalizer (V : Set G)
  constructor
  · intro hs
    obtain ⟨aM, haM, rfl⟩ := ha
    have hw : aM ∈ (omega (pCore 2 M) (p := 2) 1).map (pCore 2 M).subtype :=
      ⟨⟨aM, haM⟩, subset_closure (show (⟨aM, haM⟩ : pCore 2 M) ^ (2^1) = 1 from
        Subtype.ext (Subtype.ext hs)), rfl⟩
    rw [← h.seed_eq_omega_normalizer_core] at hw
    exact hw
  · intro hv
    let := h.elementary
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) a hv

private theorem core_square_root (h : TypeAt z V)
    (a : (normalizer (V : Set G)).pCoreIn 2) (ha : a ^ 2 = 1) :
    ∃ b : (normalizer (V : Set G)).pCoreIn 2, b ^ 2 = a := by
  have hroot : ∀ a : Multiplicative (ZMod 4), a ^ 2 = 1 → ∃ b, b ^ 2 = a := by
    decide +kernel
  have hc (i : Fin 3) : ∃ b : Multiplicative (ZMod 4), b ^ 2 = (coreEquiv h a) i :=
    hroot _ (by simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] using
      (congrArg (fun c => coreEquiv h c i) ha))
  choose b hb using hc
  refine ⟨(coreEquiv h).symm b, (coreEquiv h).injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply]
  exact funext hb

/-- Every cubic in the original local overlap fixes exactly the marked point
of V, using the whole ambient centralizer rather than a chosen action model. -/
theorem TypeAt.cubic_seed_fixed (h : TypeAt z V) (x : G)
    (hx : x ∈ involutionCentralizer z ⊓ normalizer (V : Set G))
    (hx3 : orderOf x = 3) : V ⊓ centralizer ({x} : Set G) = zpowers z := by
  let xM : normalizer (V : Set G) := ⟨x, hx.2⟩
  let a := V.normalizerMonoidHom xM
  have ha3 : a ^ 3 = 1 := by
    rw [← map_pow]
    have he : xM ^ 3 = 1 := Subtype.ext (hx3 ▸ pow_orderOf_eq_one x)
    rw [he, map_one]
  have ha : a ≠ 1 := by
    intro he
    have hxC : x ∈ centralizer (V : Set G) := by
      have hm : xM ∈ V.normalizerMonoidHom.ker := he
      rw [normalizerMonoidHom_ker] at hm
      exact hm
    have heP : centralizer (V : Set G) = (normalizer (V : Set G)).pCoreIn 2 := h.seed_centralizer
    have hxP : x ∈ (normalizer (V : Set G)).pCoreIn 2 := heP ▸ hxC
    have hp := core_fourth h ⟨x, hxP⟩
    have hdiv : 3 ∣ 4 := hx3 ▸ orderOf_dvd_of_pow_eq_one
      (congrArg (fun c : (normalizer (V : Set G)).pCoreIn 2 => (c : G)) hp)
    norm_num at hdiv
  have hc := MulAut.cubic_fixed_card_of_card_eight a ha3 ha h.seed_card
  have hfix : a.fixedSubgroup.map V.subtype = V ⊓ centralizer ({x} : Set G) := by
    ext v
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have he := congrArg Subtype.val ((MulAut.mem_fixedSubgroup a v).mp hv)
      change x * (v : G) * x⁻¹ = v at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · rintro ⟨hv, hc⟩
      refine ⟨⟨v, hv⟩, (MulAut.mem_fixedSubgroup a _).mpr (Subtype.ext ?_), rfl⟩
      change x * v * x⁻¹ = v
      rw [← mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have hcard : Nat.card (V ⊓ centralizer ({x} : Set G) : Subgroup G) = 2 := by
    rw [← hfix, card_map_of_injective V.subtype_injective, hc]
  apply (eq_of_le_of_card_ge (zpowers_le.mpr
    (show z ∈ V ⊓ centralizer ({x} : Set G) from
      ⟨h.involution_mem_seed, mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hx.1).symm⟩)) ?_).symm
  rw [hcard, Nat.card_zpowers, h.involution]

/-- The full normalizer core has a cyclic-four cubic centralizer, generated
by an actual square root of the original marked involution. -/
theorem TypeAt.cubic_normalizer_core (h : TypeAt z V) (x : G)
    (hx : x ∈ involutionCentralizer z ⊓ normalizer (V : Set G))
    (hx3 : orderOf x = 3) :
    ∃ c : G, c ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ c ^ 2 = z ∧
      orderOf c = 4 ∧
      (normalizer (V : Set G)).pCoreIn 2 ⊓ centralizer ({x} : Set G) = zpowers c := by
  let P := (normalizer (V : Set G)).pCoreIn 2
  let C := P ⊓ centralizer ({x} : Set G)
  let := core_comm h
  let : CommGroup P := IsMulCommutative.instCommGroup
  let : IsMulCommutative C := ⟨⟨fun a b => Subtype.ext
    (congrArg (fun q : P => (q : G)) (mul_comm
      (⟨a, a.property.1⟩ : P) (⟨b, b.property.1⟩ : P)))⟩⟩
  have heP : centralizer (V : Set G) = P := h.seed_centralizer
  let : CommGroup C := IsMulCommutative.instCommGroup
  let sq : C →* C := powMonoidHom 2
  have hker : sq.ker.map C.subtype = V ⊓ centralizer ({x} : Set G) := by
    ext a
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(core_square_one h a a.property.1).mp
        (congrArg Subtype.val (show a ^ 2 = 1 from ha)), a.property.2⟩
    · rintro ⟨hv, hc⟩
      have hp : a ∈ P := heP ▸
        (le_centralizer_iff_isMulCommutative.mpr h.elementary.toIsMulCommutative) hv
      exact ⟨⟨a, hp, hc⟩, Subtype.ext ((core_square_one h a hp).mpr hv), rfl⟩
  have hk : Nat.card sq.ker = 2 := by
    rw [← card_map_of_injective C.subtype_injective, hker, h.cubic_seed_fixed x hx hx3,
      Nat.card_zpowers, h.involution]
  have hsq : sq.range ≤ sq.ker := by
    rintro _ ⟨a, rfl⟩
    change (a ^ 2) ^ 2 = 1
    rw [← pow_mul]
    exact Subtype.ext (congrArg (fun q : P => (q : G)) (core_fourth h ⟨a, a.property.1⟩))
  have hC : Nat.card C ≤ 4 := by
    have hm := sq.ker.card_mul_index
    rw [index_ker, hk] at hm
    have hb := card_le_of_le hsq
    rw [hk] at hb
    omega
  have hzP : z ∈ P := heP ▸
    (le_centralizer_iff_isMulCommutative.mpr h.elementary.toIsMulCommutative)
      h.involution_mem_seed
  let zP : P := ⟨z, hzP⟩
  have hz2 : zP ^ 2 = 1 := Subtype.ext (by
    change z ^ 2 = 1
    simpa only [h.involution] using pow_orderOf_eq_one z)
  obtain ⟨b, hb⟩ := core_square_root h zP hz2
  have hnorm : normalizer (V : Set G) ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg a ha
    obtain ⟨aM, haM, he⟩ := ha
    refine ⟨⟨g, hg⟩ * aM * (⟨g, hg⟩ : normalizer (V : Set G))⁻¹,
      (inferInstance : (pCore 2 (normalizer (V : Set G))).Normal).conj_mem aM haM ⟨g, hg⟩, ?_⟩
    change g * (aM : G) * g⁻¹ = g * a * g⁻¹
    rw [show (aM : G) = a from he]
  let α := P.normalizerMonoidHom ⟨x, hnorm hx.2⟩
  have hα : α ^ 3 = 1 := by
    rw [← map_pow]
    have he : (⟨x, hnorm hx.2⟩ : normalizer (P : Set G)) ^ 3 = 1 :=
      Subtype.ext (hx3 ▸ pow_orderOf_eq_one x)
    rw [he, map_one]
  have hzfix : α zP = zP := Subtype.ext (by
    change x * z * x⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp hx.1, mul_inv_cancel_right])
  let c : P := b * α b * α (α b)
  have hcf : α c = c := by
    have ha : α (α (α b)) = b := by
      have he := congrArg (fun f : MulAut P => f b) hα
      simpa only [pow_succ, pow_zero, mul_one, MulAut.mul_apply, MulAut.one_apply] using he
    simp only [c, map_mul, ha]
    ac_rfl
  have hcs : c ^ 2 = zP := by
    simp only [c, mul_pow, ← map_pow, hb, hzfix]
    simp only [← pow_two, hz2, one_mul]
  have hc4 : orderOf c = 4 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · rw [show 2 ^ 1 = 2 from rfl, hcs]
      intro he
      have hh := h.involution
      have hz : z = 1 := congrArg Subtype.val he
      simp [hz] at hh
    · exact core_fourth h c
  have hcC : (c : G) ∈ C := ⟨c.property, mem_centralizer_singleton_iff.mpr
    ((mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hcf)).symm)⟩
  refine ⟨c, c.property, congrArg Subtype.val hcs, (orderOf_coe c).trans hc4, ?_⟩
  exact (eq_of_le_of_card_ge (zpowers_le.mpr hcC)
    (by rw [Nat.card_zpowers, orderOf_coe, hc4]; exact hC)).symm

/-- The original local overlap supplies a cubic with the marked fixed point
and cyclic-four centralizer in the entire normalizer two-core. -/
theorem TypeAt.exists_cubic_core (h : TypeAt z V) :
    ∃ x c : G, x ∈ involutionCentralizer z ⊓ normalizer (V : Set G) ∧
      orderOf x = 3 ∧ V ⊓ centralizer ({x} : Set G) = zpowers z ∧
      c ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ c ^ 2 = z ∧ orderOf c = 4 ∧
      (normalizer (V : Set G)).pCoreIn 2 ⊓ centralizer ({x} : Set G) = zpowers c := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := (involutionCentralizer z ⊓ normalizer (V : Set G) : Subgroup G)) 3
    (by rw [h.local_intersection_card]; decide)
  have hx3 : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  obtain ⟨c, hc⟩ := h.cubic_normalizer_core x x.property hx3
  exact ⟨x, c, x.property, hx3, h.cubic_seed_fixed x x.property hx3, hc⟩

end CFSG.Quasithin.HigmanSims
