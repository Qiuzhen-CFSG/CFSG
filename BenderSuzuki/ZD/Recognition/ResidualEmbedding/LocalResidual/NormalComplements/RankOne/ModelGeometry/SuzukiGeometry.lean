module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.BorelPairGeometry
public import Theory.SpecificGroups.Suzuki.OmegaGeneration
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki

/-!
# Suzuki geometry at a prescribed Sylow subgroup

Sylow conjugacy aligns the standard root and Borel with the original model.
This transports the literal two-point intersection, including its cyclic
order and inversion action. Odd order makes its commutator with the outside
involution the whole intersection.

The centralizer of every nonidentity root element lies in the root. Therefore
the common centralizer of an inside involution and an outside involution is
trivial. Together with the proved absence of outer involutions, this yields
the fixed-involution and automorphism-rigidity conclusions.

Source: GLS, Volume 4, Chapter 4, Lemmas 3.2(b--e) and 3.4(f), used in
Chapter 2, Lemmas 16.2--16.4. The omega-generation theorem supplies
Lemma 3.2(h): the torus acts regularly on the nonidentity omega elements,
so any one root involution, the torus and the outside involution generate
the same whole group.
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup PFAppendixIII PFchapter1section1 _root_.BenderSuzuki.MatrixGroups
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {m : ℕ}

/-- The source root is Ω₁(P), of order q, not the full Sylow of order q². -/
public theorem suzuki_omega_geometry (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G) :
    omegaOneAmbient (P : Subgroup G) = (center P).map (P : Subgroup G).subtype ∧
    IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup G)) ∧
    Nat.card (omegaOneAmbient (P : Subgroup G)) = 2 ^ (2 * m + 1) ∧
    Nat.card P = (2 ^ (2 * m + 1)) ^ 2 ∧
    (involutionCore (normalizer (P : Set G))).map (normalizer (P : Set G)).subtype =
      omegaOneAmbient (P : Subgroup G) :=
  ⟨suzukiSylow_omega_eq_center hm e P, suzukiSylow_omega_elementary hm e P,
    suzukiSylow_omega_card hm e P, suzukiSylow_card hm e P,
    suzukiSylow_normalizer_involutionCore hm e P⟩

omit [Finite G] in
private theorem map_twoPoint {H : Type*} [Group H] (f : G ≃* H)
    (B : Subgroup G) (t : G) :
    (twoPoint B t).map f.toMonoidHom = twoPoint (B.map f.toMonoidHom) (f t) := by
  rw [twoPoint, twoPoint, Subgroup.map_inf _ _ _ f.injective]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨f y, mem_map_of_mem _ hy, ?_⟩
    simp [map_mul, map_inv]
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨t⁻¹ * y * t, ⟨y, hy, by simp⟩, ?_⟩
    simp [map_mul, map_inv]

omit [Finite G] in
private theorem commutator_eq_of_odd_inverted (D : Subgroup G)
    (hodd : Odd (Nat.card D)) (t : G) (ht : IsInvolution t)
    (hinv : ∀ x ∈ D, rightConjugateElem x t = x⁻¹) : ⁅D, zpowers t⁆ = D := by
  have hi (x : G) (hx : x ∈ D) : t * x * t⁻¹ = x⁻¹ := by
    simpa only [rightConjugateElem, ht.inv_eq_self] using hinv x hx
  apply le_antisymm
  · apply le_normalizer_iff_commutator_le_left.mp
    apply zpowers_le.mpr
    rw [mem_normalizer_iff_map_conj_eq]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change t * y * t⁻¹ ∈ D
      rw [hi y hy]
      exact D.inv_mem hy
    · intro hx
      refine ⟨x⁻¹, D.inv_mem hx, ?_⟩
      change t * x⁻¹ * t⁻¹ = x
      rw [hi _ (D.inv_mem hx), inv_inv]
  · intro x hx
    obtain ⟨y, hy⟩ := (powCoprime (G := D) (Nat.coprime_two_right.mpr hodd)).surjective ⟨x, hx⟩
    have hy2 : (y : G) ^ 2 = x := congrArg Subtype.val hy
    have hc : ⁅(y : G), t⁆ = (y : G) ^ 2 := by
      calc
        ⁅(y : G), t⁆ = (y : G) * (t * (y : G)⁻¹ * t⁻¹) := by
          simp only [commutatorElement_def, mul_assoc]
        _ = (y : G) ^ 2 := by rw [hi _ (D.inv_mem y.property), inv_inv, pow_two]
    rw [← hy2, ← hc]
    exact commutator_mem_commutator y.property (mem_zpowers t)

/-- The literal two-point subgroup is the cyclic inverted torus of order q−1. -/
public theorem suzuki_twoPoint_geometry (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G)
    (t : G) (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    IsCyclic (twoPoint (normalizer (P : Set G)) t) ∧
    Nat.card (twoPoint (normalizer (P : Set G)) t) = 2 ^ (2 * m + 1) - 1 ∧
    (∀ x ∈ twoPoint (normalizer (P : Set G)) t, rightConjugateElem x t = x⁻¹) ∧
    ⁅twoPoint (normalizer (P : Set G)) t, zpowers t⁆ =
      twoPoint (normalizer (P : Set G)) t := by
  obtain ⟨f, _, hB⟩ := suzukiSylow_aligned_equiv hm e P
  let u := f.symm t
  have hu : IsInvolution u := ⟨fun h => ht.ne_one (f.symm.injective (h.trans f.symm.map_one.symm)),
    by simp only [u, ← map_pow, ht.sq_eq_one, map_one]⟩
  have huB : u ∉ SuzukiBorelSubgroup m := fun h =>
    htB (hB ▸ (show t ∈ (SuzukiBorelSubgroup m).map f.toMonoidHom from
      ⟨u, h, f.apply_symm_apply t⟩))
  have hD : (twoPoint (SuzukiBorelSubgroup m) u).map f.toMonoidHom =
      twoPoint (normalizer (P : Set G)) t := by
    rw [map_twoPoint, hB, f.apply_symm_apply]
  have hcyc : IsCyclic (twoPoint (normalizer (P : Set G)) t) := by
    rw [← hD]
    exact ((twoPoint (SuzukiBorelSubgroup m) u).equivMapOfInjective _ f.injective).isCyclic.mp
      (suzukiBorel_pair_isCyclic m hm u hu huB)
  have hcard : Nat.card (twoPoint (normalizer (P : Set G)) t) = 2 ^ (2 * m + 1) - 1 := by
    rw [← hD, card_map_of_injective f.injective]
    exact suzukiBorel_pair_card m hm u hu huB
  have hinv : ∀ x ∈ twoPoint (normalizer (P : Set G)) t, rightConjugateElem x t = x⁻¹ := by
    intro x hx
    rw [← hD] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hh := congrArg f (suzukiBorel_pair_inverted m hm u hu huB y hy)
    simpa only [rightConjugateElem, map_mul, map_inv, u, f.apply_symm_apply,
      MulEquiv.coe_toMonoidHom] using hh
  refine ⟨hcyc, hcard, hinv, commutator_eq_of_odd_inverted _ ?_ t ht hinv⟩
  rw [hcard]
  exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega)) odd_one

/-- Any two nontrivial root elements have centralizers contained in the same root. -/
public theorem suzuki_centralizer_le_sylow (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G)
    {x : G} (hx : x ∈ (P : Subgroup G)) (hne : x ≠ 1) :
    centralizer ({x} : Set G) ≤ (P : Subgroup G) :=
  (suzukiSylow_borel_structure hm e P).2.1 x hx hne

/-- In fact the inside/outside common centralizer is trivial. -/
public theorem suzuki_common_centralizer_eq_bot (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G)
    {z t : G} (hzP : z ∈ (P : Subgroup G)) (hz : IsInvolution z)
    (htB : t ∉ normalizer (P : Set G)) :
    centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  by_contra hne
  have hxP := suzuki_centralizer_le_sylow hm e P hzP hz.ne_one hx.1
  have htC : t ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hx.2).symm
  exact htB ((P : Subgroup G).le_normalizer
    (suzuki_centralizer_le_sylow hm e P hxP hne htC))

/-- The common centralizer has odd order, as required by Section 16. -/
public theorem suzuki_common_centralizer_odd (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G)
    {z t : G} (hzP : z ∈ (P : Subgroup G)) (hz : IsInvolution z)
    (htB : t ∉ normalizer (P : Set G)) :
    Odd (Nat.card (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G)) := by
  rw [suzuki_common_centralizer_eq_bot hm e P hzP hz htB]
  simpa only [Nat.card_unique] using odd_one

omit [Finite G] in
private theorem inner_of_square_one (hm : 1 ≤ m) (e : G ≃* SuzukiMatrixGroup m)
    (a : MulAut G) (ha : a ^ 2 = 1) : ∃ b : G, a = MulAut.conj b := by
  have ha' : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨b, hb, _⟩ := suzuki_involutoryAut_inner_and_twoRank m hm (MulAut.congr e a) ha'
  exact (MulAut.congr_inner_iff e a).mp ⟨b, hb⟩

/-- A square-one automorphism fixing one root involution fixes Ω₁(P) pointwise. -/
public theorem suzuki_automorphism_fixes_omega (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G)
    (a : MulAut G) (ha : a ^ 2 = 1)
    {z : G} (hzP : z ∈ (P : Subgroup G)) (hz : IsInvolution z) (haz : a z = z) :
    ∀ x ∈ omegaOneAmbient (P : Subgroup G), a x = x := by
  obtain ⟨b, rfl⟩ := inner_of_square_one hm e a ha
  have hbC : b ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp haz)
  have hbP := suzuki_centralizer_le_sylow hm e P hzP hz.ne_one hbC
  intro x hx
  rw [suzukiSylow_omega_eq_center hm e P] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hc := congrArg Subtype.val (mem_center_iff.mp hy (⟨b, hbP⟩ : P))
  change b * (y : G) * b⁻¹ = y
  rw [mul_inv_eq_iff_eq_mul]
  exact hc

/-- Fixing also an outside involution forces the automorphism to be identity. -/
public theorem suzuki_automorphism_eq_one_of_fixed_pair (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G)
    (a : MulAut G) (ha : a ^ 2 = 1)
    {z t : G} (hzP : z ∈ (P : Subgroup G)) (hz : IsInvolution z)
    (htB : t ∉ normalizer (P : Set G)) (haz : a z = z) (hat : a t = t) : a = 1 := by
  obtain ⟨b, rfl⟩ := inner_of_square_one hm e a ha
  have hb : b ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
    ⟨mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp haz),
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hat)⟩
  rw [suzuki_common_centralizer_eq_bot hm e P hzP hz htB, mem_bot] at hb
  rw [hb, map_one]

/-- The torus orbit of a root involution spans the whole omega subgroup. -/
public theorem suzuki_omega_le_involution_torus (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G)
    (t : G) (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G))
    {z : G} (hzP : z ∈ (P : Subgroup G)) (hz : IsInvolution z) :
    omegaOneAmbient (P : Subgroup G) ≤ zpowers z ⊔ twoPoint (normalizer (P : Set G)) t := by
  classical
  let E := omegaOneAmbient (P : Subgroup G)
  let D := twoPoint (normalizer (P : Set G)) t
  have hzE : z ∈ E := (omegaOneAmbient_le_iff _ _).mp le_rfl z hzP hz.sq_eq_one
  have hDcard : Nat.card D = 2 ^ (2*m+1) - 1 :=
    (suzuki_twoPoint_geometry hm e P t ht htB).2.1
  have hodd : Odd (Nat.card D) := by
    rw [hDcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega)) odd_one
  have hdisj : Disjoint (P : Subgroup G) D := by
    apply disjoint_of_coprime_natCard
    rw [suzukiSylow_card hm e P]
    exact (hodd.coprime_two_right.symm.pow_left _).pow_left _
  have hconj (d : D) : (MulAut.conj (d : G)) z ∈ E := by
    have hP : (P : Subgroup G).map (MulAut.conj (d : G)).toMonoidHom = P :=
      mem_normalizer_iff_map_conj_eq.mp d.property.1
    have hE : E.map (MulAut.conj (d : G)).toMonoidHom = E := by
      dsimp [E]
      rw [map_omegaOneAmbient_injective _ (MulAut.conj (d : G)).injective]
      exact congrArg omegaOneAmbient hP
    rw [← hE]
    exact mem_map_of_mem _ hzE
  let f : D → {x : E // x ≠ 1} := fun d =>
    ⟨⟨(MulAut.conj (d : G)) z, hconj d⟩,
      fun he => hz.ne_one ((MulAut.conj (d : G)).injective
        ((congrArg Subtype.val he).trans (map_one _).symm))⟩
  have hinj : Function.Injective f := by
    intro d₁ d₂ he
    have he' : (MulAut.conj (d₁ : G)) z = (MulAut.conj (d₂ : G)) z :=
      congrArg (fun x : {x : E // x ≠ 1} => (x.val : G)) he
    have hfix : (MulAut.conj ((d₂ : G)⁻¹ * d₁)) z = z := by
      have hh := congrArg (MulAut.conj (d₂ : G)⁻¹) he'
      simpa [MulAut.conj_apply, mul_assoc] using hh
    have hP := suzuki_centralizer_le_sylow hm e P hzP hz.ne_one
      (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix))
    have hD : (d₂ : G)⁻¹ * d₁ ∈ D := D.mul_mem (D.inv_mem d₂.property) d₁.property
    have hone := disjoint_def.mp hdisj hP hD
    exact Subtype.ext (inv_mul_eq_one.mp hone).symm
  have hcards : Nat.card D = Nat.card {x : E // x ≠ 1} := by
    let := Fintype.ofFinite E
    rw [Nat.card_eq_fintype_card (α := {x : E // x ≠ 1}), Fintype.card_subtype_compl]
    simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card]
    rw [hDcard, suzukiSylow_omega_card hm e P]
  have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcards⟩).2
  intro x hx
  by_cases hxeq : x = 1
  · exact hxeq ▸ one_mem _
  obtain ⟨d, hd⟩ := hsurj ⟨⟨x, hx⟩, fun he => hxeq (congrArg Subtype.val he)⟩
  have hd' : (MulAut.conj (d : G)) z = x :=
    congrArg (fun y : {x : E // x ≠ 1} => (y.val : G)) hd
  rw [← hd', MulAut.conj_apply]
  exact (zpowers z ⊔ D).mul_mem
    ((zpowers z ⊔ D).mul_mem (mem_sup_right d.property) (mem_sup_left (mem_zpowers z)))
    ((zpowers z ⊔ D).inv_mem (mem_sup_right d.property))

/-- The literal root-generated subgroup is the whole group, using Ω₁(P) itself. -/
public theorem suzuki_rootGenerated_eq_top (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G)
    (t : G) (htB : t ∉ normalizer (P : Set G)) :
    rootGenerated (P : Subgroup G) t = ⊤ := by
  obtain ⟨f, hP, hB⟩ := suzukiSylow_aligned_equiv hm e P
  have huB : f.symm t ∉ SuzukiBorelSubgroup m := fun h =>
    htB (hB ▸ (show t ∈ (SuzukiBorelSubgroup m).map f.toMonoidHom from
      ⟨f.symm t, h, f.apply_symm_apply t⟩))
  have hh := congrArg (Subgroup.map f.toMonoidHom)
    (suzukiRootSubgroup_omega_sup_zpowers_eq_top m hm (f.symm t) huB)
  simpa only [Subgroup.map_sup, map_omegaOneAmbient_injective f.toMonoidHom f.injective,
    hP, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, f.apply_symm_apply,
    map_top_of_surjective f.toMonoidHom f.surjective,
    rootGenerated] using hh

/-- The marked three-generator expression is exactly the omega-generated subgroup. -/
public theorem suzuki_marked_generation (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G)
    (t : G) (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G))
    {z : G} (hzP : z ∈ (P : Subgroup G)) (hz : IsInvolution z) :
    zpowers z ⊔ zpowers t ⊔ ⁅twoPoint (normalizer (P : Set G)) t, zpowers t⁆ =
      rootGenerated (P : Subgroup G) t := by
  rw [(suzuki_twoPoint_geometry hm e P t ht htB).2.2.2]
  apply le_antisymm
  · rw [suzuki_rootGenerated_eq_top hm e P t htB]
    exact le_top
  · exact sup_le
      ((suzuki_omega_le_involution_torus hm e P t ht htB hzP hz).trans
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (le_sup_right.trans le_sup_left)

end BenderSuzuki.ZD.RankOneModelGeometry
