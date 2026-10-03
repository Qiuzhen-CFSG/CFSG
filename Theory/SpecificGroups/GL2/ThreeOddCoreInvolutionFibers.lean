module
public import Theory.SpecificGroups.GL2.ThreeConjugacy
public import Theory.PPrimeCore
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.ElementaryAbelian.Basic
/-!
# Noncentral involution lifts through a GL₂(3) odd-core quotient

Let T be a four-group containing the involution x, and let N = C_G(x).
For a surjection from N to GL₂(3) with kernel O₂′(N), every noncentral
involution in the quotient has [O₂′(N) : C_O₂′(N)(T)] involution lifts.

Inject T through the odd kernel and choose t in T with noncentral image.
The central involution x maps to the scalar involution, so T = ⟨x,t⟩ and
C_N(t) = C_N(T). The odd-kernel orbit formula counts the lifts of f(t).
All noncentral involutions in GL₂(3) are conjugate, which transfers this
count to every required fiber. The actual odd core is retained throughout.

Source: Alperin–Brauer–Gorenstein, III.7 equation (8), article pp.103–104.
The four-group generation argument also occurs in
`Theory.GroupTheory.IsolatedFourTwoGroup`.
-/

open Matrix
namespace Matrix.GeneralLinearGroup
private abbrev L := GL (Fin 2) (ZMod 3)
private theorem central_commutes (a : L) : a * threeCentral = threeCentral * a := by
  apply Units.ext
  have h : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3),
      A * threeCentral.val = threeCentral.val * A := by decide +kernel
  exact h a.val

private theorem involution_isConj_reflection (y : L) (hy : orderOf y = 2)
    (hyz : y ≠ threeCentral) : IsConj y threeReflection := by
  obtain ⟨i, hi, -⟩ := three_conjugacy_data.1 y
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have hio := (MulAut.conj g).orderOf_eq y
  rw [show MulAut.conj g y = threeClassRepr i from hg, hy,
    three_conjugacy_data.2.1] at hio
  have hi15 : i = 1 ∨ i = 5 := by fin_cases i <;> simp_all
  rcases hi15 with rfl | rfl
  · have hiy : IsConj y threeCentral := by simpa [threeClassRepr] using hi
    obtain ⟨g, hg⟩ := isConj_iff.mp hiy.symm
    exfalso
    apply hyz
    rw [central_commutes, mul_assoc, mul_inv_cancel, mul_one] at hg
    exact hg.symm
  · simpa [threeClassRepr] using hi

private theorem central_involution_eq (y : L) (hy : orderOf y = 2)
    (hc : ∀ a : L, a * y = y * a) : y = threeCentral := by
  by_contra h
  obtain ⟨g, hg⟩ := isConj_iff.mp (involution_isConj_reflection y hy h)
  have he : y = threeReflection := by
    rw [hc g, mul_assoc, mul_inv_cancel, mul_one] at hg
    exact hg
  have hn : threeRotation * threeReflection ≠ threeReflection * threeRotation := by decide +kernel
  exact hn (he ▸ hc threeRotation)
end Matrix.GeneralLinearGroup

namespace Subgroup
private theorem centralizer_four_eq_of_central_generator
    {P : Type*} [Group P] [Finite P]
    (V : Subgroup P) [IsElementaryAbelian 2 V] (hV : Nat.card V = 4)
    (z a : P) (hzV : z ∈ V) (haV : a ∈ V) (hz1 : z ≠ 1) (ha1 : a ≠ 1)
    (hza : z ≠ a) (hzZ : z ∈ center P) :
    centralizer (V : Set P) = centralizer ({a} : Set P) := by
  have hgen : closure ({z, a} : Set P) = V := by
    let : IsKleinFour (closure ({z, a} : Set P)) :=
      isKleinFour_closure_pair z a
        (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) z hzV)
        (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a haV)
        hz1 ha1 hza
        (congrArg Subtype.val (mul_comm' (⟨z, hzV⟩ : V) ⟨a, haV⟩))
    apply eq_of_le_of_card_ge
    · exact (closure_le _).mpr (by
        intro b hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with rfl | rfl <;> assumption)
    · rw [hV, IsKleinFour.card_four]
  apply le_antisymm
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx a haV).symm
  · intro x hx
    have hVx : V ≤ centralizer ({x} : Set P) := by
      rw [← hgen]
      apply (closure_le _).mpr
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzZ x).symm
      · exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hx).symm
    intro v hv
    exact mem_centralizer_singleton_iff.mp (hVx hv)
end Subgroup

namespace Subgroup
open Matrix.GeneralLinearGroup
private theorem involution_image_order
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hker : Nat.Coprime 2 (Nat.card f.ker))
    (u : G) (hu : orderOf u = 2) : orderOf (f u) = 2 := by
  apply orderOf_eq_prime (p := 2)
  · rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  · intro he
    let a : f.ker := ⟨u, he⟩
    have ho : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans hu
    have hd : 2 ∣ Nat.card f.ker := ho ▸ _root_.orderOf_dvd_natCard a
    have hh := Nat.eq_one_of_dvd_coprimes hker (dvd_refl 2) hd
    norm_num at hh

/-- Noncentral involutions in the GL₂(3) odd-core quotient have exactly the
index of the four-group centralizer in the actual odd core as lift multiplicity. -/
public theorem card_noncentral_involution_fiber_of_oddCoreQuotient
    {G : Type*} [Group G] [Finite G]
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T)
    (f : centralizer ({x} : Set G) →* GL (Fin 2) (ZMod 3))
    (hf : Function.Surjective f)
    (hfker : f.ker = pPrimeCore 2 (centralizer ({x} : Set G)))
    (y : GL (Fin 2) (ZMod 3)) (hy : orderOf y = 2) (hyz : y ≠ threeCentral) :
    Nat.card {u : {u : centralizer ({x} : Set G) // orderOf u = 2} // f u = y} =
      ((centralizer (T : Set G)).subgroupOf
        ((pPrimeCore 2 (centralizer ({x} : Set G))).map
          (centralizer ({x} : Set G)).subtype)).index := by
  classical
  let N := centralizer ({x} : Set G)
  let O := pPrimeCore 2 N
  let K := O.map N.subtype
  let A := (centralizer (T : Set G)).subgroupOf K
  let V := T.subgroupOf N
  have hCN : centralizer (T : Set G) ≤ N :=
    centralizer_le (Set.singleton_subset_iff.mpr hxT)
  have hTN : T ≤ N := T.le_centralizer.trans hCN
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hTN
  have hV : Nat.card V = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv).trans hT
  have hfodd : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hfker]
    exact pPrimeCore_coprime_card
  have hinj : Function.Injective (f.comp V.subtype) :=
    injective_comp_subtype_of_coprime_ker f hfodd V (IsElementaryAbelian.isPGroup 2 V)
  have hVf : Nat.card (V.map f) = 4 := by
    rw [← hV]
    apply Nat.card_image_of_injOn
    intro a ha b hb hab
    exact congrArg Subtype.val (hinj (show f.comp V.subtype ⟨a, ha⟩ =
      f.comp V.subtype ⟨b, hb⟩ from hab))
  obtain ⟨b, hb, hb1, hbz⟩ : ∃ b ∈ V.map f, b ≠ 1 ∧ b ≠ threeCentral := by
    by_contra hn
    have hall : (V.map f : Set (GL (Fin 2) (ZMod 3))) ⊆ {1, threeCentral} := by
      intro b hb
      by_cases h : b = 1
      · exact Or.inl h
      · exact Or.inr (Classical.byContradiction fun hz => hn ⟨b, hb, h, hz⟩)
    have hc := Set.ncard_mono hall
    rw [Set.ncard_pair (by decide : (1 : GL (Fin 2) (ZMod 3)) ≠ threeCentral),
      ← Nat.card_coe_set_eq] at hc
    change Nat.card (V.map f) ≤ 2 at hc
    omega
  obtain ⟨t, ht, rfl⟩ := hb
  have ht1 : t ≠ 1 := by intro h; exact hb1 (by rw [h, map_one])
  have hto : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht) ht1
  let z : N := ⟨x, hTN hxT⟩
  have hzo : orderOf z = 2 := (Subgroup.orderOf_coe z).symm.trans hx
  have hzZ : z ∈ center N := by
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (mem_centralizer_singleton_iff.mp a.property)
  have hfz : f z = threeCentral := central_involution_eq (f z)
    (involution_image_order f hfodd z hzo) (by
      intro a
      obtain ⟨g, rfl⟩ := hf a
      exact (map_mul f g z).symm.trans
        ((congrArg f (mem_center_iff.mp hzZ g)).trans (map_mul f z g)))
  have hzt : z ≠ t := by intro h; exact hbz (h ▸ hfz)
  have hcentral : centralizer (V : Set N) = centralizer ({t} : Set N) :=
    centralizer_four_eq_of_central_generator V hV z t hxT ht
      (by intro h; have hh := congrArg orderOf h; rw [hzo, orderOf_one] at hh; omega)
      ht1 hzt hzZ
  have heq : centralizer (V : Set N) = (centralizer (T : Set G)).subgroupOf N := by
    ext a
    constructor
    · intro ha b hb
      exact congrArg Subtype.val (ha ⟨b, hTN hb⟩ hb)
    · intro ha b hb
      exact Subtype.ext (ha b hb)
  have hmem (a : N) : (a : G) ∈ K ↔ a ∈ O :=
    mem_map_iff_mem (f := N.subtype) N.subtype_injective
  have hcard : Nat.card ((centralizer ({t} : Set N)).subgroupOf O) = Nat.card A := by
    apply Nat.card_congr
    exact {
      toFun := fun a => ⟨⟨a.val.val.val, (hmem a.val.val).mpr a.val.property⟩,
        heq.le (hcentral.symm.le a.property)⟩
      invFun := fun a => ⟨⟨⟨a.val.val, hCN a.property⟩, (hmem _).mp a.val.property⟩,
        hcentral.le (heq.symm.le a.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hindex : ((centralizer ({t} : Set N)).subgroupOf f.ker).index = A.index := by
    rw [hfker]
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A))
    rw [← hcard, card_mul_index, hcard, A.card_mul_index]
    exact (card_map_of_injective N.subtype_injective).symm
  calc
    _ = Nat.card {u : {u : N // orderOf u = 2} // f u = f t} :=
      card_involution_fiber_eq_of_isConj f hf
        ((involution_isConj_reflection y hy hyz).trans
          (involution_isConj_reflection (f t) (involution_image_order f hfodd t hto) hbz).symm)
    _ = ((centralizer ({t} : Set N)).subgroupOf f.ker).index :=
      card_involution_fiber_eq_centralizer_index f hfodd t hto
    _ = A.index := hindex
end Subgroup
