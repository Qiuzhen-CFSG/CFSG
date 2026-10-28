module

public import Theory.GroupTheory.SylowCentralizerCore
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.CoprimeQuotientNormalizer

/-!
# Central fours in solvable groups

Let a Sylow two-subgroup contain a central elementary four and no normal
elementary subgroup of order at least eight. If a nonidentity element of
the four is central in the ambient solvable group, the four becomes central
after quotienting by the odd core. Consequently every two-subgroup containing
the four centralizes it.

In the quotient, the Sylow centralizer lies in the two-core. The elementary
omega subgroup of that core's center contains the given four. Its pullback
to the Sylow subgroup is normal and elementary, so the no-eight hypothesis
forces equality. The resulting normal four has an automorphism group of
order at most two because it has a fixed nonidentity element; its centralizing
Sylow subgroup forces the action to be trivial. The quotient map is injective
on every two-subgroup, which lifts commutation without killing the odd core.

The Sylow subgroup is presented by an injective homomorphism so that the
same source group can be retained when passing to a centralizer or quotient.
Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 5.1, p.394,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup

namespace SolvableCentralFour

/-- A central four is normal in a solvable group with trivial odd core,
provided its Sylow subgroup has no normal elementary eight. -/
public theorem normal_map_of_no_normal_eight
    {P H : Type*} [Group P] [Finite P] [Group H] [Finite H]
    (S : Sylow 2 H) (f : P →* H) (hf : Function.Injective f)
    (hrange : f.range = (S : Subgroup H))
    (hsol : Group.IsSolvable H) (hcore : pPrimeCore 2 H = ⊥)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWc : W ≤ center P) : (W.map f).Normal := by
  let : IsElementaryAbelian 2 (W.map f) := IsElementaryAbelian.map f
  let R := pCore 2 H
  let Z := center R
  let O := omega₁ Z (p := 2)
  let U := O.map Z.subtype
  let A := U.map R.subtype
  let : O.Characteristic := omega₁_characteristic Z
  let : U.Characteristic := characteristic_of_characteristic_of_characteristic
  let : A.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative Z
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hRS : R ≤ (S : Subgroup H) := fitting_pCore_le_sylow S
  have hArange : A ≤ f.range := by
    rw [hrange]
    exact (map_subtype_le U).trans hRS
  have hWcentral : W.map f ≤ centralizer (S : Set H) := by
    rintro _ ⟨w, hw, rfl⟩ s hs
    have hsrange : s ∈ f.range := by rw [hrange]; exact hs
    obtain ⟨t, rfl⟩ := hsrange
    exact (map_mul f t w).symm.trans
      ((congrArg f (mem_center_iff.mp (hWc hw) t)).trans (map_mul f w t))
  have hWR : W.map f ≤ R := hWcentral.trans
    (centralizer_sylow_le_pCore_of_pPrimeCore_eq_bot hsol hcore S)
  have hWA : W.map f ≤ A := by
    intro w hw
    let wR : R := ⟨w, hWR hw⟩
    have hwZ : wR ∈ Z := by
      apply mem_center_iff.mpr
      intro r
      exact Subtype.ext (hWcentral hw r (hRS r.property))
    let wZ : Z := ⟨wR, hwZ⟩
    have hwO : wZ ∈ O := by
      apply subset_closure
      change wZ ^ (2 ^ 1) = 1
      apply Subtype.ext
      apply Subtype.ext
      simpa using elemPow_eq_one_of_isElementaryAbelian w hw
    exact ⟨wR, ⟨wZ, hwO, rfl⟩, rfl⟩
  let E := A.comap f
  let : E.Normal := inferInstance
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := A.comap_injective_isMulCommutative hf
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by
      intro x
      apply Subtype.ext
      apply hf
      change f ((x : P) ^ 2) = f 1
      simpa only [map_pow, map_one] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) (f x) x.property) }
  have hWE : W ≤ E := map_le_iff_le_comap.mp hWA
  have hlt : Nat.card E < 8 := by
    by_contra! h
    exact hno ⟨E, inferInstance, inferInstance, h⟩
  have hdiv : 4 ∣ Nat.card E := hW ▸ card_dvd_of_le hWE
  have hEq : W = E := eq_of_le_of_card_ge hWE (by omega)
  have hmap : W.map f = A := by
    rw [hEq]
    exact map_comap_eq_self hArange
  rw [hmap]
  infer_instance

/-- A normal four centralized by a Sylow two-subgroup is central if it
contains a nonidentity element of the ambient center. -/
public theorem le_center_of_normal_of_sylow_centralizes_of_fixed_point
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (A : Subgroup H) [A.Normal]
    (hA : Nat.card A = 4) (hSA : (S : Subgroup H) ≤ centralizer (A : Set H))
    (w : A) (hw : w ≠ 1) (hwc : (w : H) ∈ center H) : A ≤ center H := by
  let ρ : H →* MulAut A := MulAut.conjNormal
  have hfix : ∀ a ∈ ρ.range, a w = w := by
    rintro a ⟨g, rfl⟩
    apply Subtype.ext
    change g * (w : H) * g⁻¹ = w
    rw [mem_center_iff.mp hwc g, mul_inv_cancel_right]
  have hbound := card_mulAut_subgroup_le_two_of_fixed_point hA w hw ρ.range hfix
  have hSker : (S : Subgroup H) ≤ ρ.ker := by
    intro s hs
    change ρ s = 1
    ext a
    change s * (a : H) * s⁻¹ = a
    rw [← hSA hs a a.property, mul_inv_cancel_right]
  have hnot : ¬ 2 ∣ Nat.card ρ.range := by
    rw [← index_ker]
    exact fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hSker))
  have hcard : Nat.card ρ.range = 1 := by
    have hpos : 0 < Nat.card ρ.range := Nat.card_pos
    have hne : Nat.card ρ.range ≠ 2 := by intro h; exact hnot (by rw [h])
    omega
  have htrivial : ρ.range = ⊥ := (card_eq_one.mp hcard)
  intro a ha
  apply mem_center_iff.mpr
  intro g
  have he : ρ g = 1 := mem_bot.mp (htrivial ▸ (show ρ g ∈ ρ.range from ⟨g, rfl⟩))
  have hh := congrArg (fun e : MulAut A => ((e ⟨a, ha⟩ : A) : H)) he
  change g * a * g⁻¹ = a at hh
  exact mul_inv_eq_iff_eq_mul.mp hh


/-- A central Sylow four containing an ambient central involution becomes
central modulo the odd core. -/
public theorem map_le_center_odd_quotient
    {P H : Type*} [Group P] [Finite P] [Group H] [Finite H]
    (S : Sylow 2 H) (i : P →* H) (hi : Function.Injective i)
    (hrange : i.range = (S : Subgroup H))
    (hsol : Group.IsSolvable H)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWc : W ≤ center P) (w : P) (hw : w ∈ W) (hw1 : w ≠ 1)
    (hwc : i w ∈ center H) :
    (W.map i).map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤
      center (H ⧸ pPrimeCore 2 H) := by
  let N := pPrimeCore 2 H
  let q := QuotientGroup.mk' N
  let f := q.comp i
  let T := S.mapSurjective (QuotientGroup.mk'_surjective N)
  have hiS (x : P) : i x ∈ (S : Subgroup H) := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hqinj := injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := H))) (S : Subgroup H) S.isPGroup'
  have hf : Function.Injective f := by
    intro x y h
    apply hi
    exact congrArg Subtype.val (hqinj (a₁ := ⟨i x, hiS x⟩) (a₂ := ⟨i y, hiS y⟩) h)
  have hfrange : f.range = (T : Subgroup (H ⧸ N)) := by
    rw [MonoidHom.range_comp, hrange]
    rfl
  let : Group.IsSolvable H := hsol
  let A := W.map f
  let : A.Normal := normal_map_of_no_normal_eight T f hf hfrange
    inferInstance (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hno W hW hWc
  have hAcard : Nat.card A = 4 := (card_map_of_injective hf).trans hW
  have hTA : (T : Subgroup (H ⧸ N)) ≤ centralizer (A : Set (H ⧸ N)) := by
    intro t ht a ha
    have ht' : t ∈ f.range := by rw [hfrange]; exact ht
    obtain ⟨s, rfl⟩ := ht'
    obtain ⟨a, ha, rfl⟩ := ha
    exact (map_mul f a s).symm.trans
      ((congrArg f (mem_center_iff.mp (hWc ha) s).symm).trans (map_mul f s a))
  let wA : A := ⟨f w, mem_map_of_mem f hw⟩
  have hwA : wA ≠ 1 := by
    intro h
    apply hw1
    apply hf
    exact (congrArg Subtype.val h).trans (map_one f).symm
  have hwAc : (wA : H ⧸ N) ∈ center (H ⧸ N) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact (map_mul q x (i w)).symm.trans
      ((congrArg q (mem_center_iff.mp hwc x)).trans (map_mul q (i w) x))
  rw [map_map]
  exact le_center_of_normal_of_sylow_centralizes_of_fixed_point T A hAcard hTA wA hwA hwAc

/-- Every two-subgroup containing the four centralizes it. The odd core
is retained and commutation is lifted using injectivity on the two-subgroup. -/
public theorem centralizes_four_of_no_normal_eight
    {P H : Type*} [Group P] [Finite P] [Group H] [Finite H]
    (S : Sylow 2 H) (i : P →* H) (hi : Function.Injective i)
    (hrange : i.range = (S : Subgroup H))
    (hsol : Group.IsSolvable H)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWc : W ≤ center P) (w : P) (hw : w ∈ W) (hw1 : w ≠ 1)
    (hwc : i w ∈ center H)
    (Q : Subgroup H) (hQ : IsPGroup 2 Q) (hWQ : W.map i ≤ Q) :
    Q ≤ centralizer (W.map i : Set H) := by
  let q := QuotientGroup.mk' (pPrimeCore 2 H)
  have hcenter := map_le_center_odd_quotient S i hi hrange hsol hno W hW hWc w hw hw1 hwc
  have hinj := injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := H))) Q hQ
  intro x hx a ha
  have he : q (a * x) = q (x * a) := by
    rw [map_mul, map_mul]
    exact (mem_center_iff.mp (hcenter (mem_map_of_mem q ha)) (q x)).symm
  exact congrArg Subtype.val (hinj
    (a₁ := ⟨a * x, Q.mul_mem (hWQ ha) hx⟩)
    (a₂ := ⟨x * a, Q.mul_mem hx (hWQ ha)⟩) he)

end SolvableCentralFour
