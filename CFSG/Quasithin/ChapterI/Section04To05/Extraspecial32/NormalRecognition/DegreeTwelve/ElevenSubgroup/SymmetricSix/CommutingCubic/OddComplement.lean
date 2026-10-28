module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.CommutingCubic.Reduction
public import Theory.GroupTheory.CyclicSylowTwoComplement
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The odd complement of the cubic centralizer

In the source involution centralizer `H`, the actual quotient map to `S₃`
shows that `C_H(X) = X⟨z⟩`: a cubic generator has a centralizer of order
three in that quotient, and the source fixed-core equality supplies exactly
`⟨z⟩` in the kernel. Transport along `H.subtype` gives the literal ambient
intersection and its order six.

Inside `C_G(X)`, the normalizer condition for a two-group then makes
`⟨z⟩` a Sylow two-subgroup. Checked Burnside transfer identifies the odd
core as its complement. Its ambient image is invariant under `z` and the
marked inverter `u`, has index two, and meets `C_G(z)` exactly in `X`.
No ambient order alternative, simplicity, or quotient-inversion premise
is used in this construction.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 2.2(2) and 4.5, pp.33 and 40.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem perm_three_centralizer (x y : Equiv.Perm (Fin 3))
    (hx : x ^ 3 = 1) (hne : x ≠ 1) (hc : x * y = y * x) :
    y = 1 ∨ y = x ∨ y = x ^ 2 := by
  revert x y
  decide +kernel

private theorem local_centralizer (h : Hypotheses z) :
    centralizer (h.X : Set (Centralizer z)) =
      (h.X : Subgroup (Centralizer z)) ⊔ zpowers (distinguished z) := by
  let : IsCyclic h.X := isCyclic_of_prime_card h.sylow_three_card
  have hXC : (h.X : Subgroup (Centralizer z)) ≤ centralizer (h.X : Set (Centralizer z)) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hzC : distinguished z ∈ centralizer (h.X : Set (Centralizer z)) := by
    intro x hx
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  apply le_antisymm ?_ (sup_le hXC (zpowers_le.mpr hzC))
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (h.X : Subgroup (Centralizer z))).mp
    (inferInstance : IsCyclic h.X)
  have hxX : x ∈ h.X := by
    change x ∈ (h.X : Subgroup (Centralizer z))
    rw [← hx]
    exact mem_zpowers x
  have hxo : orderOf x = 3 := by rw [← Nat.card_zpowers, hx, h.sylow_three_card]
  let e := h.quotient_model.some
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (Core z))
  have hfx : f x ≠ 1 := by
    intro he
    have hxQ : x ∈ Core z := (QuotientGroup.eq_one_iff x).mp
      (e.injective (he.trans (map_one e).symm))
    have hd := (Core z).orderOf_dvd_natCard hxQ
    rw [hxo, h.core_card] at hd
    norm_num at hd
  have hfx3 : (f x) ^ 3 = 1 := by
    have hx3 : x ^ 3 = 1 := hxo ▸ pow_orderOf_eq_one x
    rw [← map_pow, hx3, map_one]
  intro c hc
  have hcomm : f x * f c = f c * f x := by rw [← map_mul, ← map_mul, hc x hxX]
  have him : ∃ v ∈ h.X, f c = f v := by
    rcases perm_three_centralizer (f x) (f c) hfx3 hfx hcomm with he | he | he
    · exact ⟨1, one_mem _, he.trans (map_one f).symm⟩
    · exact ⟨x, hxX, he⟩
    · exact ⟨x ^ 2, pow_mem hxX _, he.trans (map_pow f x 2).symm⟩
  obtain ⟨v, hv, hcv⟩ := him
  have hk : c * v⁻¹ ∈ Core z := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    change f (c * v⁻¹) = e 1
    rw [map_mul, map_inv, hcv, mul_inv_cancel, map_one]
  have hkC : c * v⁻¹ ∈ centralizer (h.X : Set (Centralizer z)) :=
    mul_mem hc (inv_mem (hXC hv))
  have hkZ : c * v⁻¹ ∈ zpowers (distinguished z) := h.fixed ▸ ⟨hk, hkC⟩
  have hh := ((h.X : Subgroup (Centralizer z)) ⊔ zpowers (distinguished z)).mul_mem
    (show c * v⁻¹ ∈ (h.X : Subgroup (Centralizer z)) ⊔ zpowers (distinguished z) from mem_sup_right hkZ)
    (mem_sup_left hv)
  simpa only [inv_mul_cancel_right] using hh

private theorem centralizer_image (h : Hypotheses z) :
    (centralizer (h.X : Set (Centralizer z))).map (Centralizer z).subtype =
      Centralizer z ⊓ centralizer (cubicInG h : Set G) := by
  ext c
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.property, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hv y hy)
  · rintro ⟨hcH, hc⟩
    refine ⟨⟨c, hcH⟩, ?_, rfl⟩
    intro x hx
    exact Subtype.ext (hc x (mem_map_of_mem _ hx))

/-- The literal centralizer intersection of Aschbacher 2.2(2). -/
public theorem local_cubic_centralizer (h : Hypotheses z) :
    Centralizer z ⊓ centralizer (cubicInG h : Set G) =
      cubicInG h ⊔ zpowers z := by
  rw [← centralizer_image h, local_centralizer h, Subgroup.map_sup, MonoidHom.map_zpowers]
  rfl

/-- Its order is six, using the actual ambient embeddings. -/
public theorem local_cubic_centralizer_card (h : Hypotheses z) :
    Nat.card (Centralizer z ⊓ centralizer (cubicInG h : Set G) : Subgroup G) = 6 := by
  rw [local_cubic_centralizer]
  have hzX : z ∉ cubicInG h := by
    intro hz
    have hd := (cubicInG h).orderOf_dvd_natCard hz
    rw [h.involution, cubicInG_card] at hd
    norm_num at hd
  have hzC : z ∈ centralizer (cubicInG h : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (cubicInG_le h hx)
  rw [card_sup_zpowers_of_normalizing_involution _ z
    (h.involution ▸ pow_orderOf_eq_one z) hzX
    (centralizer_le_normalizer _ hzC), cubicInG_card]

private theorem sylow_two_card_two {K : Type*} [Group K] [Finite K]
    (t : K) (ht : orderOf t = 2)
    (hC : Nat.card (centralizer ({t} : Set K)) = 6) :
    ∃ T : Sylow 2 K, Nat.card T = 2 := by
  have hZ : Nat.card (zpowers t) = 2 := (Nat.card_zpowers t).trans ht
  have hZp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hZ)
  obtain ⟨T, hZT⟩ := hZp.exists_le_sylow
  let D : Subgroup K := (T : Subgroup K) ⊓ centralizer ({t} : Set K)
  have hZD : zpowers t ≤ D := le_inf hZT (zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr rfl))
  have hd6 : Nat.card D ∣ 6 := hC ▸ card_dvd_of_le (show D ≤ centralizer {t} from inf_le_right)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (T.isPGroup'.to_le (show D ≤ T from inf_le_left))
  have hcop : Nat.Coprime (Nat.card D) 3 := by
    rw [hn]
    exact (show Nat.Coprime 2 3 by decide).pow_left n
  have hd2 : Nat.card D ∣ 2 := hcop.dvd_of_dvd_mul_right hd6
  have hDZ : D = zpowers t := (eq_of_le_of_card_ge hZD (by
    rw [hZ]
    exact Nat.le_of_dvd (by decide) hd2)).symm
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hTZ : (T : Subgroup K) ≤ zpowers t := by
    apply le_of_nilpotent_of_card_two_of_centralizer_le _ _ hZT hZ
    simpa only [zpowers_eq_closure, centralizer_closure] using hDZ.le
  have he : (T : Subgroup K) = zpowers t := le_antisymm hTZ hZT
  exact ⟨T, he ▸ hZ⟩

private theorem cubic_centralizer_sylow (h : Hypotheses z) :
    ∃ T : Sylow 2 (centralizer (cubicInG h : Set G)), Nat.card T = 2 := by
  let C := centralizer (cubicInG h : Set G)
  have hzC : z ∈ C := fun x hx => mem_centralizer_singleton_iff.mp (cubicInG_le h hx)
  let t : C := ⟨z, hzC⟩
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t).symm.trans h.involution
  apply sylow_two_card_two t ht
  have he : (centralizer ({t} : Set C)).map C.subtype = Centralizer z ⊓ C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨mem_centralizer_singleton_iff.mpr ?_, y.property⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
    · rintro ⟨hxH, hxC⟩
      refine ⟨⟨x, hxC⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hxH)
  rw [← card_map_of_injective C.subtype_injective, he]
  exact local_cubic_centralizer_card h

/-- The normal odd complement in the actual cubic centralizer. The only use
of the chosen geometry is that its marked involution inverts the cubic. -/
public theorem oddCentralizerData (h : Hypotheses z) (a : SourceGeometry h) :
    Nonempty (CommutingCubic.OddCentralizerData h a) := by
  let C := centralizer (cubicInG h : Set G)
  let P := (pPrimeCore 2 C).map C.subtype
  have hPC : P ≤ C := map_subtype_le _
  have hPcard : Nat.card P = Nat.card (pPrimeCore 2 C) :=
    card_map_of_injective C.subtype_injective
  have hPodd : Odd (Nat.card P) := by
    rw [hPcard]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hCN : normalizer (C : Set G) ≤ normalizer (P : Set G) :=
    normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C)
  have hzC : z ∈ C := fun x hx => mem_centralizer_singleton_iff.mp (cubicInG_le h hx)
  have huN : a.u ∈ normalizer (cubicInG h : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro y ⟨x, hx, rfl⟩
      change a.u * x * a.u⁻¹ ∈ cubicInG h
      rw [CommutingCubic.choice_inverts_X a (Or.inl rfl) x hx]
      exact inv_mem hx
    · rw [card_map_of_injective (MulAut.conj a.u).injective]
  let : IsCyclic (cubicInG h) := isCyclic_of_prime_card (cubicInG_card h)
  have hXC : cubicInG h ≤ C := le_centralizer_iff_isMulCommutative.mpr inferInstance
  let Y := (cubicInG h).subgroupOf C
  have hYcentral : Y ≤ center C := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (y.property x hx).symm
  let : Y.Normal := ⟨fun x hx g => by
    have hc := mem_center_iff.mp (hYcentral hx) g
    simpa only [hc, mul_inv_cancel_right] using hx⟩
  have hYcard : Nat.card Y = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv).trans (cubicInG_card h)
  have hYcore : Y ≤ pPrimeCore 2 C := le_sSup ⟨inferInstance, by rw [hYcard]; decide⟩
  have hXP : cubicInG h ≤ P := by
    calc
      cubicInG h = Y.map C.subtype := (map_subgroupOf_eq_of_le hXC).symm
      _ ≤ P := map_mono hYcore
  have hfixed : P ⊓ Centralizer z = cubicInG h := by
    apply (eq_of_le_of_card_ge (le_inf hXP (cubicInG_le h)) ?_).symm
    have hd : Nat.card (P ⊓ Centralizer z : Subgroup G) ∣ 6 := by
      rw [← local_cubic_centralizer_card h]
      exact card_dvd_of_le (le_inf inf_le_right (inf_le_left.trans hPC))
    have ho := Odd.of_dvd_nat hPodd
      (card_dvd_of_le (show P ⊓ Centralizer z ≤ P from inf_le_left))
    have hd3 : Nat.card (P ⊓ Centralizer z : Subgroup G) ∣ 3 :=
      ho.coprime_two_right.dvd_of_dvd_mul_left hd
    rw [cubicInG_card]
    exact Nat.le_of_dvd (by decide) hd3
  obtain ⟨T, hT⟩ := cubic_centralizer_sylow h
  have hcomp := T.isComplement'_pPrimeCore_of_isCyclic
    (isCyclic_of_prime_card hT) (hT ▸ (T : Subgroup C).card_subgroup_dvd_card)
  have hcard : Nat.card C = 2 * Nat.card P := by
    rw [hPcard]
    simpa only [hT] using hcomp.card_mul_card.symm
  exact ⟨⟨P, hPC, hPodd, hCN (le_normalizer hzC),
    hCN (normalizer_le_normalizer_centralizer (cubicInG h) huN), hfixed, hcard⟩⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
