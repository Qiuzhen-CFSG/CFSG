module
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Complement

/-!
# An odd complement as the odd core of a Sylow centralizer

Let L be a normal subgroup of a finite group H with an odd-order complement
E. Suppose E centralizes the ambient image of a Sylow two-subgroup S of L,
and the centralizer of S inside L is a two-group. Then E is exactly the
ambient image of the odd core of the centralizer of S in H. Cyclicity of E
is not required.

Write D for the centralizer inside L. Since D normalizes S and both are
two-groups, Sylow maximality gives D ≤ S. Thus D commutes with E. The actual
complement factorization H=LE restricts to C_H(S)=DE, making E normal in
this centralizer and its quotient a homomorphic image of the two-group D.
The normal odd subgroup E lies in the odd core. Conversely, the core's
image in that two-group quotient has both odd order and two-power order,
so is trivial. Mapping this equality through the original centralizer
subtype gives the asserted ambient equality.

This is the final odd-core identification in ABG II.3 Proposition 3(iv),
article pages 27–28. The hypotheses about the chosen Sylow subgroup and its
centralizer are supplied separately by the actual linear or unitary model.
-/

namespace Subgroup

public theorem oddComplement_eq_oddCore_sylowCentralizer
    {H : Type*} [Group H] [Finite H] (L E : Subgroup H) [L.Normal]
    (hcomp : L.IsComplement' E) (hodd : Odd (Nat.card E)) (S : Sylow 2 L)
    (hEC : E ≤ centralizer (((S : Subgroup L).map L.subtype) : Set H))
    (hD : IsPGroup 2 (centralizer (S : Set L))) :
    E = (pPrimeCore 2 (centralizer (((S : Subgroup L).map L.subtype) : Set H))).map
      (centralizer (((S : Subgroup L).map L.subtype) : Set H)).subtype := by
  let D := centralizer (S : Set L)
  let C := centralizer (((S : Subgroup L).map L.subtype) : Set H)
  have hDS : D ≤ (S : Subgroup L) := by
    have hsup : IsPGroup 2 (D ⊔ (S : Subgroup L) : Subgroup L) :=
      hD.to_sup_of_normal_right' S.isPGroup' (centralizer_le_normalizer _)
    exact le_sup_left.trans (S.is_maximal' hsup le_sup_right).le
  have hDC (d : D) : d.val.val ∈ C := by
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    exact congrArg Subtype.val ((mem_centralizer_iff.mp d.property) s hs)
  have hdecomp (c : C) : ∃ d : D, ∃ e : E, d.val.val * e.val = c.val := by
    obtain ⟨⟨l, e⟩, he⟩ := hcomp.2 c.val
    have hlC : l.val ∈ C := by
      have hc := C.mul_mem c.property (C.inv_mem (hEC e.property))
      simpa only [← he, mul_inv_cancel_right] using hc
    have hlD : l ∈ D := by
      rw [mem_centralizer_iff]
      intro s hs
      apply Subtype.ext
      exact (mem_centralizer_iff.mp hlC) s.val ⟨s, hs, rfl⟩
    exact ⟨⟨l, hlD⟩, e, he⟩
  have hDcentralE (d : D) : d.val.val ∈ centralizer (E : Set H) := by
    rw [mem_centralizer_iff]
    intro e he
    exact ((mem_centralizer_iff.mp (hEC he)) d.val.val ⟨d.val, hDS d.property, rfl⟩).symm
  have hCN : C ≤ normalizer (E : Set H) := by
    intro c hc
    obtain ⟨d, e, he⟩ := hdecomp ⟨c, hc⟩
    change d.val.val * e.val = c at he
    rw [← he]
    exact (normalizer (E : Set H)).mul_mem
      (centralizer_le_normalizer (E : Set H) (hDcentralE d)) (E.le_normalizer e.property)
  let EC := E.subgroupOf C
  let : EC.Normal := (normal_subgroupOf_iff_le_normalizer hEC).mpr hCN
  have hECcop : Nat.Coprime 2 (Nat.card EC) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv]
    exact Nat.coprime_two_left.mpr hodd
  let f : D →* C := (L.subtype.comp D.subtype).codRestrict C hDC
  let q := QuotientGroup.mk' EC
  have hsurj : Function.Surjective (q.comp f) := by
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective EC y
    obtain ⟨d, e, he⟩ := hdecomp c
    refine ⟨d, ?_⟩
    let eC : C := ⟨e.val, hEC e.property⟩
    have heC : q eC = 1 := (QuotientGroup.eq_one_iff _).mpr e.property
    have hprod : f d * eC = c := Subtype.ext he
    change q (f d) = q c
    rw [← hprod, map_mul, heC, mul_one]
  have hQ : IsPGroup 2 (C ⧸ EC) := hD.of_surjective (q.comp f) hsurj
  have hmap : (pPrimeCore 2 C).map q = ⊥ := by
    have htwo := hQ.to_subgroup ((pPrimeCore 2 C).map q)
    have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 C).map q)) :=
      Nat.Coprime.of_dvd_right (card_map_dvd _ q) pPrimeCore_coprime_card
    rcases htwo.card_eq_or_dvd with hcard | hdiv
    · exact eq_bot_of_card_eq _ hcard
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp hcop) hdiv)
  have hcore : pPrimeCore 2 C = EC := by
    apply le_antisymm
    · have hle := map_le_iff_le_comap.mp hmap.le
      simpa only [MonoidHom.comap_bot, q, QuotientGroup.ker_mk'] using hle
    · exact le_sSup ⟨inferInstance, hECcop⟩
  rw [hcore]
  exact (map_subgroupOf_eq_of_le hEC).symm

end Subgroup
