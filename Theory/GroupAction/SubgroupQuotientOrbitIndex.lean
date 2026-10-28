module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Quotient conjugacy classes and subgroup quotient orbits

Let J be normal in H, and let D be a subgroup of J whose image DH is
normal in H. If an H/J-action on J/D agrees with conjugation, the orbit
of aD has size equal to the centralizer index of aDH in H/DH.

The preimages in H of the two stabilizers are equal. Surjective pullback
preserves index, and orbit-stabilizer finishes the comparison. Every
quotient and subgroup map is literal, so no identification of different
quotients is implicit in the statement.

This general transfer is used for the coset conjugacy count in Parrott,
*A characterization of the Tits' simple group* (1972), pp.674–675.
-/

namespace Subgroup

/-- A compatible quotient action computes the centralizer index in the
ambient quotient using the orbit in the subgroup quotient. -/
public theorem centralizer_index_eq_subgroup_quotient_orbit_card
    {H : Type*} [Group H] (J : Subgroup H) [J.Normal]
    (D : Subgroup J) [D.Normal] [(D.map J.subtype).Normal]
    (f : (H ⧸ J) →* MulAut (J ⧸ D))
    (heval : ∀ (g : H) (b b' : J), (b' : H) = g * (b : H) * g⁻¹ →
      f (QuotientGroup.mk' J g) (QuotientGroup.mk' D b) = QuotientGroup.mk' D b')
    (a : J) :
    (centralizer ({QuotientGroup.mk' (D.map J.subtype) (a : H)} :
      Set (H ⧸ D.map J.subtype))).index =
        (Set.range (fun g => f g (QuotientGroup.mk' D a))).ncard := by
  let DH := D.map J.subtype
  let qH := QuotientGroup.mk' DH
  let qJ := QuotientGroup.mk' J
  let qD := QuotientGroup.mk' D
  let : MulDistribMulAction (H ⧸ J) (J ⧸ D) := MulDistribMulAction.compHom (J ⧸ D) f
  let C := centralizer ({qH (a : H)} : Set (H ⧸ DH))
  let S := MulAction.stabilizer (H ⧸ J) (qD a)
  have heq : C.comap qH = S.comap qJ := by
    ext g
    let b : J := ⟨g * (a : H) * g⁻¹, (inferInstance : J.Normal).conj_mem a a.property g⟩
    have hquot : qH (b : H) = qH (a : H) ↔ qD b = qD a := by
      change ((b : H) : H ⧸ DH) = ((a : H) : H ⧸ DH) ↔ (b : J ⧸ D) = (a : J ⧸ D)
      rw [QuotientGroup.eq_iff_div_mem, QuotientGroup.eq_iff_div_mem]
      constructor
      · rintro ⟨d, hd, hdb⟩
        have hh : d = b / a := Subtype.ext hdb
        exact hh ▸ hd
      · intro hd
        exact ⟨b / a, hd, rfl⟩
    have hC : g ∈ C.comap qH ↔ qH (b : H) = qH (a : H) := by
      change qH g ∈ centralizer ({qH (a : H)} : Set (H ⧸ DH)) ↔ _
      rw [mem_centralizer_singleton_iff]
      have hb : qH (b : H) = qH g * qH (a : H) * (qH g)⁻¹ := by
        change qH (g * (a : H) * g⁻¹) = _
        rw [map_mul, map_mul, map_inv]
      rw [hb]
      exact mul_inv_eq_iff_eq_mul.symm
    have hS : g ∈ S.comap qJ ↔ qD b = qD a := by
      change f (qJ g) (qD a) = qD a ↔ _
      rw [heval g a b rfl]
    exact hC.trans (hquot.trans hS.symm)
  change C.index = _
  rw [← C.index_comap_of_surjective (QuotientGroup.mk'_surjective DH), heq,
    S.index_comap_of_surjective (QuotientGroup.mk'_surjective J)]
  exact MulAction.index_stabilizer (H ⧸ J) (qD a)

end Subgroup
