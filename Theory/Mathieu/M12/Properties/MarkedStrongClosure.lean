module

public import Theory.Mathieu.M11.Properties.MarkedStrongClosure
public import Theory.Mathieu.M12.Properties.PointStabilizer
public import Theory.Mathieu.M12.SylowCenterSquares

/-!
# Returning conjugates of a two-central M₁₂ involution

The genuine M₁₁ point-stabilizer embedding carries a noncommuting pair of
involutions into M₁₂. Choose that pair as conjugates of the fourth power of
an order-eight element, so both are squares. The checked M₁₂ square-fusion
theorem puts both in the marked central class. A containing Sylow subgroup
and Sylow conjugacy place the pair in the supplied Sylow subgroup. Its
nonidentity central marker belongs to the same class by the literal
Sylow-center calculation.

The two M₁₂ involution classes remain distinct. No new enumeration, global
single-class premise, covering-group fact or multiplier calculation is used.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and the Bender inspection
in Proposition 2.2.2, pp.519--520 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu
open M12SmallPair

private theorem m12_central_marker_conjugate (R : Sylow 2 M12)
    (v : M12) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) : IsConj z v := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 R commonSylow
  let e := MulAut.conj g
  have hmap : (R : Subgroup M12).map e.toMonoidHom = sylowCandidate := by
    change ((g • R : Sylow 2 M12) : Subgroup M12) = sylowCandidate
    rw [hg]
    rfl
  have hvZ : v ∈ (center R).map (R : Subgroup M12).subtype := by
    refine ⟨⟨v, hv⟩, mem_center_iff.mpr ?_, rfl⟩
    intro x
    exact Subtype.ext (hc x x.property).symm.eq
  have himage := map_subgroup_center_le e.toMonoidHom (R : Subgroup M12)
    (mem_map_of_mem e.toMonoidHom hvZ)
  rw [hmap] at himage
  obtain ⟨x, hxc, hxe⟩ := himage
  rcases (sylowCandidate_center_mem x).mp hxc with hx1 | hxz
  · have hev : e v = 1 := hxe.symm.trans hx1
    have hv1 : v = 1 := e.injective (hev.trans (map_one e).symm)
    simp [hv1] at ho
  · exact (isConj_iff.mpr ⟨g, hxe.symm.trans hxz⟩).symm

/-- Every two-central marker has noncommuting conjugates in its supplied
Sylow subgroup. The square marking is proved through the actual M₁₁ embedding. -/
theorem m12_sylow_noncommuting_conjugates (R : Sylow 2 M12)
    (v : M12) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : M12) ∧ IsConj v (b : M12) ∧ ¬Commute a b := by
  obtain ⟨P, r, _, hr, _, _, _⟩ := m11_exists_semidihedral_sylow
  have hro : orderOf (r : M11) = 8 := by
    simpa only [Subgroup.orderOf_coe] using hr
  let t : M11 := (r : M11) ^ 4
  have ht : orderOf t = 2 := by
    dsimp only [t]
    rw [orderOf_pow_of_dvd (by decide : (4 : ℕ) ≠ 0) (by rw [hro]; decide), hro]
  obtain ⟨a, b, ha, hb, hab⟩ := m11_sylow_noncommuting_conjugates P t ht
  let f : M11 →* M12 :=
    (MulAction.stabilizer M12 (12 : Fin 12)).subtype.comp m11ToM12PointStabilizer
  have hf : Function.Injective f :=
    (MulAction.stabilizer M12 (12 : Fin 12)).subtype_injective.comp
      m11ToM12PointStabilizer_injective
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map f).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 Q R
  let j : M11 →* M12 := (MulAut.conj g).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hf
  have hjP : (P : Subgroup M11).map j ≤ (R : Subgroup M12) := by
    rintro _ ⟨x, hx, rfl⟩
    change (MulAut.conj g) (f x) ∈ (R : Subgroup M12)
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hQ (mem_map_of_mem f hx))
  have hclass (x : M11) (hx : IsConj t x) : IsConj z (j x) := by
    obtain ⟨k, hk⟩ := isConj_iff.mp hx
    have hxorder : orderOf x = 2 := by
      have he : orderOf (k * t * k⁻¹) = orderOf t := (MulAut.conj k).orderOf_eq t
      rwa [hk, ht] at he
    have hjorder : orderOf (j x) = 2 := (orderOf_injective j hj x).trans hxorder
    have hsquare : ∃ y : M12, y ^ 2 = j x := by
      refine ⟨j (k * (r : M11) ^ 2 * k⁻¹), ?_⟩
      rw [← map_pow]
      apply congrArg j
      calc
        (k * (r : M11) ^ 2 * k⁻¹) ^ 2 = k * (r : M11) ^ 4 * k⁻¹ := by
          change ((MulAut.conj k) ((r : M11) ^ 2)) ^ 2 =
            (MulAut.conj k) ((r : M11) ^ 4)
          rw [← map_pow, ← pow_mul]
        _ = x := hk
    obtain ⟨h, hh⟩ := M12SylowCenters.square_involution_conjugate (j x) hjorder hsquare
    exact isConj_iff.mpr ⟨h, hh⟩
  have hmarker := m12_central_marker_conjugate R v hv ho hc
  refine ⟨⟨j a, hjP (mem_map_of_mem j a.property)⟩,
    ⟨j b, hjP (mem_map_of_mem j b.property)⟩,
    hmarker.symm.trans (hclass a ha), hmarker.symm.trans (hclass b hb), ?_⟩
  intro hcomm
  apply hab
  have hh := hcomm.map (R : Subgroup M12).subtype
  change Commute (j (a : M11)) (j (b : M11)) at hh
  exact Subtype.ext (Commute.of_map hj hh).eq

end Sporadic.Mathieu
