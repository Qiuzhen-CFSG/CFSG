module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.FactorGeometry
public import Theory.SpecificGroups.MinusExtraspecial.MarkedInvolutionAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.CoreInvolutionFusion

/-!
# Coordinate-free transitivity on the marked root center

The ten noncentral involutions in the actual minus-extraspecial core form
one orbit under H = C_G(z). Orbit-stabilizer gives |C_G(E)| = 192. The root
product R, of order 64, is its normal Sylow two-subgroup, hence characteristic.
Since E = Z(R), this identifies N_G(E) with N_G(R).

An inner conjugator from each core induces a different transposition on E#.
Their products act transitively, so conjugation balances the nonidentity
central square fibers in R. No root coordinates, tensor action, normalizer
splitting or second-involution-centralizer model is assumed.

The common core calculations are adapted from the J₂ `SourceFrame`
implementation; reciprocity here uses only H-type, not its two-class census.
Source: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3 and the proof
of 46.14, printed pp.29–30,251,257–258. The source's V in 8.15 is our E.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Coordinates
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

/-- R is characteristic in C_G(E), being its normal Sylow two-subgroup. -/
theorem R_characteristic_in_centralizer :
    (P.R.subgroupOf (centralizer (P.E : Set G))).Characteristic := by
  let C := centralizer (P.E : Set G)
  let K := P.R.subgroupOf C
  have hKcard : Nat.card K = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe (P.R_le_centralizer_E)).toEquiv).trans (P.R_card )
  have hi : K.index = 3 := by
    have h := K.card_mul_index
    rw [hKcard, P.centralizer_E_card] at h
    omega
  have hKnormal : K.Normal :=
    (normal_subgroupOf_iff_le_normalizer (P.R_le_centralizer_E)).mpr
      (centralizer_E_le_normalizer_R P)
  let S : Sylow 2 C := (IsPGroup.of_card (p := 2) (n := 6) hKcard).toSylow
    (by rw [hi]; decide)
  exact S.characteristic_of_normal hKnormal

/-- The normalizers of the intrinsic center and root product coincide. -/
theorem normalizer_E_eq_normalizer_R :
    normalizer (P.E : Set G) = normalizer (P.R : Set G) := by
  apply le_antisymm
  · let := R_characteristic_in_centralizer P
    have h := normalizer_le_normalizer_characteristic_image
      (centralizer (P.E : Set G)) (P.R.subgroupOf (centralizer (P.E : Set G)))
    rw [map_subgroupOf_eq_of_le (P.R_le_centralizer_E)] at h
    exact (normalizer_le_normalizer_centralizer P.E).trans h
  · have h := normalizer_le_normalizer_characteristic_image P.R (center P.R)
    rwa [E_center P] at h


private noncomputable def actionCoreEquiv : ambientCore D.z ≃* MinusExtraspecial.Model :=
  ((localCore D.z).equivMapOfInjective (involutionCentralizer D.z).subtype
    (involutionCentralizer D.z).subtype_injective).symm.trans D.localType.core_equiv.some

private noncomputable def actionConjugateCoreEquiv : P.conjugateCore ≃* MinusExtraspecial.Model :=
  ((ambientCore D.z).equivMapOfInjective (MulAut.conj P.g).toMonoidHom
    (MulAut.conj P.g).injective).symm.trans actionCoreEquiv

private theorem action_z_center :
    (⟨D.z, HTypeAt.involution_mem_core⟩ : ambientCore D.z) ∈ center (ambientCore D.z) := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (ambientCore_le D.z x.property))

private theorem action_u_center :
    (⟨P.u, P.u_mem_conjugateCore⟩ : P.conjugateCore) ∈ center P.conjugateCore := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (P.conjugateCore_le x.property))

private theorem action_z_ne_one : D.z ≠ 1 := by
  intro h
  have hz := D.localType.involution
  simp [h] at hz

private theorem action_u_ne_one : P.u ≠ 1 := by
  intro h
  have hu := P.u_order
  simp [h] at hu

private theorem mem_normalizer_E_of_images {a : G}
    (hz : a * D.z * a⁻¹ ∈ P.E) (hu : a * P.u * a⁻¹ ∈ P.E) :
    a ∈ normalizer (P.E : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · change (zpowers D.z ⊔ zpowers P.u).map (MulAut.conj a).toMonoidHom ≤ P.E
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hu)
  · rw [card_map_of_injective (MulAut.conj a).injective]

/-- Inner elements of the two actual cores induce the two distinct transpositions on E#. -/
theorem exists_center_transpositions :
    ∃ a b : normalizer (P.R : Set G),
      (a : G) * D.z * (a : G)⁻¹ = D.z ∧
      (a : G) * P.u * (a : G)⁻¹ = D.z * P.u ∧
      (b : G) * D.z * (b : G)⁻¹ = D.z * P.u ∧
      (b : G) * P.u * (b : G)⁻¹ = P.u := by
  obtain ⟨a, ha⟩ := MinusExtraspecial.exists_conjugator_central_mul_of_equiv
    actionCoreEquiv action_z_center
    (fun h => action_z_ne_one (congrArg Subtype.val h))
    (u := (⟨P.u, P.mem_core⟩ : ambientCore D.z))
    (Subtype.ext (P.u_order ▸ pow_orderOf_eq_one P.u))
    (fun h => action_u_ne_one P (congrArg Subtype.val h))
    (fun h => P.ne (congrArg Subtype.val h))
  have haz : (a : G) * D.z * (a : G)⁻¹ = D.z := by
    rw [mem_centralizer_singleton_iff.mp (ambientCore_le D.z a.property)]
    simp only [mul_inv_cancel_right]
  have hau : (a : G) * P.u * (a : G)⁻¹ = D.z * P.u := congrArg Subtype.val ha
  have han : (a : G) ∈ normalizer (P.R : Set G) := by
    rw [← normalizer_E_eq_normalizer_R P ]
    exact mem_normalizer_E_of_images P (haz.symm ▸ P.z_mem_E)
      (hau.symm ▸ P.E.mul_mem P.z_mem_E P.u_mem_E)
  obtain ⟨b, hb⟩ := MinusExtraspecial.exists_conjugator_central_mul_of_equiv
    (actionConjugateCoreEquiv P) (action_u_center P)
    (fun h => action_u_ne_one P (congrArg Subtype.val h))
    (u := (⟨D.z, P.z_mem_conjugateCore ⟩ : P.conjugateCore))
    (Subtype.ext (D.localType.involution ▸ pow_orderOf_eq_one D.z))
    (fun h => action_z_ne_one (congrArg Subtype.val h))
    (fun h => P.ne (congrArg Subtype.val h).symm)
  have hbz : (b : G) * D.z * (b : G)⁻¹ = D.z * P.u :=
    (congrArg Subtype.val hb).trans P.commute.eq.symm
  have hbu : (b : G) * P.u * (b : G)⁻¹ = P.u := by
    rw [mem_centralizer_singleton_iff.mp (P.conjugateCore_le b.property)]
    simp only [mul_inv_cancel_right]
  have hbn : (b : G) ∈ normalizer (P.R : Set G) := by
    rw [← normalizer_E_eq_normalizer_R P ]
    exact mem_normalizer_E_of_images P (hbz.symm ▸ P.E.mul_mem P.z_mem_E P.u_mem_E)
      (hbu.symm ▸ P.u_mem_E)
  exact ⟨⟨a, han⟩, ⟨b, hbn⟩, haz, hau, hbz, hbu⟩

private theorem mem_E_cases {x : G} (hx : x ∈ P.E) :
    x = 1 ∨ x = D.z ∨ x = P.u ∨ x = D.z * P.u := by
  have h := MinusExtraspecial.commuting_square_one_of_equiv actionCoreEquiv action_z_center
    (fun h => action_z_ne_one (congrArg Subtype.val h))
    (u := (⟨P.u, P.mem_core⟩ : ambientCore D.z))
    (x := (⟨x, P.E_le_core hx⟩ : ambientCore D.z))
    (Subtype.ext (P.u_order ▸ pow_orderOf_eq_one P.u))
    (fun h => action_u_ne_one P (congrArg Subtype.val h))
    (fun h => P.ne (congrArg Subtype.val h))
    (Subtype.ext (mem_centralizer_singleton_iff.mp
      (P.R_le_double_centralizer (P.E_le_R hx)).2))
    (Subtype.ext (E_square_eq_one P hx))
  exact h.imp (congrArg Subtype.val)
    (fun h => h.imp (congrArg Subtype.val)
      (fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val)))

/-- The source normalizer is transitive on E#, with no root-coordinate premise. -/
theorem centerTransitive : CenterTransitive P := by
  obtain ⟨a, b, haz, hau, hbz, _⟩ := exists_center_transpositions P
  have hab : ((a * b : normalizer (P.R : Set G)) : G) * D.z *
      ((a * b : normalizer (P.R : Set G)) : G)⁻¹ = P.u := by
    change (MulAut.conj ((a : G) * (b : G))) D.z = P.u
    rw [map_mul]
    change (MulAut.conj (a : G)) ((b : G) * D.z * (b : G)⁻¹) = P.u
    rw [hbz, map_mul]
    change ((a : G) * D.z * (a : G)⁻¹) * ((a : G) * P.u * (a : G)⁻¹) = P.u
    rw [haz, hau, ← mul_assoc, ← pow_two, E_square_eq_one P P.z_mem_E, one_mul]
  have hbase : ∀ x ∈ P.E, x ≠ 1 → ∃ c : normalizer (P.R : Set G),
      (c : G) * D.z * (c : G)⁻¹ = x := by
    intro x hx hx1
    rcases (mem_E_cases P hx).resolve_left hx1 with rfl | rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨a * b, hab⟩
    · exact ⟨b, hbz⟩
  intro e he he1 f hf hf1
  obtain ⟨c, hc⟩ := hbase e he he1
  obtain ⟨d, hd⟩ := hbase f hf hf1
  refine ⟨d * c⁻¹, ?_⟩
  change (d : G) * (c : G)⁻¹ * e * ((d : G) * (c : G)⁻¹)⁻¹ = f
  rw [← hc, ← hd]
  group

/-- The actual source action balances all nonidentity central square fibers in R. -/
theorem source_squareFibers_balanced
    (c d : center P.R) (hc : c ≠ 1) (hd : d ≠ 1) :
    Nat.card {x : P.R // x ^ 2 = (c : P.R)} =
      Nat.card {x : P.R // x ^ 2 = (d : P.R)} :=
  squareFibers_balanced P (centerTransitive P) c d hc hd

end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Coordinates
