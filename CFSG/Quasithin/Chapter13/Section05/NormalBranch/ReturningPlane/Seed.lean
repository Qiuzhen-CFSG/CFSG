module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane.Quotient
public import CFSG.Quasithin.Chapter13.Section05.LocalGeometry.NonabelianClosure

/-!
# The two original hyperplanes above the returning plane

The quaternion closure is nonabelian, so F.9 gives its exact intersection
with V as the source seed V₃. Natural-form duality shows that an element
of L normalizing that seed also fixes its original point V₁. Consequently
a returning plane-normalizer outside the point centralizer moves the seed.
Two distinct order-eight seeds containing the same order-four plane meet
in precisely that plane.

Source: Aschbacher–Smith,13.5.16, printed p.921, using F.9.4 and the
natural flag preceding13.5.4. The earlier13.5.15 conclusions remain explicit.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
open Theory.GroupTheory.Recognition
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

include d

theorem module_card : Nat.card D.V = 16 := by
  rw [Nat.card_congr d.coordinate.toEquiv]
  change Nat.card (natural (Fin 6)) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    finrank_natural_even (Fin 6) (by decide)]
  decide

/-- Nonabelianness is derived from the actual quaternion presentation. -/
theorem closure_intersection_module (h : D.Hypothesis) (b : Conclusions D M 6 g)
    (hM : M = D.L) : D.V ⊓ D.UH = D.Vplus := by
  have hn : ¬ IsMulCommutative D.UH := by
    intro hcomm
    let := hcomm
    let q := QuaternionCentralProduct.dataOfEquiv b.five.2.some
    have hz : center D.UH = ⊤ := by
      apply top_unique
      intro x _
      exact mem_center_iff.mpr (fun y => mul_comm y x)
    have hc := q.center_card
    rw [hz, Nat.card_congr topEquiv.toEquiv, q.card] at hc
    contradiction
  have hi : D.Vplus.relIndex D.V = 2 := by
    have hc := (D.Vplus.subgroupOf D.V).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe h.plus_le).toEquiv,
      d.seed_card, module_card d] at hc
    change (D.Vplus.subgroupOf D.V).index = 2
    omega
  have hs := LocalGeometry.seed_eq_intersection_core h hi hn
  rw [TypeU4.core_eq_closure b hM] at hs
  exact hs

/-- In the original natural action, a seed normalizer fixes its dual point. -/
theorem seed_normalizer_le_point (h : D.Hypothesis) (y : D.L)
    (hy : y.val ∈ normalizer (D.Vplus : Set G)) : y.val ∈ D.Gz := by
  have hs := (localNormalizer_mem d D.Vplus h.plus_le y).mp hy
  have hp := stabilizer_le_orthogonal_stabilizer (Section07.NaturalAction.image d D.Vplus) hs
  rw [Section07.NaturalAction.seed_perpendicular d,
    LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] at hp
  have hpoint := (localNormalizer_mem d D.V₁ (h.point_lt.le.trans h.plus_le) y).mpr hp
  exact h.normalizer_point_eq ▸ hpoint

/-- The literal distinct returning seeds meet in the original plane. -/
theorem seed_intersection (h : D.Hypothesis) (y : D.L)
    (hy : y.val ∈ normalizer (V₂ : Set G)) (hyG : y.val ∉ D.Gz) :
    D.Vplus ⊓ UnitaryFourThree.conjugate D.Vplus y.val = V₂ := by
  let W := UnitaryFourThree.conjugate D.Vplus y.val
  have hcW : Nat.card W = 8 :=
    (card_map_of_injective (MulAut.conj y.val⁻¹).injective).trans d.seed_card
  have hle : V₂ ≤ D.Vplus ⊓ W := by
    apply le_inf d.plane_le_seed
    have he : V₂.map (MulAut.conj y.val⁻¹).toMonoidHom = V₂ :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (V₂ : Set G)).inv_mem hy)
    rw [← he]
    exact map_mono d.plane_le_seed
  have hne : D.Vplus ⊓ W ≠ D.Vplus := by
    intro he
    have hs : D.Vplus ≤ W := he ▸ inf_le_right
    have heq : D.Vplus = W := eq_of_le_of_card_ge hs (by rw [d.seed_card, hcW])
    have hnorm : y.val⁻¹ ∈ normalizer (D.Vplus : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr heq.symm
    have hh : y.val ∈ normalizer (D.Vplus : Set G) := by
      simpa only [inv_inv] using ((normalizer (D.Vplus : Set G)).inv_mem hnorm)
    exact hyG (seed_normalizer_le_point d h y hh)
  have hlt : Nat.card (D.Vplus ⊓ W : Subgroup G) < 8 := by
    have hh : Nat.card (D.Vplus ⊓ W : Subgroup G) < Nat.card D.Vplus :=
      Set.ncard_lt_ncard (lt_of_le_of_ne inf_le_left
        (fun he => hne (SetLike.coe_injective he)))
    rwa [d.seed_card] at hh
  have hdiv := card_dvd_of_le hle
  rw [d.plane_card] at hdiv
  have hpos : 0 < Nat.card (D.Vplus ⊓ W : Subgroup G) := Nat.card_pos
  have hcard : Nat.card (D.Vplus ⊓ W : Subgroup G) = 4 := by
    obtain ⟨n, hn⟩ := hdiv
    omega
  exact (eq_of_le_of_card_ge hle (by rw [d.plane_card, hcard])).symm

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
end
