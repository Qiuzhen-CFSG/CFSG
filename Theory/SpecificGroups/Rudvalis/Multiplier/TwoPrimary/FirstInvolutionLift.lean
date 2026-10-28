module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Structure
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Involutions
public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction

/-!
# Lifting the marked max4 involution through an elementary central kernel

The marked eight-group lies in both the center and the derived subgroup of
the literal max4 core. In a central extension its lifts therefore commute:
the commutator with a lift of a central element is a homomorphism into the
central kernel and kills the derived subgroup. An exponent-two kernel makes
lift squares independent of the chosen lift. Squares are consequently
multiplicative on the marked eight-group and invariant under conjugation.

Three checked max4 conjugation equations force the three basis squares to
be one. The first max4 generator acts nontrivially on that eight-group, so
it is outside the core; the certified ambient fusion transports the marked
involutory lift to this generator. Every map is the literal model map.

This proves `FirstInvolutionLift`, the ambient branch of the upper bound
for Aschbacher--Smith I.1.3(1), printed p.407. The exponent-two kernel
hypothesis is explicit. The final consumer retains `Max4CoverBounds`, the
independent local-cover calculation. No multiplier-dependent I.2 covering
conclusion is used. The imported model modules preserve the ATLAS source
attribution and checked word conventions.
-/

open Subgroup
open scoped commutatorElement

private theorem central_derived_lifts_commute
    {E B : Type*} [Group E] [Group B] (f : E →* B)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {x y : E} (hx : f x ∈ center B) (hy : f y ∈ _root_.commutator B) :
    Commute x y := by
  have hc (z : E) : ⁅x, z⁆ ∈ center E := by
    apply hk
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp hx (f z)).symm
  let d : E →* center E := {
    toFun z := ⟨⁅x, z⁆, hc z⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      calc
        _ = ⁅x,a⁆ * (a * ⁅x,b⁆) * a⁻¹ := by group
        _ = ⁅x,a⁆ * ⁅x,b⁆ := by rw [mem_center_iff.mp (hc b) a]; group }
  have hmap : (_root_.commutator E).map f = _root_.commutator B := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    rfl
  obtain ⟨z, hz, he⟩ := hmap.symm ▸ hy
  have hxz : Commute x z := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hD : _root_.commutator E ≤ d.ker := by
      apply commutator_le.mpr
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact Subtype.ext (mem_center_iff.mp (d b).property (d a))
    exact congrArg Subtype.val (hD hz)
  have hdiff : y * z⁻¹ ∈ f.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hxc : Commute x (y * z⁻¹) := mem_center_iff.mp (hk hdiff) x
  simpa only [inv_mul_cancel_right] using hxc.mul_right hxz

namespace Rudvalis.Multiplier.TwoPrimary
open SylowOvergroups PerfectCentralCovering CoveringIncidence
open SylowOvergroups.RadicalCoverage.LocalCover
open RankOneEightCharacteristic RankOneEightAction

private theorem marked_lifts_commute
    {E : Type} [Group E] (c : Cover E Model) {x y : E}
    (hx : c.toMonoidHom x ∈ elementary 2) (hy : c.toMonoidHom y ∈ elementary 2) :
    Commute x y := by
  let R := max4Core.comap c.toMonoidHom
  let f := c.toMonoidHom.subgroupComap max4Core
  have hf : Function.Surjective f :=
    c.toMonoidHom.subgroupComap_surjective_of_surjective max4Core c.surjective
  have hk : f.ker ≤ center R := by
    intro z hz
    apply mem_center_iff.mpr
    intro w
    exact Subtype.ext (mem_center_iff.mp
      (c.ker_le_center (congrArg Subtype.val hz)) w)
  let a : R := ⟨x, marked_eight_le_core hx⟩
  let b : R := ⟨y, marked_eight_le_core hy⟩
  have ha : f a ∈ center max4Core := Max4Special.markedCore_le_center hx
  have hb : f b ∈ _root_.commutator max4Core := Max4Special.markedCore_le_derived hy
  exact congrArg Subtype.val (central_derived_lifts_commute f hf hk ha hb).eq

private theorem square_eq_of_conjugate_images
    {E : Type} [Group E] (c : Cover E Model)
    (h2 : ∀ z ∈ c.toMonoidHom.ker, z ^ 2 = 1)
    {x y : E} (hx : c.toMonoidHom x ^ 2 = 1)
    (g : Model) (he : g * c.toMonoidHom x * g⁻¹ = c.toMonoidHom y) :
    x ^ 2 = y ^ 2 := by
  obtain ⟨t, rfl⟩ := c.surjective g
  have hk : x ^ 2 ∈ c.toMonoidHom.ker := by rwa [MonoidHom.mem_ker, map_pow]
  have hc := mem_center_iff.mp (c.ker_le_center hk) t
  calc
    x ^ 2 = (t * x * t⁻¹) ^ 2 := by rw [conj_pow, hc, mul_inv_cancel_right]
    _ = y ^ 2 := square_eq_of_map_eq_of_kernel_exponent_two c.toMonoidHom
      c.ker_le_center h2 (by simpa only [map_mul, map_inv] using he)

private theorem marked_zero_lift_square
    {E : Type} [Group E] (c : Cover E Model)
    (h2 : ∀ z ∈ c.toMonoidHom.ker, z ^ 2 = 1) :
    ∃ x : E, c.toMonoidHom x = elementaryGenerator 0 ∧ x ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := c.surjective (basis 0)
  obtain ⟨b, hb⟩ := c.surjective (basis 1)
  obtain ⟨d, hd⟩ := c.surjective (basis 2)
  have hab : Commute a b := marked_lifts_commute c (ha ▸ basis_mem 0) (hb ▸ basis_mem 1)
  have had : Commute a d := marked_lifts_commute c (ha ▸ basis_mem 0) (hd ▸ basis_mem 2)
  have hbd : Commute b d := marked_lifts_commute c (hb ▸ basis_mem 1) (hd ▸ basis_mem 2)
  have hasq : c.toMonoidHom a ^ 2 = 1 := by rw [ha, pow_two, basis_square]
  have hbsq : c.toMonoidHom b ^ 2 = 1 := by rw [hb, pow_two, basis_square]
  have e0 : a ^ 2 = a ^ 2 * b ^ 2 := by
    rw [← hab.mul_pow]
    apply square_eq_of_conjugate_images c h2 hasq max4Generators.2
    rw [map_mul, ha, hb]
    exact second_conj_zero
  have e1 : b ^ 2 = b ^ 2 * d ^ 2 := by
    rw [← hbd.mul_pow]
    apply square_eq_of_conjugate_images c h2 hbsq max4Generators.2
    rw [map_mul, hb, hd]
    exact second_conj_one
  have e2 : b ^ 2 = a ^ 2 * b ^ 2 * d ^ 2 := by
    rw [← hab.mul_pow, ← (had.mul_left hbd).mul_pow]
    apply square_eq_of_conjugate_images c h2 hbsq max4Generators.1
    rw [map_mul, map_mul, ha, hb, hd]
    exact first_conj_one
  have hb2 : b ^ 2 = 1 := (mul_eq_left.mp e0.symm)
  have hd2 : d ^ 2 = 1 := (mul_eq_left.mp e1.symm)
  refine ⟨a, ha, ?_⟩
  simpa only [hb2, hd2, mul_one] using e2.symm

set_option maxRecDepth 10000 in
private theorem first_outside_core : max4Generators.1 ∉ max4Core := by
  intro hx
  have hc := (max4Core_eq_centralizer ▸ hx).2
  have hm := mem_centralizer_iff.mp hc (basis 1) (basis_mem 1)
  change elementaryGenerator 1 * max4Generators.1 = max4Generators.1 * elementaryGenerator 1 at hm
  have he : max4Generators.1 * elementaryGenerator 1 * max4Generators.1⁻¹ =
      elementaryGenerator 1 := by
    rw [← hm]
    exact mul_inv_cancel_right _ _
  rw [first_conj_one] at he
  have hp := congrArg (fun z : Model => z • (0 : Fin 4060)) he
  simp only [mul_smul, Max4InvolutionCertificate.elementary_smul] at hp
  exact (by decide +kernel :
    (CatalogueCertificate.elementaryPermutation 0 * CatalogueCertificate.elementaryPermutation 1 *
      CatalogueCertificate.elementaryPermutation 2) (0 : Fin 4060) ≠
      CatalogueCertificate.elementaryPermutation 1 0) hp

/-- The elementary-kernel ambient lifting contract, with no further premises. -/
public theorem firstInvolutionLift : FirstInvolutionLift := by
  intro E _ _ c h2
  obtain ⟨a, ha, ha2⟩ := marked_zero_lift_square c h2
  have hs := congrArg max4.subtype max4First_sq
  have hsq : max4Generators.1 ^ 2 = 1 := by
    simpa only [map_pow, map_one, max4First, Subgroup.subtype_apply] using hs
  have hne : max4Generators.1 ≠ 1 := by
    intro h
    apply first_outside_core
    rw [h]
    exact max4Core.one_mem
  have ho : orderOf max4Generators.1 = 2 := orderOf_eq_prime hsq hne
  have hf := outside_core_isConj_marked max4Generators.1 max4First.property first_outside_core ho
  obtain ⟨g, hg⟩ := isConj_iff.mp hf.symm
  obtain ⟨t, ht⟩ := c.surjective g
  refine ⟨t * a * t⁻¹, ?_, ?_⟩
  · simpa only [map_mul, map_inv, ht, ha] using hg
  · rw [conj_pow, ha2, mul_one, mul_inv_cancel]

/-- The literal restriction theorem now needs only the independent max4 cover bounds. -/
public theorem kernel_card_le_two_of_max4_bounds
    (hlocal : Max4CoverBounds)
    {E : Type} [Group E] [Finite E] (c : Cover E Model)
    (hp : IsPGroup 2 c.toMonoidHom.ker) : Nat.card c.toMonoidHom.ker ≤ 2 :=
  kernel_card_le_two_of_local_bounds hlocal firstInvolutionLift c hp

end Rudvalis.Multiplier.TwoPrimary
