module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Radical
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Quadratic geometry of a marked doubled-dual extension

The central elementary kernel makes squares well defined on the quotient.
A natural target forces the square maps on each pure dual factor to vanish.
The actual commutator pairing therefore has only cross terms; a nonzero pairing
has zero radical by transitivity on nonzero covectors.

This adapts the literal square and commutator transport in MS93's
DistanceFour/CenterAssembly to a central kernel larger than the natural target.
The fourth-case application constructs all these data from its actual sections.
Source: MS93 (1993), Lemma 4.5 and the binary argument in (4.6.11)--(4.6.12).
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.QuadraticRadical
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear

/-- Literal quotient, natural subgroup, and their common marking. -/
structure Extension (E J : Type*) [Group E] [Group J] where
  actor : J →* S
  actor_surjective : Function.Surjective actor
  action : J →* MulAut E
  quotient : E →* Multiplicative (W × W)
  onto : Function.Surjective quotient
  kernel_central : quotient.ker ≤ center E
  kernel_square : ∀ x : quotient.ker, x ^ 2 = 1
  U : Subgroup E
  coordinates : U ≃* Multiplicative W
  square_mem : ∀ x : E, x ^ 2 ∈ U
  commutator_mem : ∀ x y : E, ⁅x,y⁆ ∈ U
  quotient_action : ∀ (j : J) (x : E),
    (quotient (action j x)).toAdd =
      (dual (actor j) (quotient x).toAdd.1, dual (actor j) (quotient x).toAdd.2)
  coordinates_action : ∀ (j : J) (x y : U),
    (y : E) = action j x →
    (coordinates y).toAdd = (actor j).val.mulVec (coordinates x).toAdd

namespace Extension
variable {E J : Type*} [Group E] [Group J] (d : Extension E J)

private theorem natural_square (x : d.U) : x ^ 2 = 1 := by
  apply d.coordinates.injective
  rw [map_pow, map_one, pow_two]
  change Multiplicative.ofAdd ((d.coordinates x).toAdd + (d.coordinates x).toAdd) =
    Multiplicative.ofAdd 0
  congr 1
  ext i
  exact CharTwo.add_self_eq_zero _

private theorem coordinates_zero_iff (x : d.U) :
    (d.coordinates x).toAdd = 0 ↔ (x : E) = 1 := by
  constructor
  · intro h
    have he : d.coordinates x = 1 := congrArg Multiplicative.ofAdd h
    exact congrArg Subtype.val (d.coordinates.injective (he.trans d.coordinates.map_one.symm))
  · intro h
    have hx : x = 1 := Subtype.ext h
    rw [hx, map_one]
    rfl

private theorem square_eq_of_image_eq {x y : E}
    (h : d.quotient x = d.quotient y) : x ^ 2 = y ^ 2 := by
  let c := x * y⁻¹
  have hc : c ∈ d.quotient.ker := by
    change d.quotient (x * y⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hc2 : c ^ 2 = 1 := congrArg Subtype.val (d.kernel_square ⟨c, hc⟩)
  have hcomm : Commute c y := (mem_center_iff.mp (d.kernel_central hc) y).symm
  have he : x = c * y := by simp [c]
  rw [he, hcomm.mul_pow, hc2, one_mul]

private noncomputable def squareMap (v : W × W) : W :=
  (d.coordinates ⟨(Classical.choose (d.onto (Multiplicative.ofAdd v))) ^ 2,
    d.square_mem _⟩).toAdd

private theorem squareMap_image (x : E) :
    d.squareMap (d.quotient x).toAdd =
      (d.coordinates ⟨x ^ 2, d.square_mem x⟩).toAdd := by
  unfold squareMap
  congr 2
  apply Subtype.ext
  exact d.square_eq_of_image_eq (Classical.choose_spec (d.onto _))

private theorem squareMap_equivariant (g : S) (v : W × W) :
    d.squareMap (dual g v.1, dual g v.2) = g.val.mulVec (d.squareMap v) := by
  obtain ⟨m, hm⟩ := d.actor_surjective g
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  have hv : (d.quotient x).toAdd = v := congrArg Multiplicative.toAdd hx
  have hact := d.quotient_action m x
  rw [hm] at hact
  rw [← hv, ← hact, d.squareMap_image, d.squareMap_image, ← hm]
  apply d.coordinates_action
  exact (map_pow (d.action m) x 2).symm

private theorem squareMap_first (v : W) : d.squareMap (v, 0) = 0 := by
  apply equivariantDualMap_zero (fun w => d.squareMap (w, 0)) _ v
  intro g w
  simpa only [dual, Matrix.mulVec_zero] using d.squareMap_equivariant g (w, 0)

private theorem squareMap_second (v : W) : d.squareMap (0, v) = 0 := by
  apply equivariantDualMap_zero (fun w => d.squareMap (0, w)) _ v
  intro g w
  simpa only [dual, Matrix.mulVec_zero] using d.squareMap_equivariant g (0, w)

private theorem square_eq_one_of_pure (x : E)
    (hx : (d.quotient x).toAdd.1 = 0 ∨ (d.quotient x).toAdd.2 = 0) : x ^ 2 = 1 := by
  apply (d.coordinates_zero_iff ⟨x ^ 2, d.square_mem x⟩).mp
  rw [← d.squareMap_image]
  rcases hx with hx | hx
  · have he : (d.quotient x).toAdd = (0, (d.quotient x).toAdd.2) :=
      Prod.ext hx rfl
    rw [he, d.squareMap_second]
  · have he : (d.quotient x).toAdd = ((d.quotient x).toAdd.1, 0) :=
      Prod.ext rfl hx
    rw [he, d.squareMap_first]

private theorem commutator_eq_one_of_pure
    (x y : E)
    (hpure : ((d.quotient x).toAdd.1 = 0 ∧ (d.quotient y).toAdd.1 = 0) ∨
      ((d.quotient x).toAdd.2 = 0 ∧ (d.quotient y).toAdd.2 = 0)) : ⁅x,y⁆ = 1 := by
  have hx : x ^ 2 = 1 := d.square_eq_one_of_pure x (hpure.elim
    (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  have hy : y ^ 2 = 1 := d.square_eq_one_of_pure y (hpure.elim
    (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  have hxy : (x*y) ^ 2 = 1 := by
    apply d.square_eq_one_of_pure
    rw [map_mul, toAdd_mul]
    rcases hpure with h | h
    · apply Or.inl
      change (d.quotient x).toAdd.1 + (d.quotient y).toAdd.1 = 0
      rw [h.1, h.2, add_zero]
    · apply Or.inr
      change (d.quotient x).toAdd.2 + (d.quotient y).toAdd.2 = 0
      rw [h.1, h.2, add_zero]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hy)
  rw [commutatorElement_def, hxi, hyi]
  simpa only [pow_two, mul_assoc] using hxy

/-- The standard central-extension pairing is restricted to the proven exact
kernel by its commutator evaluation formula, without identifying the center. -/
private theorem exists_actual_pairing :
    ∃ b : (W × W) → (W × W) → W,
      (∀ x y z, b (x+y) z = b x z + b y z) ∧
      (∀ x y : E, b (d.quotient x).toAdd (d.quotient y).toAdd =
        (d.coordinates ⟨⁅x,y⁆, d.commutator_mem x y⟩).toAdd) := by
  obtain ⟨B, hB⟩ := CentralExtension.exists_lift_commutator_pairing
    d.quotient d.onto d.kernel_central (MonoidHom.id (Multiplicative (W × W)))
  have hmem (x y : W × W) : ((B x y).toMul : E) ∈ d.U := by
    obtain ⟨a, ha⟩ := d.onto (Multiplicative.ofAdd x)
    obtain ⟨b, hb⟩ := d.onto (Multiplicative.ofAdd y)
    rw [hB x y a b ha hb]
    exact d.commutator_mem a b
  let b : (W × W) → (W × W) → W := fun x y =>
    (d.coordinates ⟨(B x y).toMul, hmem x y⟩).toAdd
  refine ⟨b, ?_, ?_⟩
  · intro x y z
    have he : (⟨(B (x+y) z).toMul, hmem (x+y) z⟩ : d.U) =
        ⟨(B x z).toMul, hmem x z⟩ * ⟨(B y z).toMul, hmem y z⟩ := by
      apply Subtype.ext
      change ((B (x+y) z).toMul : E) =
        (B x z).toMul * (B y z).toMul
      rw [map_add, AddMonoidHom.add_apply]
      rfl
    change (d.coordinates ⟨(B (x+y) z).toMul, _⟩).toAdd = _
    rw [he, map_mul, toAdd_mul]
  · intro x y
    apply congrArg (fun z : d.U => (d.coordinates z).toAdd)
    apply Subtype.ext
    exact hB _ _ x y rfl rfl

private theorem pairing_symmetric
    (b : (W × W) → (W × W) → W)
    (heval : ∀ x y : E, b (d.quotient x).toAdd (d.quotient y).toAdd =
      (d.coordinates ⟨⁅x,y⁆, d.commutator_mem x y⟩).toAdd) (v w : W × W) : b v w = b w v := by
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd w)
  have hv : (d.quotient x).toAdd = v := congrArg Multiplicative.toAdd hx
  have hw : (d.quotient y).toAdd = w := congrArg Multiplicative.toAdd hy
  rw [← hv, ← hw, heval, heval]
  apply congrArg (fun z : d.U => (d.coordinates z).toAdd)
  apply Subtype.ext
  have hs : (⁅x,y⁆ : E) ^ 2 = 1 :=
    congrArg Subtype.val (d.natural_square ⟨⁅x,y⁆, d.commutator_mem x y⟩)
  have hi : (⁅x,y⁆ : E)⁻¹ = ⁅x,y⁆ :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs)
  exact hi.symm.trans (commutatorElement_inv x y)

private theorem pairing_equivariant
    (b : (W × W) → (W × W) → W)
    (heval : ∀ x y : E, b (d.quotient x).toAdd (d.quotient y).toAdd =
      (d.coordinates ⟨⁅x,y⁆, d.commutator_mem x y⟩).toAdd)
    (g : S) (v w : W × W) :
    b (dual g v.1, dual g v.2) (dual g w.1, dual g w.2) = g.val.mulVec (b v w) := by
  obtain ⟨m, hm⟩ := d.actor_surjective g
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd w)
  have hv : (d.quotient x).toAdd = v := congrArg Multiplicative.toAdd hx
  have hw : (d.quotient y).toAdd = w := congrArg Multiplicative.toAdd hy
  have hax := d.quotient_action m x
  have hay := d.quotient_action m y
  rw [hm] at hax hay
  rw [← hv, ← hw, ← hax, ← hay, heval, heval, ← hm]
  apply d.coordinates_action
  exact (map_commutatorElement (d.action m) x y).symm

/-- Noncommutativity and the actual marked maps force the center into the kernel. -/
theorem center_le_kernel (hne : ∃ x y : E, ⁅x,y⁆ ≠ 1) :
    center E ≤ d.quotient.ker := by
  obtain ⟨b, hadd, heval⟩ := d.exists_actual_pairing
  have hs := d.pairing_symmetric b heval
  have he := d.pairing_equivariant b heval
  have hfirst (v w : W) : b (v,0) (w,0) = 0 := by
    obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd (v,0))
    obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd (w,0))
    have hv : (d.quotient x).toAdd = (v,0) := congrArg Multiplicative.toAdd hx
    have hw : (d.quotient y).toAdd = (w,0) := congrArg Multiplicative.toAdd hy
    rw [← hv, ← hw, heval]
    apply (d.coordinates_zero_iff _).mpr
    exact d.commutator_eq_one_of_pure x y (Or.inr
      ⟨congrArg Prod.snd hv, congrArg Prod.snd hw⟩)
  have hsecond (v w : W) : b (0,v) (0,w) = 0 := by
    obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd (0,v))
    obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd (0,w))
    have hv : (d.quotient x).toAdd = (0,v) := congrArg Multiplicative.toAdd hx
    have hw : (d.quotient y).toAdd = (0,w) := congrArg Multiplicative.toAdd hy
    rw [← hv, ← hw, heval]
    apply (d.coordinates_zero_iff _).mpr
    exact d.commutator_eq_one_of_pure x y (Or.inl
      ⟨congrArg Prod.fst hv, congrArg Prod.fst hw⟩)
  have hbne : ∃ x y, b x y ≠ 0 := by
    obtain ⟨x,y,hxy⟩ := hne
    refine ⟨(d.quotient x).toAdd, (d.quotient y).toAdd, ?_⟩
    rw [heval]
    exact fun hh => hxy ((d.coordinates_zero_iff _).mp hh)
  intro x hx
  have hv : (d.quotient x).toAdd = 0 := by
    apply alternating_pair_separating b hadd hs hfirst hsecond he hbne
    intro v
    obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd v)
    have hv : (d.quotient y).toAdd = v := congrArg Multiplicative.toAdd hy
    rw [← hv, heval]
    apply (d.coordinates_zero_iff _).mpr
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx y).symm
  exact hv

end Extension
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.QuadraticRadical
