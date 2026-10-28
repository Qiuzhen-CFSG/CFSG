module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo.NaturalFour.Calculation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.LocalImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction

/-!
# Order-four fixed vectors in the actual natural layer

An elementary four-group in SL₃(2) has its natural fixed space contained in
its displacement space. Normalize one involution, apply the small checked
matrix calculation, and conjugate the displacements back. The compatible
`LocalModel` then identifies these displacements with genuine commutators
in the amalgam, retaining both its projection kernel and its action marking.

The final configuration theorem supplies exactly the order-four premise of
`Configuration.backward_index_two_of_R1_controls`: every element of Uₐ
centralizing Vδ lies in [Zₐ,Vδ]. It requires no R₁ or failed-escape bounds.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, the sentence using |VδQₐ/Qₐ| > q and
[R₁,Vδ] = 1 to obtain R₁ ≤ [Zₐ,Vδ].
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
open Escape.Propagation.Backward.Products.Selection.Choices
open BinaryLinearThree.FourGroupGeometry.FixedSpaces (involution exists_involution_conjugator)
namespace NaturalFour
private theorem exists_second (E : Subgroup SL) (hc : Nat.card E = 4) (a : E) :
    ∃ b : E, b ≠ 1 ∧ b ≠ a := by
  classical
  let := Fintype.ofFinite E
  have hh : ({1, a} : Finset E).card < (Finset.univ : Finset E).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hc]
    exact (Finset.card_insert_le _ _).trans_lt (by simp)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hh
  exact ⟨b, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hb⟩

/-- Every subgroup containing the natural displacements of a four-group
contains its fixed vectors. -/
theorem fixedSpace_le_of_displacements (E : Subgroup SL)
    (hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 4)
    (D : Subgroup Space)
    (hD : ∀ g ∈ E, ∀ v : Space, modelAction g v * v⁻¹ ∈ D) :
    fixedSpace E ≤ D := by
  let := hE
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : E)
  have ha' : (a : SL) ≠ 1 := fun h => ha (Subtype.ext h)
  have hasq : (a : SL) * a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : SL) a.property
  obtain ⟨k, hk⟩ := exists_involution_conjugator a ha' hasq
  let H := E.map (MulAut.conj k⁻¹).toMonoidHom
  have hat : MulAut.conj k⁻¹ (a : SL) = involution := by
    change k⁻¹ * a * (k⁻¹)⁻¹ = involution
    rw [inv_inv, mul_assoc, hk, inv_mul_cancel_left]
  have ht : involution ∈ H := ⟨a, a.property, hat⟩
  have hHE : IsElementaryAbelian 2 H := IsElementaryAbelian.map _
  let := hHE
  have hHc : Nat.card H = 4 := (card_map_of_injective (MulAut.conj k⁻¹).injective).trans hc
  obtain ⟨b, hb1, hbt⟩ := exists_second H hHc ⟨involution, ht⟩
  have hb1' : (b : SL) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbt' : (b : SL) ≠ involution := fun h => hbt (Subtype.ext h)
  have hbsq : (b : SL) * b = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (b : SL) b.property
  have hbcomm : (b : SL) * involution = involution * b :=
    congrArg Subtype.val (mul_comm b (⟨involution, ht⟩ : H))
  obtain ⟨c, hcE, hcb⟩ := b.property
  change MulAut.conj k⁻¹ c = (b : SL) at hcb
  have hconj (g : SL) (v : Space) :
      modelAction k (modelAction (MulAut.conj k⁻¹ g) v) =
        modelAction g (modelAction k v) := by
    change modelAction k (modelAction (k⁻¹ * g * (k⁻¹)⁻¹) v) = _
    rw [inv_inv, ← MulAut.mul_apply, ← map_mul]
    simp only [mul_assoc, mul_inv_cancel_left, map_mul, MulAut.mul_apply]
  intro w hw
  let w' := modelAction k⁻¹ w
  have hfix (g : SL) (hg : g ∈ E) : modelAction (MulAut.conj k⁻¹ g) w' = w' := by
    apply (modelAction k).injective
    rw [hconj]
    have hkw : modelAction k w' = w := by
      change modelAction k (modelAction k⁻¹ w) = w
      rw [map_inv, MulAut.apply_inv_self]
    rw [hkw]
    exact hw g hg
  have htw : involution.val.mulVec w'.toAdd = w'.toAdd := by
    exact congrArg Multiplicative.toAdd (hat ▸ hfix a a.property)
  have hbw : (b : SL).val.mulVec w'.toAdd = w'.toAdd := by
    exact congrArg Multiplicative.toAdd (hcb ▸ hfix c hcE)
  obtain ⟨u, v, huv⟩ := normalized_fixed_displacement b hb1' hbt' hbsq hbcomm w'.toAdd htw hbw
  have hw' : w' = (modelAction involution (Multiplicative.ofAdd u) * (Multiplicative.ofAdd u)⁻¹) *
      (modelAction b (Multiplicative.ofAdd v) * (Multiplicative.ofAdd v)⁻¹) := by
    apply Multiplicative.toAdd.injective
    change w'.toAdd = (involution.val.mulVec u + -u) + ((b : SL).val.mulVec v + -v)
    simpa only [sub_eq_add_neg] using huv
  have hkw : modelAction k w' = w := by
    change modelAction k (modelAction k⁻¹ w) = w
    rw [map_inv, MulAut.apply_inv_self]
  have he := congrArg (modelAction k) hw'
  rw [hkw, map_mul, map_mul, map_mul, map_inv, map_inv, ← hat, ← hcb,
    hconj, hconj] at he
  rw [he]
  exact D.mul_mem (hD a a.property _) (hD c hcE _)
end NaturalFour

variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Transport natural fixed vectors using the projection and module marking
of the same local model. -/
theorem natural_fixed_le_commutator {a : Vertex R} (model : LocalModel a)
    (E : Subgroup (FreeAmalgam R)) (hES : E ≤ stabilizer R a)
    [IsElementaryAbelian 2 E] (hfour : (Q R a).relIndex E = 4) :
    U R a ⊓ centralizer (E : Set (FreeAmalgam R)) ≤ ⁅Z R a, E⁆ := by
  let := IsElementaryAbelian.subgroupOf (p := 2) hES
  have hI : IsElementaryAbelian 2 (model.actorImage E) :=
    IsElementaryAbelian.map model.projection
  have hIc : Nat.card (model.actorImage E) = 4 :=
    (model.actorImage_card E hES).trans hfour
  have hcalc : fixedSpace (model.actorImage E) ≤ model.coordinates ⁅Z R a, E⁆ := by
    apply NaturalFour.fixedSpace_le_of_displacements (model.actorImage E) hI hIc
    rintro g ⟨x, hx, rfl⟩ v
    obtain ⟨u, rfl⟩ := model.equiv.surjective v
    let z : U R a := ⟨x * (u : FreeAmalgam R) * (x : FreeAmalgam R)⁻¹,
      (mem_normalizer_iff.mp (U_normalized a x.property) u).mp u.property⟩
    refine ⟨z * u⁻¹, ?_, ?_⟩
    · change (x : FreeAmalgam R) * u * (x : FreeAmalgam R)⁻¹ * (u : FreeAmalgam R)⁻¹ ∈ ⁅Z R a, E⁆
      rw [commutator_comm]
      exact commutator_mem_commutator hx (U_le_Z R a u.property)
    · change model.equiv (z * u⁻¹) = _
      rw [map_mul, map_inv, model.action x u z rfl]
  intro u hu
  let u0 : U R a := ⟨u, hu.1⟩
  have hf : model.equiv u0 ∈ fixedSpace (model.actorImage E) := by
    rw [model.fixedSpace_actorImage E hES]
    exact ⟨u0, hu, rfl⟩
  obtain ⟨v, hv, he⟩ := hcalc hf
  have hvu : v = u0 := model.equiv.injective he
  change (v : FreeAmalgam R) ∈ ⁅Z R a, E⁆ at hv
  rw [hvu] at hv
  exact hv

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- The literal order-four premise needed by the R₁/index-two argument. -/
theorem backward_natural_fixed_le_commutator [Finite M] (s : Configuration p)
    (hb : 4 < geometry.b R) {source : LocalSource L R}
    (common : CommonFacts R source geometry)
    (hfour : (Q R a).relIndex (V R s.delta) = 4) :
    U R a ⊓ centralizer (V R s.delta : Set (FreeAmalgam R)) ≤ ⁅Z R a, V R s.delta⁆ := by
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) a p.start_color
  let := s.radius_elementary hb
  exact natural_fixed_le_commutator model (V R s.delta)
    (s.radius_le_start_stabilizer hb) hfour

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
