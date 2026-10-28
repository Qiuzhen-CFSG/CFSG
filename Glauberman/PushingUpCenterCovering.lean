module
public import Glauberman.PushingUpFullCenters
public import Glauberman.PushingUpOmegaFixedIndex
public import Theory.Representation.SL2FourQuadraticRecognition.NaturalCovering

/-!
# Natural commutator covering of the original Sylow center

The natural quotient of the original central omega action makes the Sylow
moved span cover its fixed space modulo the ambient fixed space. Translating
this identity back through the literal conjugation action gives
[Z(O₂(H)), S] Z(H) = Z(S). The original fixed-index estimates also give
|Z(S) : Z(H)| = 4. Both conclusions retain the original Sylow subgroup and
its chosen automorphism, with no natural-module or fixed-space input.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(g),
printed page 47. These are the covering and index inputs for extension of
the actual intersection lattice to depth 3v - 1.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory
open scoped IsMulCommutative
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

omit [Finite H] [Field F] [Finite F] in
theorem omegaAction_moved_space (L : Subgroup H) :
    Representation.NormalElementaryQuotient.commutatorSpace (omegaCenterIn (pCore 2 H)) L =
      subspaceCommutator (omegaAction H) ⊤ L := by
  let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
  have he : omegaAction H = Representation.NormalElementaryQuotient.originalAction
      (omegaCenterIn (pCore 2 H)) := by
    apply MonoidHom.ext
    intro h
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [omegaAction_apply, Representation.NormalElementaryQuotient.originalAction_apply]
  rw [he]
  exact Representation.NormalElementaryQuotient.original_moved_space _ L

omit [Finite H] [Field F] [Finite F] in
theorem omegaAction_moved_fixed_join (S : Subgroup H)
    (hcover : subspaceCommutator (omegaAction H) ⊤ S ⊔ fixedSpace (omegaAction H) ⊤ =
      fixedSpace (omegaAction H) S) :
    ⁅omegaCenterIn (pCore 2 H), S⁆ ⊔ (omegaCenterIn (pCore 2 H) ⊓ center H) =
      omegaCenterIn (pCore 2 H) ⊓ centralizer (S : Set H) := by
  let V := omegaCenterIn (pCore 2 H)
  let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
  have hmem (v : Additive V) :
      v ∈ subspaceCommutator (omegaAction H) ⊤ S ↔ (v.toMul : H) ∈ ⁅V, S⁆ := by
    rw [← omegaAction_moved_space]
    rfl
  apply le_antisymm
  · refine sup_le (le_inf (commutator_le_left V S) ?_)
      (inf_le_inf_left V (center_le_centralizer _))
    intro x hx
    let v : Additive V := Additive.ofMul ⟨x, commutator_le_left V S hx⟩
    have hv : v ∈ fixedSpace (omegaAction H) S := by
      rw [← hcover]
      exact Submodule.mem_sup_left ((hmem v).mpr hx)
    exact (omegaAction_fixedSpace H S v).mp hv
  · intro x hx
    let v : Additive V := Additive.ofMul ⟨x, hx.1⟩
    have hv : v ∈ fixedSpace (omegaAction H) S := (omegaAction_fixedSpace H S v).mpr hx.2
    rw [← hcover] at hv
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
    have ha' : (a.toMul : H) ∈ ⁅V, S⁆ := (hmem a).mp ha
    have hb' : (b.toMul : H) ∈ center H := by
      have hc := (omegaAction_fixedSpace H ⊤ b).mp hb
      simpa only [coe_top, centralizer_univ] using hc
    have hm := mul_mem_sup ha' (show (b.toMul : H) ∈ V ⊓ center H from ⟨b.toMul.property, hb'⟩)
    have he : (a.toMul : H) * (b.toMul : H) = x :=
      congrArg (fun w : Additive V => (w.toMul : H)) hab
    exact he ▸ hm

theorem original_psl2_four_center_commutator_covering
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    ⁅centerIn (pCore 2 H), (S : Subgroup H)⁆ ⊔ center H = centerIn (S : Subgroup H) := by
  obtain ⟨q, hq, _, _, _, _, E, hE⟩ := original_psl2_four_omegaAction_recognition
    hF S hu K e hf hno.noCharacteristicNormal
  have hquad := (original_psl2_four_omegaAction_sylow hF S hu K e hf
    hno.noCharacteristicNormal).2.1
  have hcover := Representation.SL2FourQuadraticRecognition.sylow_moved_covers_fixed_of_natural_quotient
    (omegaAction H) q hq E hE S hquad
  have hh := omegaAction_moved_fixed_join (S : Subgroup H) hcover
  obtain ⟨hglobal, hfixed⟩ := original_psl2_four_full_center_fixed_spaces hF S α hu K e hf hno
  have hcenter := (original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno).2
  rw [hglobal] at hh
  have hh' : ⁅omegaCenterIn (pCore 2 H), (S : Subgroup H)⁆ ⊔ center H =
      centerIn (S : Subgroup H) := hh.trans hfixed
  rw [hcenter] at hh'
  exact hh'

/-- The original full Sylow center has index four over the ambient center. -/
theorem original_psl2_four_center_index
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    (center H).relIndex (centerIn (S : Subgroup H)) = 4 := by
  let V := omegaCenterIn (pCore 2 H)
  obtain ⟨hZ, hZS⟩ := original_psl2_four_full_center_fixed_spaces hF S α hu K e hf hno
  obtain ⟨hlower, htop⟩ := original_psl2_four_omega_fixedIndex_data hF S hu K e hf
    hno.noCharacteristicNormal
  have hSQ : ¬ (S : Subgroup H) ≤ pCore 2 H := by
    have hi := (Theory.SpecificGroups.SL2.sylow_twoCore_quotient_elementary_four hF S hu K e).2
    intro h
    have he := relIndex_eq_one.mpr h
    rw [relIndex, index_eq_card] at he
    omega
  have hlow := hlower (S : Subgroup H) le_rfl hSQ
  have hdim := (original_psl2_four_omegaAction_sylow hF S hu K e hf
    hno.noCharacteristicNormal).2.2.1
  have hi : (centerIn (S : Subgroup H)).relIndex V = 4 := by
    rw [← hZS]
    apply le_antisymm ?_ hlow
    rw [omegaAction_fixed_index]
    exact Nat.pow_le_pow_right (by decide) hdim
  have htop' := (htop ⊤ (by simp)).1
  simp only [coe_top, centralizer_univ, hZ] at htop'
  have hZV : center H ≤ V := hZ ▸ inf_le_left
  have hZSV : centerIn (S : Subgroup H) ≤ V := hZS ▸ inf_le_left
  have hZZS : center H ≤ centerIn (S : Subgroup H) := by
    rw [← hZS]
    exact le_inf hZV (center_le_centralizer _)
  have hmul := relIndex_mul_relIndex (center H) (centerIn (S : Subgroup H)) V hZZS hZSV
  rw [hi, htop'] at hmul
  omega

end Glauberman
