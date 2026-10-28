module
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Uniform character multiplicities in the ternary octonion algebra

Every elementary two-subgroup of the actual octonion automorphism group has
all of its sign characters in the defining representation, with equal positive
multiplicity. Consequently its order times each character-space dimension is
eight. This gives the elementary rank bound and the dimensions four, two and
one for subgroups of orders two, four and eight, without using conjugacy.

Each involution splits into its two eigenspaces. Simultaneous decomposition
then follows from commutativity. The norm and multiplication make the occurring
characters a subgroup, and right multiplication identifies their spaces.
Faithfulness and finite character duality force that subgroup to be the full
dual. Independence turns the decomposition into the dimension identity.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4, and Volume II pp.481–482. This module does
not assert elementary-subgroup conjugacy or maximal-two-local coverage.
The octonion conventions come from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
namespace Atlas.G2.TernaryLocals.CharacterGeometry
open Atlas.SplitOctonion
open scoped IsMulCommutative

/-- The actual restricted octonion action, as linear endomorphisms. -/
def action (E : Subgroup G) : E →* Module.End (ZMod 3) V where
  toFun g := g.val.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem action_sq (E : Subgroup G) [IsElementaryAbelian 2 E] (g : E) :
    action E g ^ 2 = 1 := by
  rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) g, map_one]

private theorem action_semisimple (E : Subgroup G) [IsElementaryAbelian 2 E] (g : E) :
    (action E g).IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X : Polynomial (ZMod 3)) ^ 2 - 1)
  · exact (Polynomial.X_pow_sub_one_separable_iff.mpr (by decide : (2 : ZMod 3) ≠ 0)).squarefree
  · simp [action_sq E g]

private theorem involution_eigenspaces (f : Module.End (ZMod 3) V) (hf : f^2 = 1) :
    (⨆ r : ZMod 3, f.eigenspace r) = ⊤ := by
  apply top_unique
  intro x _
  have hff : f (f x) = x := by
    simpa only [pow_two, Module.End.mul_apply, Module.End.one_apply] using
      LinearMap.congr_fun hf x
  have hplus : -(x + f x) ∈ f.eigenspace 1 := by
    rw [Module.End.mem_eigenspace_iff]
    simp only [map_neg, map_add, hff, one_smul]
    congr 1
    exact add_comm _ _
  have hminus : -(x - f x) ∈ f.eigenspace (-1) := by
    rw [Module.End.mem_eigenspace_iff]
    simp only [map_neg, map_sub, hff, neg_one_smul]
    abel
  have hs := (⨆ r : ZMod 3, f.eigenspace r).add_mem
    ((le_iSup (fun r => f.eigenspace r) 1) hplus)
    ((le_iSup (fun r => f.eigenspace r) (-1)) hminus)
  have he : -(x + f x) + -(x - f x) = x := by
    have hthree : (3 : ZMod 3) = 0 := rfl
    calc
      _ = x - (3 : ZMod 3) • x := by module
      _ = x := by rw [hthree, zero_smul, sub_zero]
  rwa [he] at hs

private theorem weight_character (E : Subgroup G) (w : E → ZMod 3)
    (hw : (⨅ g, (action E g).eigenspace (w g)) ≠ ⊥) :
    ∃ χ : Character E, ∀ g, (χ g : ZMod 3) = w g := by
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  have he : ∀ g, action E g v = w g • v := by
    simpa only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] using hv
  have h1 : w 1 = 1 := by
    apply smul_left_injective (ZMod 3) hn
    simpa using (he 1).symm
  have hm : ∀ a b, w (a*b) = w a * w b := by
    intro a b
    apply smul_left_injective (ZMod 3) hn
    change w (a*b) • v = (w a * w b) • v
    rw [← he (a*b), map_mul, Module.End.mul_apply, he b, map_smul, he a,
      smul_smul, mul_comm]
  have h0 : ∀ a, w a ≠ 0 := by
    intro a ha
    have h := hm a a⁻¹
    rw [mul_inv_cancel, h1, ha, zero_mul] at h
    exact one_ne_zero h
  exact ⟨{ toFun := fun g => Units.mk0 (w g) (h0 g)
           map_one' := Units.ext h1
           map_mul' := fun a b => Units.ext (hm a b) }, fun _ => rfl⟩

private theorem characterSpace_eq_iInf (E : Subgroup G) (χ : Character E) :
    characterSpace E χ = ⨅ g, (action E g).eigenspace (χ g : ZMod 3) := by
  ext v
  simp only [mem_characterSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  rfl

/-- Elementary two-groups split the octonions into simultaneous sign spaces. -/
theorem iSup_characterSpace_eq_top (E : Subgroup G) [IsElementaryAbelian 2 E] :
    (⨆ χ : Character E, characterSpace E χ) = ⊤ := by
  have hcomm : ∀ a b, Commute (action E a) (action E b) := by
    intro a b
    change action E a * action E b = action E b * action E a
    simp [← map_mul, mul_comm]
  have heq : ∀ g r, (action E g).maxGenEigenspace r = (action E g).eigenspace r :=
    fun g r => (action_semisimple E g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace r
  have htop : (⨆ w : E → ZMod 3, ⨅ g, (action E g).eigenspace (w g)) = ⊤ := by
    have hs : ∀ g, (⨆ r, (action E g).maxGenEigenspace r) = ⊤ := by
      intro g
      simpa only [heq] using involution_eigenspaces (action E g) (action_sq E g)
    simpa only [heq] using
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        (action E) (fun a b _ => hcomm a b) hs
  apply top_unique
  rw [← htop]
  refine iSup_le fun w => ?_
  by_cases hw : (⨅ g, (action E g).eigenspace (w g)) = ⊥
  · simp [hw]
  obtain ⟨χ, hχ⟩ := weight_character E w hw
  have he : (⨅ g, (action E g).eigenspace (w g)) = characterSpace E χ := by
    rw [characterSpace_eq_iInf]
    simp only [hχ]
  rw [he]
  exact le_iSup (characterSpace E) χ

/-- Independence of the different simultaneous sign spaces. -/
theorem characterSpace_independent (E : Subgroup G) [IsElementaryAbelian 2 E] :
    iSupIndep (characterSpace E) := by
  have hcomm : ∀ a b, Commute (action E a) (action E b) := by
    intro a b
    change action E a * action E b = action E b * action E a
    simp [← map_mul, mul_comm]
  have hm : ∀ a b r, Set.MapsTo (action E a)
      ((action E b).maxGenEigenspace r) ((action E b).maxGenEigenspace r) :=
    fun a b r => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) r
  have heq : ∀ g r, (action E g).maxGenEigenspace r = (action E g).eigenspace r :=
    fun g r => (action_semisimple E g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace r
  have hi : iSupIndep (fun w : E → ZMod 3 => ⨅ g, (action E g).eigenspace (w g)) := by
    simpa only [heq] using
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (action E) hm
  have hi' := hi.comp (f := fun χ : Character E => fun g => (χ g : ZMod 3))
    (show Function.Injective (fun χ : Character E => fun g => (χ g : ZMod 3)) from
      fun a b h => MonoidHom.ext fun g => Units.ext (congr_fun h g))
  convert hi' using 1
  funext χ
  exact characterSpace_eq_iInf E χ

private instance enoughTwoRoots : HasEnoughRootsOfUnity (ZMod 3) 2 where
  prim := ⟨-1, IsPrimitiveRoot.neg_one 3 (by decide)⟩
  cyc := rootsOfUnity.isCyclic (ZMod 3) 2

private theorem character_exponent_dvd (E : Subgroup G) :
    Monoid.exponent (Character E) ∣ 2 := by
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro χ
  rw [pow_two, character_mul_self χ]

/-- The characters appearing in the octonion action form a subgroup. -/
def occurring (E : Subgroup G) [IsElementaryAbelian 2 E] : Subgroup (Character E) where
  carrier := {χ | characterSpace E χ ≠ ⊥}
  one_mem' := by
    intro h
    have hm := unit_mem E
    rw [h, Submodule.mem_bot] at hm
    exact unit_ne_zero hm
  mul_mem' := mul_ne_bot_of_span E (iSup_characterSpace_eq_top E)
  inv_mem' := by
    intro χ hχ
    have hi : χ⁻¹ = χ := inv_eq_of_mul_eq_one_left (character_mul_self χ)
    rwa [hi]

private def evaluation (E : Subgroup G) [IsElementaryAbelian 2 E] :
    E →* (occurring E →* (ZMod 3)ˣ) where
  toFun g := {
    toFun := fun χ => χ.val g
    map_one' := rfl
    map_mul' _ _ := rfl }
  map_one' := by ext χ; exact congrArg Units.val (χ.val.map_one)
  map_mul' a b := by ext χ; exact congrArg Units.val (χ.val.map_mul a b)

private theorem evaluation_injective (E : Subgroup G) [IsElementaryAbelian 2 E] :
    Function.Injective (evaluation E) := by
  intro a b hab
  apply mul_inv_eq_one.mp
  apply eq_one_of_characters E (iSup_characterSpace_eq_top E)
  intro χ hχ
  have he : χ a = χ b := congrArg (fun f : occurring E →* (ZMod 3)ˣ => f ⟨χ,hχ⟩) hab
  rw [map_mul, map_inv, he, mul_inv_cancel]

/-- Every sign character occurs, since the occurring subgroup separates E. -/
theorem characterSpace_ne_bot (E : Subgroup G) [IsElementaryAbelian 2 E]
    (χ : Character E) : characterSpace E χ ≠ ⊥ := by
  let : HasEnoughRootsOfUnity (ZMod 3) (Monoid.exponent E) :=
    HasEnoughRootsOfUnity.of_dvd (ZMod 3) (IsElementaryAbelian.exponent_dvd_p 2 E)
  let : HasEnoughRootsOfUnity (ZMod 3) (Monoid.exponent (occurring E)) :=
    HasEnoughRootsOfUnity.of_dvd (ZMod 3)
      ((Monoid.exponent_submonoid_dvd (occurring E).toSubmonoid).trans (character_exponent_dvd E))
  have hle := Nat.card_le_card_of_injective (evaluation E) (evaluation_injective E)
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (occurring E) (ZMod 3)] at hle
  have hc := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity E (ZMod 3)
  have ht : occurring E = ⊤ :=
    (occurring E).eq_top_of_card_eq (le_antisymm (occurring E).card_le_card_group (hc.trans_le hle))
  have hm : χ ∈ occurring E := by rw [ht]; trivial
  exact hm

/-- Every character space contains a vector of nonzero norm. -/
theorem exists_nonisotropic (E : Subgroup G) [IsElementaryAbelian 2 E]
    (χ : Character E) : ∃ v ∈ characterSpace E χ, norm v ≠ 0 :=
  exists_nonisotropic_of_span E (iSup_characterSpace_eq_top E) χ (characterSpace_ne_bot E χ)

/-- The spaces for all characters have the same positive dimension. -/
theorem finrank_eq_identity (E : Subgroup G) [IsElementaryAbelian 2 E]
    (χ : Character E) :
    Module.finrank (ZMod 3) (characterSpace E χ) =
      Module.finrank (ZMod 3) (characterSpace E 1) :=
  finrank_eq_identity_of_span E (iSup_characterSpace_eq_top E) χ (characterSpace_ne_bot E χ)

/-- The regular character multiplicity identity for the actual octonion action. -/
theorem card_mul_finrank (E : Subgroup G) [IsElementaryAbelian 2 E] (χ : Character E) :
    Nat.card E * Module.finrank (ZMod 3) (characterSpace E χ) = 8 := by
  classical
  let := Fintype.ofFinite (Character E)
  let : HasEnoughRootsOfUnity (ZMod 3) (Monoid.exponent E) :=
    HasEnoughRootsOfUnity.of_dvd (ZMod 3) (IsElementaryAbelian.exponent_dvd_p 2 E)
  have hi : DirectSum.IsInternal (characterSpace E) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (characterSpace_independent E) (iSup_characterSpace_eq_top E)
  have hs : (∑ ψ : Character E, Module.finrank (ZMod 3) (characterSpace E ψ)) = 8 := by
    rw [← Module.finrank_directSum]
    exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap (characterSpace E)) hi).finrank_eq.trans
      (carrier_finrank (ZMod 3))
  have hc := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity E (ZMod 3)
  simp_rw [finrank_eq_identity E] at hs
  rw [finrank_eq_identity E χ]
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, hc] using hs

/-- Every elementary two-subgroup of G₂(3) has order dividing eight. -/
theorem elementary_card_dvd_eight (E : Subgroup G) [IsElementaryAbelian 2 E] :
    Nat.card E ∣ 8 :=
  ⟨Module.finrank (ZMod 3) (characterSpace E 1), (card_mul_finrank E 1).symm⟩

/-- A four-group has four character planes. -/
theorem finrank_of_card_four (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (χ : Character E) :
    Module.finrank (ZMod 3) (characterSpace E χ) = 2 := by
  have h := card_mul_finrank E χ
  rw [hE] at h
  omega

/-- An elementary eight has eight character lines. -/
theorem finrank_of_card_eight (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (χ : Character E) :
    Module.finrank (ZMod 3) (characterSpace E χ) = 1 := by
  have h := card_mul_finrank E χ
  rw [hE] at h
  omega

/-- Both sign spaces of an involution have dimension four. -/
theorem finrank_of_card_two (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 2) (χ : Character E) :
    Module.finrank (ZMod 3) (characterSpace E χ) = 4 := by
  have h := card_mul_finrank E χ
  rw [hE] at h
  omega

end Atlas.G2.TernaryLocals.CharacterGeometry
