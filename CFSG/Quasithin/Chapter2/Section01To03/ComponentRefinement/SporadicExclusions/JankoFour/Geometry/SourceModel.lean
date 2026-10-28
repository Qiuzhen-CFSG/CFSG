module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Contracts
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowGeometry

/-!
# The supplied component action on the actual Janko four quotient

The map to the matrix model has kernel exactly O₂(L). This kernel is central
by quasisimplicity; perfectness makes the induced automorphism map faithful.
The chosen component Sylow is precisely L ∩ S, and its quotient image is fixed
pointwise by the given involution action.

The intrinsic Sylow geometry theorem therefore supplies a genuine max1 conjugate
which is invariant under all automorphisms preserving that image and generates
the model with the fixed subgroup of the actual action. This is the model part
of the local cover; lifting fixed points and the Mathieu layer of the entire
component orbit are separate obligations. No trivial-center hypothesis is used.

Source: Aschbacher--Smith, 1.1.5(3)(f) and 2.3.9(7), printed pp.502 and 526;
GLS3, Table 5.3i. The central-quotient transport follows the same argument as
`SporadicExclusions.Held.LocalGeometry.Transport`, with the actual Janko carrier.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem twoCore_le_center (h : LocalSetup H L M S z) : pCore 2 L ≤ center L := by
  let := h.finite
  let := h.quasisimple
  exact IsQuasisimple.pCore_le_center 2

/-- The specified quotient, followed by its actual Janko model isomorphism. -/
def modelMap (d : SporadicQuotientInput L z .j4) : L →* Janko4.Model :=
  d.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem modelMap_surjective (d : SporadicQuotientInput L z .j4) :
    Function.Surjective (modelMap d) :=
  d.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

/-- No central two-kernel is discarded by the model map. -/
theorem modelMap_ker (d : SporadicQuotientInput L z .j4) :
    (modelMap d).ker = pCore 2 L := by
  ext x
  change d.quotientIso (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ _
  rw [map_eq_one_iff _ d.quotientIso.injective]
  exact QuotientGroup.eq_one_iff x

/-- The genuine automorphism action on the characteristic two-core quotient. -/
def modelAut (d : SporadicQuotientInput L z .j4) : MulAut L →* MulAut Janko4.Model :=
  (MulAut.congr d.quotientIso).toMonoidHom.comp (quotientAut (pCore 2 L))

theorem modelAut_apply (d : SporadicQuotientInput L z .j4) (a : MulAut L) (x : L) :
    modelAut d a (modelMap d x) = modelMap d (a x) := by
  change d.quotientIso (quotientAut (pCore 2 L) a
    (d.quotientIso.symm (d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)))) = _
  rw [d.quotientIso.symm_apply_apply, quotientAut_apply_mk]
  rfl

/-- Perfectness detects an automorphism from its action modulo the central two-kernel. -/
theorem modelAut_injective (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) : Function.Injective (modelAut d) := by
  let : IsQuasisimple L := h.quasisimple
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro a ha
  apply MulAut.eq_one_of_central_displacement a
  intro x
  apply twoCore_le_center h
  rw [← modelMap_ker d]
  change modelMap d (x⁻¹ * a x) = 1
  rw [map_mul, map_inv, ← modelAut_apply]
  change modelAut d a = 1 at ha
  rw [ha, MulAut.one_apply, inv_mul_cancel]

theorem modelAut_conj (d : SporadicQuotientInput L z .j4) (x : L) :
    modelAut d (MulAut.conj x) = MulAut.conj (modelMap d x) := by
  ext y
  obtain ⟨y, rfl⟩ := modelMap_surjective d y
  rw [modelAut_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem modelAction_order (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) : orderOf (modelAut d d.action) = 2 := by
  rw [orderOf_injective (modelAut d) (modelAut_injective h d)]
  exact h.action_order d.action d.conjugation

theorem modelAction_inner (d : SporadicQuotientInput L z .j4) :
    modelAut d d.action ∈ (MulAut.conj (G := Janko4.Model)).range := by
  obtain ⟨x, hx⟩ := d.inner
  exact ⟨modelMap d x, by rw [← hx, modelAut_conj]⟩

/-- The restricted Sylow subgroup; its underlying subgroup is uniquely determined by `componentSylow_map`. -/
def componentSylow (h : LocalSetup H L M S z) : Sylow 2 L :=
  h.exists_component_sylow.choose

theorem componentSylow_map (h : LocalSetup H L M S z) :
    (componentSylow h : Subgroup L).map L.subtype =
      L ⊓ (S : Subgroup H).map H.subtype := h.exists_component_sylow.choose_spec

/-- Membership is the actual intersection with the supplied S, independent of the existential presentation. -/
theorem mem_componentSylow (h : LocalSetup H L M S z) (x : L) :
    x ∈ (componentSylow h : Subgroup L) ↔
      (x : G) ∈ (S : Subgroup H).map H.subtype := by
  rw [← mem_map_iff_mem L.subtype_injective, componentSylow_map h]
  exact and_iff_right x.property

theorem componentSylow_fixed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) (x : L)
    (hx : x ∈ (componentSylow h : Subgroup L)) : d.action x = x := by
  apply Subtype.ext
  rw [d.conjugation, ← h.central (x : G) ((mem_componentSylow h x).mp hx),
    mul_inv_cancel_right]

/-- The image of the actual component Sylow subgroup under the specified quotient. -/
def modelSylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) : Sylow 2 Janko4.Model := by
  let := h.finite
  exact (componentSylow h).mapSurjective (modelMap_surjective d)

theorem modelSylow_coe (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) :
    (modelSylow h d : Subgroup Janko4.Model) = (componentSylow h).map (modelMap d) := rfl

theorem modelSylow_preimage (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) :
    (modelSylow h d : Subgroup Janko4.Model).comap (modelMap d) = componentSylow h := by
  rw [modelSylow_coe, comap_map_eq_self]
  rw [modelMap_ker]
  exact pCore_isPGroup.le_sylow_of_normal _

theorem modelSylow_fixed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) (x : Janko4.Model)
    (hx : x ∈ (modelSylow h d : Subgroup Janko4.Model)) : modelAut d d.action x = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [modelAut_apply, componentSylow_fixed h d y hy]


/-- An actual max1 conjugate adapted to the supplied Sylow and involution action.
Its invariance applies to the entire automorphism stabilizer of that Sylow. -/
theorem exists_source_model_seed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) :
    ∃ P : Subgroup Janko4.Model,
      (modelSylow h d : Subgroup Janko4.Model) ≤ P ∧
      Nonempty (P ≃* Janko4.Cardinality.max1Subgroup
        Janko4.matrixA_mul_self Janko4.matrixB_pow_four) ∧
      (∀ a : MulAut Janko4.Model,
        (modelSylow h d : Subgroup Janko4.Model).map a.toMonoidHom = modelSylow h d →
          P.map a.toMonoidHom = P) ∧
      (modelAut d d.action).fixedSubgroup ⊔ P = ⊤ := by
  obtain ⟨P, hP, he, hi, hg⟩ :=
    Janko4.LocalStructure.exists_sylow_mathieu_seed (modelSylow h d)
  refine ⟨P, hP, he, hi, ?_⟩
  obtain ⟨u, hu⟩ := d.inner
  have ha : modelAut d d.action = MulAut.conj (modelMap d u) := by
    rw [← hu, modelAut_conj]
  have hne : modelMap d u ≠ 1 := by
    intro hh
    apply h.action_ne_one d.action d.conjugation
    apply modelAut_injective h d
    rw [ha, hh, map_one, map_one]
  have hc : modelMap d u ∈ centralizer (modelSylow h d : Set Janko4.Model) := by
    intro r hr
    have hh := modelSylow_fixed h d r hr
    rw [ha] at hh
    change modelMap d u * r * (modelMap d u)⁻¹ = r at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [ha, MulAut.fixedSubgroup_conj]
  exact hg (modelMap d u) hne hc

end CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

end
