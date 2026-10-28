module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.Words
public import Theory.SpecificGroups.ReeTwo.Recognition
public import Theory.SpecificGroups.ReeTwo.SylowCenter

/-!
# From the ambient root identities to the marked first parabolic

The last root is Parrott's r5, so the existing faithful-recognition criterion
makes the root-and-Weyl map injective. Its image lies in the actual first
parabolic, and the proved local orders give surjectivity. The same map
restricts to the chosen positive Sylow subgroup and the whole overlap.

All results retain the explicit finite `Ambient.Relations` premise. They are
assembly lemmas, not an unconditional identification of the ambient model.
No structural conclusion or cardinality-only identification is assumed.

Sources: Shinoda (1975), pp.81–83; Parrott (1972), p.683;
Aschbacher–Smith 14.2.21, printed p.989.
-/

@[expose] public section
noncomputable section
namespace ReeTwo.ParabolicMarkedComparison
open ReeF4
open Tits.ExceptionalParabolics

variable (h : Ambient.Relations)
include h

/-- The source's last root is the marked Atlas central involution. -/
theorem atlas_last_root : FullRee.atlasEmbedding Tits.atlas1600R5 = Ambient.root 9 := by
  have hc : Commute Ambient.rootOne (Ambient.root 2) := by
    have hr := h.root_one 2
    change rightComm Ambient.rootOne (Ambient.root 2) = 1 at hr
    have he : (Ambient.root 2 * Ambient.rootOne)⁻¹ *
        (Ambient.rootOne * Ambient.root 2) = 1 := by
      simpa only [rightComm, mul_inv_rev, mul_assoc] using hr
    exact (inv_mul_eq_one.mp he).symm
  have h4 : Ambient.rootOne ^ 4 = 1 := by
    simpa only [inv_pow, inv_eq_one] using h.four
  rw [Tits.atlas1600R5_eq, map_mul, map_pow, Ambient.atlas_generator,
    Ambient.atlas_generator]
  change Ambient.rootOne * Ambient.rootOne * (Ambient.rootOne * Ambient.root 2) ^ 2 =
    Ambient.root 2 ^ 2
  rw [hc.mul_pow]
  calc
    _ = Ambient.rootOne ^ 4 * Ambient.root 2 ^ 2 := by group
    _ = _ := by rw [h4, one_mul]

theorem last_root_ne_one : Ambient.root 9 ≠ 1 := by
  rw [← atlas_last_root h]
  intro he
  exact Tits.atlas1600R5_ne_one
    (FullRee.atlasEmbedding_injective (he.trans FullRee.atlasEmbedding.map_one.symm))

/-- The specified root-and-Weyl homomorphism into the ambient fixed matrices. -/
def localMap : Centralizer →* Model 0 :=
  Centralizer.lift h.core h.root_one h.weyl_root h.five h.four h.action

@[simp] theorem localMap_root (i : CoreRoot) :
    localMap h (Centralizer.root i) = Ambient.root i := Centralizer.lift_root ..

@[simp] theorem localMap_rootOne :
    localMap h Centralizer.rootOne = Ambient.rootOne := Centralizer.lift_rootOne ..

@[simp] theorem localMap_weyl :
    localMap h Centralizer.weyl = Ambient.weyl := Centralizer.lift_weyl ..

theorem localMap_injective : Function.Injective (localMap h) :=
  Centralizer.hom_injective_of_last_root _ (by simpa using last_root_ne_one h)

private theorem core_map_le_sylow : Centralizer.core.map (localMap h) ≤ FullRee.S :=
  Centralizer.lift_core_le h.core h.root_one h.weyl_root h.five h.four h.action
    FullRee.S Ambient.root_mem_sylow

private theorem localMap_mem_first (g : Centralizer) : localMap h g ∈ FullRee.first := by
  obtain ⟨v, i, j, rfl⟩ := Centralizer.normal_form g
  simp only [map_mul, map_pow, map_inv, localMap_rootOne, localMap_weyl]
  apply FullRee.first.mul_mem
  · apply FullRee.first.mul_mem
    · exact FullRee.sylow_le_first (core_map_le_sylow h ⟨_, ⟨_, rfl⟩, rfl⟩)
    · exact FullRee.first.pow_mem (FullRee.first.mul_mem
        (FullRee.first.pow_mem (FullRee.first.inv_mem
          (FullRee.sylow_le_first Ambient.rootOne_mem_sylow)) _)
        Ambient.weyl_mem_first) _
  · exact FullRee.first.pow_mem (FullRee.first.inv_mem
      (FullRee.sylow_le_first Ambient.rootOne_mem_sylow)) _

/-- Relation-based injectivity, followed by the proved first-parabolic order. -/
theorem localMap_range : (localMap h).range = FullRee.first := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, rfl⟩
    exact localMap_mem_first h g
  · rw [Nat.card_congr (MonoidHom.ofInjective (localMap_injective h)).toEquiv.symm,
      Centralizer.card, FullRee.first_card]

/-- The actual first-parabolic isomorphism with its specified ambient map. -/
def firstEquiv : Centralizer ≃* FullRee.first :=
  (MonoidHom.ofInjective (localMap_injective h)).trans
    (MulEquiv.subgroupCongr (localMap_range h))

@[simp] theorem firstEquiv_coe (g : Centralizer) :
    (firstEquiv h g : Model 0) = localMap h g := rfl

/-- The Sylow comparison is the restriction of the same root map. -/
def sylowMap : SylowModel →* Model 0 := (localMap h).comp SylowModel.embedding

@[simp] theorem sylowMap_root (i : CoreRoot) :
    sylowMap h (SylowModel.root i) = Ambient.root i := by simp [sylowMap]

@[simp] theorem sylowMap_rootOne :
    sylowMap h SylowModel.rootOne = Ambient.rootOne := by simp [sylowMap]

private theorem sylowMap_mem (g : SylowModel) : sylowMap h g ∈ FullRee.S := by
  have he : g = SemidirectProduct.inl g.left *
      (SylowModel.rootOne⁻¹) ^ g.right.toAdd.val := by
    rw [SylowModel.rootOne, ← map_inv, inv_inv, ← map_pow, FiveFour.generator_pow_val]
    exact (SemidirectProduct.inl_left_mul_inr_right g).symm
  rw [he, map_mul, map_pow, map_inv, sylowMap_rootOne]
  apply FullRee.S.mul_mem
  · exact core_map_le_sylow h ⟨_, ⟨g.left, by
      apply SemidirectProduct.ext
      · rfl
      · exact (map_one SylowModel.complementEmbedding).symm⟩, rfl⟩
  · exact FullRee.S.pow_mem (FullRee.S.inv_mem Ambient.rootOne_mem_sylow) _

theorem sylowMap_injective : Function.Injective (sylowMap h) :=
  (localMap_injective h).comp SylowModel.embedding_injective

theorem sylowMap_range : (sylowMap h).range = FullRee.S := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, rfl⟩
    exact sylowMap_mem h g
  · rw [Nat.card_congr (MonoidHom.ofInjective (sylowMap_injective h)).toEquiv.symm,
      SylowModel.card, FullRee.sylow_card]

def sylowEquiv : SylowModel ≃* FullRee.S :=
  (MonoidHom.ofInjective (sylowMap_injective h)).trans
    (MulEquiv.subgroupCongr (sylowMap_range h))

@[simp] theorem sylowEquiv_coe (g : SylowModel) :
    (sylowEquiv h g : Model 0) = sylowMap h g := rfl

/-- The Sylow and parabolic comparisons commute with their literal inclusions. -/
theorem sylow_first_commutes (g : SylowModel) :
    Subgroup.inclusion FullRee.sylow_le_first (sylowEquiv h g) =
      firstEquiv h (SylowModel.embedding g) := rfl

/-- The chosen Sylow image is also the whole marked overlap. -/
theorem sylowMap_range_overlap : (sylowMap h).range = FullRee.first ⊓ FullRee.second := by
  rw [sylowMap_range, FullRee.overlap_eq_borel, FullRee.borel_eq_sylow]

end ReeTwo.ParabolicMarkedComparison
