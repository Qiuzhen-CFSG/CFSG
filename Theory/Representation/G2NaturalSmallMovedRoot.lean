module
public import Theory.Representation.G2NaturalLongRootFixer
public import Theory.Representation.G2NaturalOffenders.SmallMoved
public import Theory.Representation.G2OrthogonalCover.Universal
public import Theory.AtlasPort.LinearGroups.G2.Perfectness
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.G2NaturalNormalizerOffenders

/-!
# Small-moved elementary subgroups in natural G₂(4)

Self-duality identifies moved dimension with fixed codimension. A nontrivial
involution is a root element; the short root is excluded by its displacement.
The long root attains the whole allowed codimension, so its fixed space equals
the subgroup's fixed space. The literal pointwise-fixer theorem places the
subgroup in that same conjugate highest-root group, of order four.

Source: Aschbacher–Smith 11.4.1(2), p.776, using B.4.6(4),(13), pp.88–90.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Atlas.G2.NaturalSmallMovedRoot
attribute [local instance] ZMod.algebra
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem fixedCodim_eq_moved (hF : Nat.card F = 4)
    (C : Subgroup (Atlas.G2.Model F)) :
    fixedCodim (Atlas.G2.Natural.Normalizer.binary F) C =
      Module.finrank (ZMod 2)
        (subspaceCommutator (Atlas.G2.Natural.Normalizer.binary F) ⊤ C) := by
  let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect (by omega)
  let E := Atlas.G2.Natural.OrthogonalCover.binarySelfDual F
  have hall (g : Atlas.G2.Model F) : g ∈ commutator (Atlas.G2.Model F) := by
    rw [Group.IsPerfect.commutator_eq_top]
    trivial
  have he : ∀ g v,
      E (Atlas.G2.Natural.Normalizer.binary F g v) =
        (Atlas.G2.Natural.Normalizer.binary F).dual g (E v) := by
    intro g v
    have hg : Atlas.G2.Natural.Normalizer.binary F g =
        Atlas.G2.Natural.OrthogonalCover.binaryNatural F ⟨g, hall g⟩ := by
      rw [Atlas.G2.Natural.Normalizer.binary_apply]
      rfl
    have hgi : Atlas.G2.Natural.Normalizer.binary F g⁻¹ =
        Atlas.G2.Natural.OrthogonalCover.binaryNatural F ⟨g⁻¹, hall g⁻¹⟩ := by
      rw [Atlas.G2.Natural.Normalizer.binary_apply]
      rfl
    rw [hg, Representation.dual_apply, hgi]
    exact Atlas.G2.Natural.OrthogonalCover.binarySelfDual_equivariant F ⟨g, hall g⟩ v
  have hd := fixedCodim_map_equivariant
    (Atlas.G2.Natural.Normalizer.binary F)
    (Atlas.G2.Natural.Normalizer.binary F).dual
    (MonoidHom.id _) E he C
  calc
    fixedCodim (Atlas.G2.Natural.Normalizer.binary F) C =
        fixedCodim (Atlas.G2.Natural.Normalizer.binary F).dual C := by
          simpa only [Subgroup.map_id] using hd
    _ = Module.finrank (ZMod 2)
        (subspaceCommutator (Atlas.G2.Natural.Normalizer.binary F) ⊤ C) :=
      fixedCodim_dual_eq_moved_finrank _ _


omit [Finite F] in
private theorem normalizer_binary_eq : Natural.Normalizer.binary F =
    NaturalOffenders.binaryNatural (F := F) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  rw [Natural.Normalizer.binary_apply]
  rfl

private theorem codim_mono {A B : Subgroup (Model F)} (hAB : A ≤ B) :
    fixedCodim (NaturalOffenders.binaryNatural (F := F)) A ≤
      fixedCodim (NaturalOffenders.binaryNatural (F := F)) B := by
  have hf : fixedSpace (NaturalOffenders.binaryNatural (F := F)) B ≤
      fixedSpace (NaturalOffenders.binaryNatural (F := F)) A := by
    intro v hv a
    exact hv ⟨a,hAB a.property⟩
  have hd := Submodule.finrank_mono hf
  have ha := fixedCodim_add_finrank (NaturalOffenders.binaryNatural (F := F)) A
  have hb := fixedCodim_add_finrank (NaturalOffenders.binaryNatural (F := F)) B
  omega

/-- Every elementary subgroup moving at most four binary dimensions lies
in one actual conjugate of the highest-root group. -/
theorem exists_le_highestRoot (hF : Nat.card F = 4)
    (C : Subgroup (Model F)) [IsElementaryAbelian 2 C]
    (hCm : Module.finrank (ZMod 2)
      (subspaceCommutator (Natural.Normalizer.binary F) ⊤ C) ≤ 4) :
    ∃ g : Model F, C ≤ LieParabolicSetup.highestRoot.map (MulAut.conj g).toMonoidHom := by
  classical
  have hc : Nat.card F = 2 ^ 2 := by simpa using hF
  have hfixed : fixedCodim (NaturalOffenders.binaryNatural (F := F)) C ≤ 4 := by
    rw [← normalizer_binary_eq, fixedCodim_eq_moved hF]
    exact hCm
  rcases C.bot_or_exists_ne_one with hbot | ⟨a,ha,hne⟩
  · exact ⟨1, hbot ▸ bot_le⟩
  have hmono := codim_mono (zpowers_le.mpr ha)
  have hroot := EvenInvolutionGeometry.involution_isRoot
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  rcases hroot with ⟨g,r,hr,he⟩ | ⟨g,r,hr,he⟩
  · have hlong : fixedCodim (NaturalOffenders.binaryNatural (F := F)) (zpowers a) = 4 := by
      rw [NaturalOffenders.natural_fixedCodim_eq]
      exact NaturalOffenders.fixedCodim_longRoot hc ⟨r,hr,g,he⟩
    have hle : fixedSpace (NaturalOffenders.binaryNatural (F := F)) C ≤
        fixedSpace (NaturalOffenders.binaryNatural (F := F)) (zpowers a) := by
      intro v hv b
      exact hv ⟨b, (zpowers_le.mpr ha) b.property⟩
    have hf := fixedCodim_add_finrank (NaturalOffenders.binaryNatural (F := F)) C
    have hfa := fixedCodim_add_finrank (NaturalOffenders.binaryNatural (F := F)) (zpowers a)
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
    refine ⟨g, ?_⟩
    rw [← NaturalLongRootFixer.subspaceKernel_fixedSpace_longRoot g r hr, ← he, ← heq]
    intro b hb
    exact ⟨mem_top _, fun v hv => hv ⟨b,hb⟩⟩
  · have hshort : fixedCodim (NaturalOffenders.binaryNatural (F := F)) (zpowers a) = 6 := by
      rw [he, NaturalOffenders.natural_fixedCodim_eq]
      change fixedCodim (NaturalOffenders.binaryAction (F := F))
        (zpowers ((MulAut.conj g).toMonoidHom (rootC r))) = _
      rw [← MonoidHom.map_zpowers, fixedCodim_map_conj]
      exact NaturalOffenders.fixedCodim_rootC hc r hr
    omega

/-- The actual highest-root group has order four, giving the sharp bound. -/
theorem card_le_four (hF : Nat.card F = 4)
    (C : Subgroup (Model F)) [IsElementaryAbelian 2 C]
    (hCm : Module.finrank (ZMod 2)
      (subspaceCommutator (Natural.Normalizer.binary F) ⊤ C) ≤ 4) : Nat.card C ≤ 4 := by
  obtain ⟨g,hg⟩ := exists_le_highestRoot hF C hCm
  have h := Subgroup.card_le_of_le hg
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    LieParabolicSetup.card_highestRoot, hF] at h

/-- Binary rank at most two for the same literal small-moved actor. -/
theorem rank_le_two (hF : Nat.card F = 4)
    (C : Subgroup (Model F)) [IsElementaryAbelian 2 C]
    (hCm : Module.finrank (ZMod 2)
      (subspaceCommutator (Natural.Normalizer.binary F) ⊤ C) ≤ 4) : rank C ≤ 2 := by
  have h := Nat.log_mono_right (b := 2) (card_le_four hF C hCm)
  exact h

end Atlas.G2.NaturalSmallMovedRoot
