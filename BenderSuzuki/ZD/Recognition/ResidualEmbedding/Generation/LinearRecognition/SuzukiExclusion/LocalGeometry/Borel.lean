module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.GeometryContract
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry

/-!
# The marked Borel two-core in the Suzuki exclusion

The proper-residual Borel identification transports the root group, its
elementary center and its square-one elements through one and the same
embedding. Thus the subgroup `P` in (14B) is the literal two-core of `M ∩ L`,
and `A = ⟨Z ∩ M⟩` is its embedded center. Its order is q², with the actual
Suzuki field order q = 2^(2*m+1).

Source: GLS4, Chapter 2, (14B), using Lemma 12.2 and Chapter 4, Lemma 3.2(b,c).
The normalizer Sylow construction remains separate from these model facts.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup BenderSuzuki.MatrixGroups

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

/-- One actual matrix-model marking identifies the Borel, its full two-core,
and its elementary center in the original ambient group. -/
public theorem Context.borel_marking :
    ∃ f : SuzukiMatrixGroup m ≃* residualGenerated M z t,
      let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
      (SuzukiBorelSubgroup m).map φ = M ⊓ residualGenerated M z t ∧
      (SuzukiRootSubgroup m).map φ = borelTwoCore M z t ∧
      (omegaOneAmbient (SuzukiRootSubgroup m)).map φ = closure (Z ∩ (M : Set G)) := by
  have hm : 0 < m := d.parameter_pos
  obtain ⟨f, hf⟩ := residualGenerated_suzuki_borel_marking d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper hm d.model
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  have hi : Function.Injective φ := Subtype.val_injective.comp f.injective
  have hAL := proper_residualGenerated_contains_distinguishedClosure d.minimal
    d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  refine ⟨f, hf, (suzukiBorel_pCore_map hm φ hi _ hf).symm, ?_⟩
  rw [← suzukiBorel_involutionCore_map hm φ hi _ hf]
  exact (distinguishedClosure_eq_involutionCore_local d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper hAL)

/-- The source Borel two-core is the ambient image of a Sylow subgroup of L. -/
public theorem Context.borelTwoCore_sylow :
    ∃ V : Sylow 2 (residualGenerated M z t),
      (V : Subgroup (residualGenerated M z t)).map (residualGenerated M z t).subtype =
        borelTwoCore M z t := by
  obtain ⟨f, _, hP, _⟩ := d.borel_marking
  obtain ⟨V, hV⟩ := suzukiRootSubgroup_isSylow m d.parameter_pos
  refine ⟨V.mapSurjective (f := f.toMonoidHom) f.surjective, ?_⟩
  change ((V : Subgroup (SuzukiMatrixGroup m)).map f.toMonoidHom).map _ = _
  rw [hV, map_map]
  exact hP

/-- The full Borel two-core has order q². -/
public theorem Context.borelTwoCore_card :
    Nat.card (borelTwoCore M z t) = (2 ^ (2 * m + 1)) ^ 2 := by
  obtain ⟨f, _, hP, _⟩ := d.borel_marking
  rw [← hP, card_map_of_injective (Subtype.val_injective.comp f.injective),
    suzukiRootSubgroup_card m d.parameter_pos]

/-- The embedded center of the actual Borel two-core is the distinguished closure. -/
public theorem Context.borelTwoCore_center :
    (center (borelTwoCore M z t)).map (borelTwoCore M z t).subtype =
      closure (Z ∩ (M : Set G)) := by
  obtain ⟨f, _, hP, hA⟩ := d.borel_marking
  rw [suzukiRootSubgroup_omega_eq_center m d.parameter_pos,
    map_embeddedCenter _ _ (Subtype.val_injective.comp f.injective), hP] at hA
  exact hA

/-- The square-one elements of P, including the identity, are exactly A. -/
public theorem Context.borelTwoCore_square_one :
    {x : G | x ∈ borelTwoCore M z t ∧ x ^ 2 = 1} =
      (closure (Z ∩ (M : Set G)) : Set G) := by
  obtain ⟨f, _, hP, hA⟩ := d.borel_marking
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  have hi : Function.Injective φ := Subtype.val_injective.comp f.injective
  rw [suzukiRootSubgroup_omega_eq_center m d.parameter_pos] at hA
  rw [← hP, ← hA]
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hs⟩
    have hy2 : (⟨y, hy⟩ : SuzukiRootSubgroup m) ^ 2 = 1 := by
      apply Subtype.ext
      apply hi
      change φ (y ^ 2) = φ 1
      simpa only [map_pow, map_one] using hs
    exact ⟨y, ⟨⟨y, hy⟩,
      (suzukiRootSubgroup_square_iff_center m d.parameter_pos _).mp hy2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨mem_map_of_mem φ y.property, ?_⟩
    have hy2 := (suzukiRootSubgroup_square_iff_center m d.parameter_pos y).mpr hy
    exact (map_pow φ (y : SuzukiMatrixGroup m) 2).symm.trans
      ((congrArg φ (congrArg Subtype.val hy2)).trans φ.map_one)

end BenderSuzuki.ZD.SuzukiExclusion
