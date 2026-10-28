module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.Tits

/-!
# The source omega-center marking

The faithful Sylow comparison transports the proved two-element center of
`SylowModel` to the actual positive Ree subgroup. Thus source root 12
generates the literal Ω₁(Z(T)). The same root is the embedded Parrott r5;
the certified Atlas Sylow center gives the matching Tits statement.

The finite ambient root identities remain an explicit premise. These
results preserve the subgroup inclusions in the two ambient carriers.
Source: Shinoda (1975), (3.1), p.83; Parrott (1972), pp.672,683;
Aschbacher–Smith 14.2.21, printed p.989.
-/

@[expose] public section
noncomputable section
namespace ReeTwo.ParabolicMarkedComparison
open ReeF4 Tits.ExceptionalParabolics

private theorem omega_center_of_two_elements {G : Type*} [Group G]
    (P : Subgroup G) (z : P) (hz : z ∈ Subgroup.center P) (hz2 : z ^ 2 = 1)
    (hc : ∀ x : P, x ∈ Subgroup.center P → (x : G) = 1 ∨ (x : G) = z) :
    (omega₁ (Subgroup.center P) (p := 2)).map
      (P.subtype.comp (Subgroup.center P).subtype) = Subgroup.zpowers (z : G) := by
  apply le_antisymm
  · rintro _ ⟨x, _, rfl⟩
    rcases hc x.val x.property with he | he
    · change (x.val : G) ∈ Subgroup.zpowers (z : G)
      rw [he]
      exact Subgroup.one_mem _
    · change (x.val : G) ∈ Subgroup.zpowers (z : G)
      rw [he]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨⟨z, hz⟩, Subgroup.subset_closure ?_, rfl⟩
    change (⟨z, hz⟩ : Subgroup.center P) ^ (2 ^ 1) = 1
    exact Subtype.ext hz2

private theorem model_last_root_central :
    SylowModel.root 9 ∈ Subgroup.center SylowModel := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply SylowModel.embedding_injective
  simp only [map_mul, SylowModel.embedding_root]
  exact Subgroup.mem_center_iff.mp Centralizer.root_twelve_central _

variable (h : Ambient.Relations)
include h

/-- The full positive Sylow has precisely the identity and source root 12 in its center. -/
theorem sylow_center (g : FullRee.S) (hg : g ∈ Subgroup.center FullRee.S) :
    (g : Model 0) = 1 ∨ (g : Model 0) = Ambient.root 9 := by
  have hx : (sylowEquiv h).symm g ∈ Subgroup.center SylowModel :=
    (Subgroup.centerCongr (sylowEquiv h).symm ⟨g, hg⟩).property
  rcases SylowModel.eq_one_or_root_twelve_of_mem_center _ hx with he | he
  · left
    have he' := congrArg (sylowEquiv h) he
    simpa using congrArg Subtype.val he'
  · right
    have he' := congrArg (sylowEquiv h) he
    simpa using congrArg Subtype.val he'

theorem sylow_last_root_central :
    (⟨Ambient.root 9, Ambient.root_mem_sylow 9⟩ : FullRee.S) ∈
      Subgroup.center FullRee.S := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  obtain ⟨x, rfl⟩ := (sylowEquiv h).surjective g
  apply Subtype.ext
  simpa using congrArg (sylowMap h) (Subgroup.mem_center_iff.mp model_last_root_central x)

theorem last_root_square : Ambient.root 9 ^ 2 = 1 := by
  simpa only [pow_two, coreSquare, rootWord_nil] using h.core.square 9

/-- Literal ambient Ω₁(Z(T)) for the chosen full-Ree Sylow, with its root generator. -/
theorem sylow_omega_center :
    (omega₁ (Subgroup.center FullRee.S) (p := 2)).map
      (FullRee.S.subtype.comp (Subgroup.center FullRee.S).subtype) =
        Subgroup.zpowers (Ambient.root 9) :=
  omega_center_of_two_elements FullRee.S
    ⟨Ambient.root 9, Ambient.root_mem_sylow 9⟩ (sylow_last_root_central h)
    (Subtype.ext (last_root_square h)) (sylow_center h)

/-- In Atlas coordinates the same involution generates Ω₁ of the marked Sylow center. -/
theorem tits_sylow_omega_center :
    (omega₁ (Subgroup.center Tits.ExceptionalParabolics.S) (p := 2)).map
      (Tits.ExceptionalParabolics.S.subtype.comp
        (Subgroup.center Tits.ExceptionalParabolics.S).subtype) =
        Subgroup.zpowers Tits.atlas1600R5 := by
  apply omega_center_of_two_elements Tits.ExceptionalParabolics.S
    ⟨Tits.atlas1600R5, Tits.atlas1600R5_mem_sylowTwo⟩
    Tits.atlas1600R5_mem_center_sylowTwo
  · apply Subtype.ext
    apply FullRee.atlasEmbedding_injective
    change FullRee.atlasEmbedding (Tits.atlas1600R5 ^ 2) = FullRee.atlasEmbedding 1
    simpa only [map_pow, map_one, atlas_last_root h] using last_root_square h
  · intro x hx
    exact (Tits.atlas1600SylowTwo_mem_center_iff x).mp hx

/-- The two source omega-center markings agree under the fixed Atlas embedding. -/
theorem tits_sylow_omega_center_image :
    ((omega₁ (Subgroup.center Tits.ExceptionalParabolics.S) (p := 2)).map
      (Tits.ExceptionalParabolics.S.subtype.comp
        (Subgroup.center Tits.ExceptionalParabolics.S).subtype)).map FullRee.atlasEmbedding =
        Subgroup.zpowers (Ambient.root 9) := by
  rw [tits_sylow_omega_center h, MonoidHom.map_zpowers, atlas_last_root h]

end ReeTwo.ParabolicMarkedComparison
