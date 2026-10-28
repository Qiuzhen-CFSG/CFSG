module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Transport

/-!
# Actual summands and transported lines in a doubled action

Starting from an equivariant identification with two copies, the coordinate
embeddings and projections are defined on the original module. They
intertwine the same actor, have complementary ranges, and reconstruct every
vector. A model line gives a distinct line in each range, with exactly the
same original parabolic stabilizer. Irr+ transports through these actual
embeddings, including its central quotient.

This does not assert that the original V₂ lies in both disjoint ranges.
Choosing the model line from V₂ is the separate binary geometry obligation.
The constructions apply in particular to the doubled natural SL₃(2) case.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
B.5.1(1ii), p.99, and proof of 15.3.31, p.1132 (PDF p.1149).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D A V W : Type*} [Group D] [Group A]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) A W}

noncomputable def copyEmbedding (e : ActionEquiv ρ (repeated σ 2)) (i : Fin 2) : W →ₗ[ZMod 2] V :=
  e.linearEquiv.symm.toLinearMap.comp (LinearMap.single (ZMod 2) (fun _ : Fin 2 => W) i)

noncomputable def copyProjection (e : ActionEquiv ρ (repeated σ 2)) (i : Fin 2) : V →ₗ[ZMod 2] W :=
  (LinearMap.proj i).comp e.linearEquiv.toLinearMap

theorem copyProjection_copyEmbedding (e : ActionEquiv ρ (repeated σ 2))
    (i : Fin 2) (w : W) : copyProjection e i (copyEmbedding e i w) = w := by
  simp [copyProjection, copyEmbedding]

theorem copyEmbedding_injective (e : ActionEquiv ρ (repeated σ 2)) (i : Fin 2) :
    Function.Injective (copyEmbedding e i) :=
  Function.LeftInverse.injective (copyProjection_copyEmbedding e i)

theorem copyProjection_equivariant (e : ActionEquiv ρ (repeated σ 2))
    (i : Fin 2) (g : D) (v : V) :
    copyProjection e i (ρ g v) = σ (e.groupEquiv g) (copyProjection e i v) :=
  congrFun (e.intertwines g v) i

theorem copyEmbedding_equivariant (e : ActionEquiv ρ (repeated σ 2))
    (i : Fin 2) (g : D) (w : W) :
    copyEmbedding e i (σ (e.groupEquiv g) w) = ρ g (copyEmbedding e i w) := by
  apply e.linearEquiv.injective
  rw [e.intertwines]
  change e.linearEquiv (e.linearEquiv.symm _) =
    repeated σ 2 (e.groupEquiv g) (e.linearEquiv (e.linearEquiv.symm _))
  rw [e.linearEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply]
  ext j
  by_cases h : j = i
  · subst j; simp [repeated]
  · simp [repeated, Pi.single_eq_of_ne h]

theorem copy_ranges_disjoint (e : ActionEquiv ρ (repeated σ 2)) :
    Disjoint (LinearMap.range (copyEmbedding e 0)) (LinearMap.range (copyEmbedding e 1)) := by
  apply Submodule.disjoint_def.mpr
  rintro v ⟨a, rfl⟩ ⟨b, he⟩
  have hh := congrArg (copyProjection e 0) he
  have ha : a = 0 := by
    simpa [copyProjection, copyEmbedding] using hh.symm
  rw [ha, map_zero]

theorem copy_reconstruction (e : ActionEquiv ρ (repeated σ 2)) (v : V) :
    copyEmbedding e 0 (copyProjection e 0 v) + copyEmbedding e 1 (copyProjection e 1 v) = v := by
  apply e.linearEquiv.injective
  simp only [map_add, copyEmbedding, copyProjection, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp

theorem copy_ranges_sup (e : ActionEquiv ρ (repeated σ 2)) :
    LinearMap.range (copyEmbedding e 0) ⊔ LinearMap.range (copyEmbedding e 1) = ⊤ := by
  apply top_unique
  intro v _
  exact Submodule.mem_sup.mpr ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, copy_reconstruction e v⟩

theorem copy_isIrrPlus (e : ActionEquiv ρ (repeated σ 2)) (i : Fin 2)
    (hi : IsIrrPlus σ ⊤ ⊤) : IsIrrPlus ρ ⊤ (LinearMap.range (copyEmbedding e i)) := by
  have h := IsIrrPlus.map_embedding ρ σ e.groupEquiv.toMonoidHom
    (copyEmbedding e i) (copyEmbedding_injective e i)
    (fun g w => (copyEmbedding_equivariant e i g w).symm) ⊤ ⊤
    (by simpa only [map_top_of_surjective e.groupEquiv.toMonoidHom e.groupEquiv.surjective] using hi)
  simpa only [Submodule.map_top] using h

theorem copy_line_stabilizer (e : ActionEquiv ρ (repeated σ 2))
    (i : Fin 2) (R : Submodule (ZMod 2) W) :
    subspaceStabilizer ρ (R.map (copyEmbedding e i)) =
      (subspaceStabilizer σ R).comap e.groupEquiv.toMonoidHom :=
  embedding_stabilizer (σ.comp e.groupEquiv.toMonoidHom) ρ
    (copyEmbedding e i) (copyEmbedding_injective e i)
    (copyEmbedding_equivariant e i) R

theorem copy_line_card (e : ActionEquiv ρ (repeated σ 2))
    (i : Fin 2) (R : Submodule (ZMod 2) W) :
    Nat.card (R.map (copyEmbedding e i)) = Nat.card R :=
  embedding_line_card (copyEmbedding e i) (copyEmbedding_injective e i) R

theorem copy_lines_disjoint (e : ActionEquiv ρ (repeated σ 2))
    (R : Submodule (ZMod 2) W) :
    Disjoint (R.map (copyEmbedding e 0)) (R.map (copyEmbedding e 1)) :=
  (copy_ranges_disjoint e).mono (by rintro _ ⟨w, _, rfl⟩; exact ⟨w, rfl⟩)
    (by rintro _ ⟨w, _, rfl⟩; exact ⟨w, rfl⟩)

/-- The same marked parabolic stabilizes two distinct transported lines.
The maps are the actual two coordinate embeddings, not inclusions of one
nonzero subspace into two disjoint copies. -/
theorem copy_marked_lines (e : ActionEquiv ρ (repeated σ 2))
    (P : Subgroup D) (R : Submodule (ZMod 2) W)
    (hR : Nat.card R = 4)
    (hP : P.map e.groupEquiv.toMonoidHom = subspaceStabilizer σ R) :
    (∀ i : Fin 2, Nat.card (R.map (copyEmbedding e i)) = 4 ∧
      subspaceStabilizer ρ (R.map (copyEmbedding e i)) = P) ∧
      Disjoint (R.map (copyEmbedding e 0)) (R.map (copyEmbedding e 1)) := by
  refine ⟨fun i => ⟨(copy_line_card e i R).trans hR, ?_⟩, copy_lines_disjoint e R⟩
  rw [copy_line_stabilizer, ← hP,
    Subgroup.comap_map_eq_self_of_injective e.groupEquiv.injective]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
