module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Action

/-!
# Transport of the tensor census to the actual ambient block

An actual block equivalence intertwining precisely the full conjugation
action transports orbit cardinalities and generated subgroups, as well as
coverage. Invariance of both the block and `V` is deduced from the action
formula. No normalizer moving `V`, global fusion, or order-only recognition
is used here.

The source-action realization and the intrinsic tensor census remain
separate inputs. Source: Aschbacher–Smith, 15.3.61(2), printed p.1151.
-/

public section
open Subgroup Matrix
open CFSG.Quasithin.Chapter15.Section03.FusionCore
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks
variable {G : Type*} [Group G] {I P V D : Subgroup G}

namespace BlockCoordinates
variable (c : BlockCoordinates I P V D)

/-- The model is embedded by the supplied actual block isomorphism. -/
@[expose] def embed : BlockModel →* G :=
  (fusionBlock P V D).subtype.comp c.equiv.symm.toMonoidHom

theorem embed_injective : Function.Injective c.embed :=
  Subtype.val_injective.comp c.equiv.symm.injective

@[simp] theorem embed_equiv (x : fusionBlock P V D) : c.embed (c.equiv x) = x := by
  simp [embed]

theorem embed_mem (x : BlockModel) : c.embed x ∈ fusionBlock P V D :=
  (c.equiv.symm x).property

theorem conjugate_iff (x y : BlockModel) :
    ConjugateBy I (c.embed x) (c.embed y) ↔ Related x y := by
  constructor
  · rintro ⟨g, hg, he⟩
    obtain ⟨l, r, t, h⟩ := c.forward g hg
    have h' := h (c.equiv.symm x)
    simp only [MulEquiv.apply_symm_apply] at h'
    exact ⟨l, r, t, c.embed_injective (h'.symm.trans he)⟩
  · rintro ⟨l, r, t, rfl⟩
    obtain ⟨g, hg, h⟩ := c.realize l r t
    refine ⟨g, hg, ?_⟩
    simpa [embed] using h (c.equiv.symm x)

theorem image_orbit (x : BlockModel) :
    c.embed '' {y | Related x y} = {y | ConjugateBy I (c.embed x) y} := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (c.conjugate_iff x w).mpr hw
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨l, r, t, h⟩ := c.forward g hg
    refine ⟨transform l r t x, ⟨l, r, t, rfl⟩, ?_⟩
    simpa [embed] using (h (c.equiv.symm x)).symm

theorem orbit_card (x : BlockModel) :
    Nat.card {y : G // ConjugateBy I (c.embed x) y} =
      Nat.card {y : BlockModel // Related x y} := by
  let f : {y : BlockModel // Related x y} → {y : G // ConjugateBy I (c.embed x) y} :=
    fun y => ⟨c.embed y, (c.conjugate_iff _ _).mpr y.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro y w h
      have he : c.embed y = c.embed w :=
        congrArg (fun u : {y : G // ConjugateBy I (c.embed x) y} => (u : G)) h
      exact Subtype.ext (c.embed_injective he)
    · intro y
      have hy : (y : G) ∈ c.embed '' {w | Related x w} := by
        rw [c.image_orbit]
        exact y.property
      obtain ⟨w, hw, he⟩ := hy
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem modelV_map : modelV.map c.embed = V := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (c.distinguished (c.equiv.symm y)).mpr (by simpa using hy)
  · intro hx
    let xB : fusionBlock P V D := ⟨x, (show V ≤ fusionBlock P V D from le_sup_right) hx⟩
    exact ⟨c.equiv xB, (c.distinguished xB).mp hx, c.embed_equiv xB⟩

theorem orbit_span (x : BlockModel)
    (h : closure {y | Related x y} = modelV) :
    closure {y | ConjugateBy I (c.embed x) y} = V := by
  rw [← c.image_orbit, ← MonoidHom.map_closure, h, c.modelV_map]

include c in
private theorem conj_mem_block (g : G) (hg : g ∈ I) (x : G)
    (hx : x ∈ fusionBlock P V D) : MulAut.conj g x ∈ fusionBlock P V D := by
  obtain ⟨l, r, t, h⟩ := c.forward g hg
  rw [h ⟨x, hx⟩]
  exact (c.equiv.symm _).property

include c in
theorem normalizes_block : I ≤ normalizer (fusionBlock P V D : Set G) := by
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact c.conj_mem_block g hg x
  · intro hx
    have h := c.conj_mem_block g⁻¹ (I.inv_mem hg) (MulAut.conj g x) hx
    simpa [MulAut.conj_apply, mul_assoc] using h

private theorem transform_mem_modelV (l r : Frame) (t : BinaryPlane) (x : BlockModel)
    (hx : x ∈ modelV) : transform l r t x ∈ modelV := by
  change first x = 0 at hx
  change l.val *ᵥ first x = 0
  rw [hx, Matrix.mulVec_zero]

include c in
private theorem conj_mem_V (g : G) (hg : g ∈ I) (x : G) (hx : x ∈ V) :
    MulAut.conj g x ∈ V := by
  let xB : fusionBlock P V D := ⟨x, (show V ≤ fusionBlock P V D from le_sup_right) hx⟩
  obtain ⟨l, r, t, h⟩ := c.forward g hg
  rw [h xB]
  apply (c.distinguished _).mpr
  simp only [MulEquiv.apply_symm_apply]
  exact transform_mem_modelV l r t _ ((c.distinguished xB).mp hx)

include c in
theorem normalizes_V : I ≤ normalizer (V : Set G) := by
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact c.conj_mem_V g hg x
  · intro hx
    have h := c.conj_mem_V g⁻¹ (I.inv_mem hg) (MulAut.conj g x) hx
    simpa [MulAut.conj_apply, mul_assoc] using h

end BlockCoordinates

/-- Transport the complete finite calculation through the actual action.
The realization and the tensor calculation must both be proved by callers. -/
noncomputable def blockCensus_of_coordinates
    (c : BlockCoordinates I P V D) (h : TensorCensus)
    (z v : fusionBlock P V D) (hz : Singular (c.equiv z))
    (hv : Nonsingular (c.equiv v)) : BlockCensus I P V D (z : G) (v : G) where
  model := c.equiv.trans modelSixEquiv
  normalizes_block := c.normalizes_block
  normalizes_V := c.normalizes_V
  z_mem := (c.distinguished z).mpr hz.1
  v_mem := (c.distinguished v).mpr hv.1
  outside₁ := c.embed outsideOne
  outside₂ := c.embed outsideTwo
  outside₁_mem := c.embed_mem _
  outside₂_mem := c.embed_mem _
  outside₁_not_mem := by
    intro hm
    exact outsideOne_not_mem (by simpa using (c.distinguished (c.equiv.symm outsideOne)).mp hm)
  outside₂_not_mem := by
    intro hm
    exact outsideTwo_not_mem (by simpa using (c.distinguished (c.equiv.symm outsideTwo)).mp hm)
  z_card := by simpa using (c.orbit_card (c.equiv z)).trans (h.singular_card _ hz)
  v_card := by simpa using (c.orbit_card (c.equiv v)).trans (h.nonsingular_card _ hv)
  outside₁_card := (c.orbit_card _).trans h.outsideOne_card
  outside₂_card := (c.orbit_card _).trans h.outsideTwo_card
  z_span := by simpa using c.orbit_span _ (h.singular_span _ hz)
  v_span := by simpa using c.orbit_span _ (h.nonsingular_span _ hv)
  cover := by
    intro x hx hne
    let xB : fusionBlock P V D := ⟨x, hx⟩
    have he : c.equiv xB ≠ 1 := by
      intro he
      exact hne (congrArg Subtype.val (c.equiv.injective (he.trans c.equiv.map_one.symm)))
    have horb := h.cover _ hz _ hv (c.equiv xB) he
    have tr (w : BlockModel) (hw : Related w (c.equiv xB)) :
        ConjugateBy I (c.embed w) x := by
      simpa only [c.embed_equiv] using (c.conjugate_iff _ _).mpr hw
    rcases horb with h₁ | h₂ | h₃ | h₄
    · exact Or.inl (by simpa using tr _ h₁)
    · exact Or.inr (Or.inl (by simpa using tr _ h₂))
    · exact Or.inr (Or.inr (Or.inl (tr _ h₃)))
    · exact Or.inr (Or.inr (Or.inr (tr _ h₄)))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks
