module
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceVectorGeometry

/-!
# The source polar decompositions and residual actions

For a nonsingular paired sum u+w, the original summands split as their
marked lines plus their literal intersections with ⟨u,w⟩ᗮ. The two
complements are dual natural modules for the same residual. Their sum
is the actual moving module, and the residual fixes precisely ⟨u,w⟩.
All identifications use the source quadratic form and representation.

Source: Aschbacher–Smith H.9.1(4), printed p.390, retaining its valid
module clauses under the corrected nonsingular Sylow marking.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup n M V)

theorem natural_map_coordinates (U : Submodule (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    (U.map S.naturalEmbedding).map S.model.coordinates.toLinearMap = U.prod ⊥ := by
  rw [← Submodule.map_comp]
  have he : S.model.coordinates.toLinearMap.comp S.naturalEmbedding = LinearMap.inl _ _ _ := by
    apply LinearMap.ext
    intro x
    exact S.naturalEmbedding_coordinates x
  rw [he, Submodule.map_inl]

theorem dual_map_coordinates (U : Submodule (ZMod 2) (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))) :
    (U.map S.dualEmbedding).map S.model.coordinates.toLinearMap = Submodule.prod ⊥ U := by
  rw [← Submodule.map_comp]
  have he : S.model.coordinates.toLinearMap.comp S.dualEmbedding = LinearMap.inr _ _ _ := by
    apply LinearMap.ext
    intro x
    exact S.dualEmbedding_coordinates x
  rw [he, Submodule.map_inr]

noncomputable def pairedNaturalComplement (w : S.dual) : Submodule (ZMod 2) V :=
  (S.model.dualCoordinates w).ker.map S.naturalEmbedding

private theorem mem_orthogonal_pair (u w v : V) :
    v ∈ LinearMap.BilinForm.orthogonal S.quadratic.polarBilin
        (Submodule.span (ZMod 2) {u,w}) ↔
      S.quadratic.polarBilin u v = 0 ∧ S.quadratic.polarBilin w v = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨h u (Submodule.subset_span (by simp)), h w (Submodule.subset_span (by simp))⟩
  · intro h z hz
    have hh : Submodule.span (ZMod 2) {u,w} ≤ (S.quadratic.polarBilin.flip v).ker := by
      apply Submodule.span_le.mpr
      intro a ha
      rcases (by simpa using ha : a = u ∨ a = w) with rfl | rfl
      · exact h.1
      · exact h.2
    exact hh hz

/-- The first complementary module is literally V₁∩⟨u,w⟩ᗮ. -/
theorem pairedNaturalComplement_orthogonal (u : S.natural) (w : S.dual) :
    S.pairedNaturalComplement w = S.natural ⊓ LinearMap.BilinForm.orthogonal
      S.quadratic.polarBilin (Submodule.span (ZMod 2) {(u : V),(w : V)}) := by
  ext v
  rw [Submodule.mem_inf, mem_orthogonal_pair]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(S.naturalCoordinates.symm x).property, ?_, ?_⟩
    · rw [S.polar_coordinates, S.model.natural_marking, S.naturalEmbedding_coordinates]
      simp
    · rw [S.polar_coordinates, S.model.dual_marking, S.naturalEmbedding_coordinates]
      simpa using hx
  · rintro ⟨hv,_,h⟩
    refine ⟨S.naturalCoordinates ⟨v,hv⟩, ?_, congrArg Subtype.val (S.naturalCoordinates.symm_apply_apply _)⟩
    rw [S.polar_coordinates, S.model.dual_marking, S.model.natural_marking ⟨v,hv⟩] at h
    simpa using h

/-- The dual complementary module is literally V₂∩⟨u,w⟩ᗮ. -/
theorem pairedDualComplement_orthogonal (u : S.natural) (w : S.dual) :
    S.dualHyperplane u = S.dual ⊓ LinearMap.BilinForm.orthogonal
      S.quadratic.polarBilin (Submodule.span (ZMod 2) {(u : V),(w : V)}) := by
  rw [S.dualHyperplane_eq_map]
  ext v
  rw [Submodule.mem_inf, mem_orthogonal_pair]
  constructor
  · rintro ⟨f,hf,rfl⟩
    refine ⟨(S.model.dualCoordinates.symm f).property, ?_, ?_⟩
    · rw [S.polar_coordinates, S.model.natural_marking, S.dualEmbedding_coordinates]
      simpa using hf
    · rw [S.polar_coordinates, S.model.dual_marking, S.dualEmbedding_coordinates]
      simp
  · rintro ⟨hv,h,_⟩
    refine ⟨S.model.dualCoordinates ⟨v,hv⟩, ?_, congrArg Subtype.val (S.model.dualCoordinates.symm_apply_apply _)⟩
    rw [S.polar_coordinates, S.model.natural_marking, S.model.dual_marking ⟨v,hv⟩] at h
    simpa using h

private theorem paired_coordinates (u : S.natural) (w : S.dual) :
    S.model.coordinates ((u : V) + w) = (S.naturalCoordinates u,S.model.dualCoordinates w) := by
  simp [S.model.natural_marking, S.model.dual_marking]

private theorem pairing_one (u : S.natural) (w : S.dual)
    (h : S.quadratic ((u : V) + w) = 1) :
    S.model.dualCoordinates w (S.naturalCoordinates u) = 1 := by
  simpa only [S.quadratic_apply, paired_coordinates, BinaryNaturalDual.quadratic_apply] using h

private theorem natural_line_map (u : S.natural) :
    Submodule.span (ZMod 2) {(u : V)} =
      (Submodule.span (ZMod 2) {S.naturalCoordinates u}).map S.naturalEmbedding := by
  rw [Submodule.map_span, Set.image_singleton]
  congr 2
  exact (congrArg Subtype.val (S.naturalCoordinates.symm_apply_apply u)).symm
private theorem dual_line_map (w : S.dual) :
    Submodule.span (ZMod 2) {(w : V)} =
      (Submodule.span (ZMod 2) {S.model.dualCoordinates w}).map S.dualEmbedding := by
  rw [Submodule.map_span, Set.image_singleton]
  congr 2
  exact (congrArg Subtype.val (S.model.dualCoordinates.symm_apply_apply w)).symm

/-- Both original marked summands split as the paired line plus its polar complement. -/
theorem paired_decompositions (u : S.natural) (w : S.dual)
    (h : S.quadratic ((u : V) + w) = 1) :
    Submodule.span (ZMod 2) {(u : V)} ⊔ S.pairedNaturalComplement w = S.natural ∧
    Disjoint (Submodule.span (ZMod 2) {(u : V)}) (S.pairedNaturalComplement w) ∧
    Submodule.span (ZMod 2) {(w : V)} ⊔ S.dualHyperplane u = S.dual ∧
    Disjoint (Submodule.span (ZMod 2) {(w : V)}) (S.dualHyperplane u) ∧
    Disjoint (S.pairedNaturalComplement w) (S.dualHyperplane u) := by
  have hp := pairing_one S u w h
  have hn := line_isCompl_kernel hp
  have hd := dual_line_isCompl_annihilator hp
  have hi₁ : Function.Injective S.naturalEmbedding := S.natural.injective_subtype.comp S.naturalCoordinates.symm.injective
  have hi₂ : Function.Injective S.dualEmbedding := S.dual.injective_subtype.comp S.model.dualCoordinates.symm.injective
  rw [natural_line_map, dual_line_map, pairedNaturalComplement, S.dualHyperplane_eq_map]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [← Submodule.map_sup, hn.sup_eq_top, Submodule.map_top, S.naturalEmbedding_range]
  · rw [disjoint_iff, ← Submodule.map_inf _ hi₁, hn.inf_eq_bot, Submodule.map_bot]
  · rw [← Submodule.map_sup, hd.sup_eq_top, Submodule.map_top, S.dualEmbedding_range]
  · rw [disjoint_iff, ← Submodule.map_inf _ hi₂, hd.inf_eq_bot, Submodule.map_bot]
  · apply S.complement.disjoint.mono
    · rw [← S.naturalEmbedding_range]; exact (Submodule.map_mono le_top).trans_eq (Submodule.map_top _)
    · rw [← S.dualEmbedding_range]; exact (Submodule.map_mono le_top).trans_eq (Submodule.map_top _)

/-- The source residual fixes precisely the paired plane and moves its orthogonal complement. -/
theorem paired_fixed_moving (u : S.natural) (w : S.dual)
    (h : S.quadratic ((u : V) + w) = 1) :
    S.fixed (S.residual ((u : V) + w)) = Submodule.span (ZMod 2) {(u : V),(w : V)} ∧
    S.moving ((u : V) + w) = S.pairedNaturalComplement w ⊔ S.dualHyperplane u := by
  have hp := pairing_one S u w h
  constructor
  · apply Submodule.map_injective_of_injective S.model.coordinates.injective
    rw [(S.nonsingular_structure h).2.2.2.1, paired_coordinates]
    rw [show ({(u : V),(w : V)} : Set V) = {(u : V)} ∪ {(w : V)} by ext; simp [or_comm],
      Submodule.span_union, natural_line_map, dual_line_map, Submodule.map_sup,
      S.natural_map_coordinates, S.dual_map_coordinates, Submodule.prod_sup_prod]
    simp
  · apply Submodule.map_injective_of_injective S.model.coordinates.injective
    rw [S.moving_map_nonsingular h, paired_coordinates, Submodule.map_sup,
      pairedNaturalComplement, S.natural_map_coordinates, S.dualHyperplane_eq_map,
      S.dual_map_coordinates, Submodule.prod_sup_prod]
    simp only [sup_bot_eq, bot_sup_eq]
    ext z
    rw [AdaptedPair.mem_movingSpace]
    rfl

noncomputable def pairedNaturalEquiv (w : S.dual) :
    (S.model.dualCoordinates w).ker ≃ₗ[ZMod 2] S.pairedNaturalComplement w :=
  Submodule.equivMapOfInjective S.naturalEmbedding
    (S.natural.injective_subtype.comp S.naturalCoordinates.symm.injective) _

noncomputable def pairedDualEquiv (u : S.natural) :
    annihilator (S.naturalCoordinates u) ≃ₗ[ZMod 2] S.dualHyperplane u :=
  (Submodule.equivMapOfInjective S.dualEmbedding
    (S.dual.injective_subtype.comp S.model.dualCoordinates.symm.injective) _).trans
      (LinearEquiv.ofEq _ _ (S.dualHyperplane_eq_map u).symm)

/-- The exact natural and contragredient actions on the ORIGINAL polar complements. -/
theorem paired_complement_actions (u : S.natural) (w : S.dual)
    (h : S.quadratic ((u : V) + w) = 1) :
    Module.finrank (ZMod 2) (S.pairedNaturalComplement w) = n - 1 ∧
    Module.finrank (ZMod 2) (S.dualHyperplane u) = n - 1 ∧
    ∃ (hp : S.model.dualCoordinates w (S.naturalCoordinates u) = 1)
      (e : S.residual ((u : V) + w) ≃* BinaryLinear.GL (S.model.dualCoordinates w).ker),
      (∀ (a : S.residual ((u : V) + w)) (z : (S.model.dualCoordinates w).ker),
        S.representation a.val (S.pairedNaturalEquiv w z : V) =
          (S.pairedNaturalEquiv w (e a z) : V)) ∧
      (∀ (a : S.residual ((u : V) + w)) (f : annihilator (S.naturalCoordinates u)),
        S.representation a.val (S.pairedDualEquiv u f : V) =
          (S.pairedDualEquiv u ((annihilatorEquivKernelDual hp).symm
            ((e a).symm.dualMap (annihilatorEquivKernelDual hp f))) : V)) := by
  have hh := S.nonsingular_complement_actions h
  dsimp only at hh
  rw [paired_coordinates S u w] at hh
  obtain ⟨_,_,hd₁,hd₂,hp,e,ha,hb⟩ := hh
  have hn (z : (S.model.dualCoordinates w).ker) :
      S.model.coordinates (S.pairedNaturalEquiv w z : V) = (z.val,0) :=
    S.naturalEmbedding_coordinates z
  have hd (f : annihilator (S.naturalCoordinates u)) :
      S.model.coordinates (S.pairedDualEquiv u f : V) = (0,f.val) :=
    S.dualEmbedding_coordinates f
  refine ⟨(S.pairedNaturalEquiv w).finrank_eq.symm.trans hd₁,
    (S.pairedDualEquiv u).finrank_eq.symm.trans hd₂,hp,e,?_,?_⟩
  · intro a z
    apply S.model.coordinates.injective
    rw [hn]
    have he : S.model.coordinates.symm (z.val,0) = (S.pairedNaturalEquiv w z : V) :=
      (S.model.coordinates.symm_apply_eq).mpr (hn z).symm
    simpa only [he] using ha a z
  · intro a f
    apply S.model.coordinates.injective
    rw [hd]
    have he : S.model.coordinates.symm (0,f.val) = (S.pairedDualEquiv u f : V) :=
      (S.model.coordinates.symm_apply_eq).mpr (hd f).symm
    simpa only [he] using hb a f

/-- The original pure-vector hypothesis makes the chosen sum nonsingular. -/
theorem paired_nonsingular_iff (u : S.natural) (w : S.dual) :
    S.quadratic ((u : V) + w) = 1 ↔ (w : V) ∉ S.dualHyperplane u := by
  rw [dualHyperplane, Submodule.mem_inf,
    LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
  change _ ↔ ¬ ((w : V) ∈ S.dual ∧ S.quadratic.polarBilin u w = 0)
  rw [S.polar_coordinates, S.model.natural_marking, S.model.dual_marking,
    S.quadratic_apply, paired_coordinates, BinaryNaturalDual.quadratic_apply]
  simp only [w.property, true_and, LinearMap.zero_apply, zero_add]
  exact (by decide : ∀ a : ZMod 2, a = 1 ↔ a ≠ 0) _
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
