module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairMovement
/-!
# A concrete point parabolic for the moving root-pair envelope

The first hyperbolic-plane SL₂ and the optional second long root fix the
second basis vector. Their envelope therefore lies in its point stabilizer,
which is proper because the opposite second root moves that line.
Combining this calculation with inner root-pair alignment gives one marking
for the full preimage envelope, its rank-one quotient and residual movement.

Source: the rank-one construction in MS93 (5.1), printed p.913. The actual
replacement application is in RootProductMovement. Alignment of this point
parabolic with the source's selected path and the normalizer generation
statements are separate obligations.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Subgroup Matrix Representation
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.RootEnvelope
variable {F : Type*} [Field F]

/-- The chosen rank-one envelope lies in the parabolic of the second standard point. -/
theorem group_le_second_point_stabilizer (b : Bool) :
    group (F := F) b ≤ Theory.SpecificGroups.SymplecticFour.stabilizer (F ∙ e 1) := by
  rintro x ⟨⟨A,z⟩,rfl⟩
  apply (mem_stabilizer_iff _ _).mpr
  have hv : embedding b (A,z) • e (F := F) 1 = e 1 := by
    change (OppositeLongRootPair.embedding A * rootElement 2 z.val.toAdd) • e (F := F) 1 = _
    rw [mul_smul]
    have hr : rootElement 2 z.val.toAdd • e (F := F) 1 = e 1 := by
      change (rootElement 2 z.val.toAdd).val *ᵥ e (F := F) 1 = _
      ext i
      rcases i with i | i <;> fin_cases i <;>
        simp [e,rootElement,rootMatrix,Matrix.fromBlocks,Matrix.single,Matrix.mulVec,dotProduct]
    rw [hr]
    change OppositeLongRootPair.matrix A *ᵥ e (F := F) 1 = _
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [e,OppositeLongRootPair.matrix,Matrix.fromBlocks,Matrix.mulVec,dotProduct]
  intro v hv'
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv'
  change toLinear (embedding b (A,z)) (c • e 1) ∈ _
  rw [map_smul]
  change c • (embedding b (A,z) • e 1) ∈ _
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- This geometric parabolic is proper; the opposite second root moves its point. -/
theorem second_point_stabilizer_ne_top :
    Theory.SpecificGroups.SymplecticFour.stabilizer (F ∙ e (F := F) 1) ≠ ⊤ := by
  intro ht
  have hr : rootElement 3 (1:F) ∈ Theory.SpecificGroups.SymplecticFour.stabilizer (F ∙ e (F := F) 1) :=
    ht ▸ mem_top _
  have hv := (mem_stabilizer_iff _ _).mp hr (e (F := F) 1) (Submodule.mem_span_singleton_self _)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv
  have hh := congrFun hc (.inr 1)
  change (c • e (F := F) 1) (.inr 1) = ((rootElement 3 (1:F)).val *ᵥ e (F := F) 1) (.inr 1) at hh
  simp [e,rootElement,rootMatrix,Matrix.fromBlocks,Matrix.single,Matrix.mulVec,dotProduct] at hh
variable [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
local notation "τ" => restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
open Representation.BinaryOffender

/-- Arbitrary full root pairs retain the residual noncentrality after
conjugating the quotient marking inside the original symplectic group. -/
theorem exists_moving_root_pair_envelope_in_point_parabolic
    {G : Type*} [Group G] [Finite G]
    (f : G →* Sp F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (U J : Subgroup G) (hkJ : f.ker ≤ J) (s t : Option F)
    (hJ : J.map f = rootImage s ⊔ rootImage t)
    (hindex : ∀ A : Subgroup G, (centralizer (A : Set G)).relIndex U =
      2 ^ fixedCodim τ (A.map f)) :
    ∃ I : Subgroup G, J ≤ I ∧
      ∃ S : Sylow 2 I, (S : Subgroup I).map I.subtype = J ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
        ⁅U ⊓ centralizer (J : Set G), (pResidual 2 I).map I.subtype⁆ ≠ ⊥ ∧
        ∃ g : Sp F, I.map ((MulAut.conj g).toMonoidHom.comp f) ≤
          Theory.SpecificGroups.SymplecticFour.stabilizer (F ∙ e (F := F) 1) := by
  obtain ⟨g,hg⟩ := rootPair_standard_first s t
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x)=1 ↔ f x=1
    exact (MulAut.conj g).map_eq_one_iff
  have hm : J.map f' = (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom := by
    rw [←Subgroup.map_map,hJ]
  have hi : ∀ A : Subgroup G, (centralizer (A : Set G)).relIndex U =
      2 ^ fixedCodim τ (A.map f') := by
    intro A
    rw [←Subgroup.map_map,fixedCodim_map_conj]
    exact hindex A
  have hh (b : Bool) (hb : J.map f' = sylowImage b) :=
    exists_moving_preimage_envelope f' hf' (hker ▸ hk) U J (hker ▸ hkJ) b hb hi
  rcases hg with hg | hg
  · obtain ⟨I,hJI,hIm,S,hS,he,hn⟩ := hh false
      (by simpa only [sylowImage,Bool.false_eq_true,↓reduceIte,sup_bot_eq] using hm.trans hg)
    exact ⟨I,hJI,S,hS,he,hn,g,hIm.le.trans (group_le_second_point_stabilizer _)⟩
  · obtain ⟨I,hJI,hIm,S,hS,he,hn⟩ := hh true
      (by simpa only [sylowImage,↓reduceIte] using hm.trans hg)
    exact ⟨I,hJI,S,hS,he,hn,g,hIm.le.trans (group_le_second_point_stabilizer _)⟩

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.RootEnvelope
