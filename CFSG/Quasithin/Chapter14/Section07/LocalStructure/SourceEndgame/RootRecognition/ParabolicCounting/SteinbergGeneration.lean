module

public import Theory.Representation.PSL3Two.SteinbergStructure.LocalActions
public import Theory.Representation.ResidualMovedGeneration
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.SourceCounts
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# Original natural and Steinberg commutators in 14.7.73

The marked actor is the order-twelve two-residual `pointA`, transported by
an actual inner automorphism of SL₃(2). Full Steinberg commutator generation
for the point parabolic survives restriction to its two-residual by the
modular fixed-vector and duality argument. Three explicit natural-module
displacements give the corresponding generation of the natural three-space.

The original `d.qL` and equivariant coordinate maps lift these calculations
through the literal kernels: first the trivial kernel on V, then V on S.
Thus [V,L₁]=V and [S,L₁]=S. Flag invariance and characteristicity of the
actual residual give T ≤ N(L₁). The genuine source identity S=O₂(L) puts
S in T, so generation gives S ≤ L₁ and relative normality gives S ≤ O₂(L₁).
The same marked image supplies order twelve to the original fixed-kernel
count, without any extra cardinality premise.

These are conditional source applications. The original Steinberg section,
14.7.72 two-core identity, normalization of L by T, and earlier marked-image
equality remain with their source producers. The SP two-core equality and
index-two conclusion remain with the parabolic-counting assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.73, printed pp.1076–1077 (PDF pp.1093–1094), and H.6.3(5),
printed pp.387–388. Existing parabolic-counting files and public boundaries
are preserved.
-/

public section
noncomputable section

open Representation Representation.BinaryOffender Matrix.PSL3Two
namespace BinaryLinearThree.ParabolicResidualGeneration

/-- The order-twelve point residual generates all Steinberg displacements.
Restriction from the full parabolic uses the modular residual lemma. -/
private theorem steinberg (g : Group) : subspaceCommutator S ⊤
    (MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  have h := commutator_pResidual_eq_top S
    (pointParabolicSL.map (MulAut.conj g).toMonoidHom)
    (SteinbergStructure.LocalActions.point_conjugate_commutator_eq_top g)
  rw [← Subgroup.map_embedded_pResidual] at h
  change subspaceCommutator S ⊤ ((MarkedAutomorphisms.residual pointParabolicSL).map _) = ⊤ at h
  rwa [MarkedAutomorphisms.point_residual] at h

private def naturalActor (i : Fin 3) : Group :=
  ![IrreducibleCatalogue.shear, MarkedAutomorphisms.cubic, MarkedAutomorphisms.cubic] i

private def naturalSeed (i : Fin 3) : Vector :=
  ![![0,1,0], ![0,0,1], ![0,1,1]] i

private theorem naturalActor_mem (i : Fin 3) : naturalActor i ∈ MarkedAutomorphisms.pointA := by
  fin_cases i <;> decide +kernel

private theorem natural_displacement (i : Fin 3) :
    W (naturalActor i) (naturalSeed i) - naturalSeed i = Pi.single i 1 := by
  fin_cases i <;> decide +kernel

private theorem natural_point : subspaceCommutator W ⊤ MarkedAutomorphisms.pointA = ⊤ := by
  have hb (i : Fin 3) : Pi.single i 1 ∈ subspaceCommutator W ⊤ MarkedAutomorphisms.pointA :=
    Submodule.subset_span ⟨naturalActor i, naturalActor_mem i, naturalSeed i,
      Submodule.mem_top, (natural_displacement i).symm⟩
  apply top_unique
  intro v _
  rw [pi_eq_sum_univ' v]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)

/-- The same order-twelve point residual generates the original natural
three-space, with the marking transported by the actual inner automorphism. -/
private theorem natural (g : Group) : subspaceCommutator W ⊤
    (MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  have hc (h : Group) (v : Vector) : W (g * h * g⁻¹) (W g v) = W g (W h v) := by
    simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
  have ht : ∀ v ∈ subspaceCommutator W ⊤ MarkedAutomorphisms.pointA,
      W g v ∈ subspaceCommutator W ⊤
        (MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, _, rfl⟩ := hv
      rw [map_sub]
      apply Submodule.subset_span
      exact ⟨g * a * g⁻¹, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩,
        W g u, Submodule.mem_top, by rw [hc]⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa using Submodule.smul_mem _ c ha
  apply top_unique
  intro v _
  have hv : W g⁻¹ v ∈ subspaceCommutator W ⊤ MarkedAutomorphisms.pointA := by
    rw [natural_point]
    trivial
  simpa only [Representation.self_inv_apply] using ht _ hv
end BinaryLinearThree.ParabolicResidualGeneration

open Subgroup Representation.BinaryOffender
namespace Representation.BinaryConjugationSection
variable {G D W : Type*} [Group G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {H A B J : Subgroup G} (π : H →* D) (σ : Representation (ZMod 2) D W)
  (s : BinaryConjugationSection H A B (σ.comp π))

include s in
/-- Full displacement under the literal actor image lifts across exactly the
specified coordinate kernel. -/
private theorem eq_commutator_sup_of_model_generation (hJ : J ≤ H)
    (hgen : subspaceCommutator σ ⊤ ((J.subgroupOf H).map π) = ⊤) :
    A = ⁅A, J⁆ ⊔ B := by
  have hm : subspaceCommutator σ ⊤ ((J.subgroupOf H).map π) ≤
      s.imageSpace ⁅A, J⁆ := by
    apply Submodule.span_le.mpr
    rintro w ⟨j, hj, v, _, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hj
    exact s.displacement_range_le_imageSpace_of_commutator_le J ⁅A, J⁆
      (commutator_comm J A).le h hh ⟨v, rfl⟩
  have hcomm : ⁅A, J⁆ ≤ A :=
    le_normalizer_iff_commutator_le_left.mp (hJ.trans s.normalized)
  apply le_antisymm
  · intro a ha
    let aA : A := ⟨a, ha⟩
    have hw : (s.coordinates aA).toAdd ∈ s.imageSpace ⁅A, J⁆ := by
      apply hm
      rw [hgen]
      trivial
    obtain ⟨c, hc, he⟩ := (s.mem_imageSpace_iff _ _).mp hw
    have hk : ((aA / c : A) : G) ∈ B := by
      apply (s.coordinates_eq_one_iff _).mp
      rw [map_div, Multiplicative.toAdd.injective he, div_self']
    have h := (⁅A, J⁆ ⊔ B).mul_mem ((show B ≤ ⁅A, J⁆ ⊔ B from le_sup_right) hk)
      ((show ⁅A, J⁆ ≤ ⁅A, J⁆ ⊔ B from le_sup_left) hc)
    simpa only [Subgroup.coe_div, div_mul_cancel] using h
  · exact sup_le hcomm s.kernel_le
end Representation.BinaryConjugationSection

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.SteinbergGeneration
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The original natural coordinates have trivial kernel; the marked point
residual therefore generates V by actual subgroup commutators. -/
theorem natural_commutator (hVL : V ≤ L) (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    ⁅V, F.Li L 1⁆ = V := by
  have h := (d.natural_section hVL).eq_commutator_sup_of_model_generation
    d.qL BinaryLinearThree.W ((F.Li_le L 1).trans inf_le_left)
    (by rw [hmark]; exact BinaryLinearThree.ParabolicResidualGeneration.natural g)
  simpa only [sup_bot_eq] using h.symm

/-- The literal kernel of the Steinberg coordinates is the original V. -/
theorem steinberg_commutator_sup
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    S L F = ⁅S L F, F.Li L 1⁆ ⊔ V := by
  exact s.eq_commutator_sup_of_model_generation d.qL BinaryLinearThree.S
    ((F.Li_le L 1).trans inf_le_left)
    (by rw [hmark]; exact BinaryLinearThree.ParabolicResidualGeneration.steinberg g)

/-- The opening generation step of 14.7.73, combining the original natural
and Steinberg sections through their literal kernels. -/
theorem steinberg_commutator
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    ⁅S L F, F.Li L 1⁆ = S L F := by
  have hV : V ≤ ⁅S L F, F.Li L 1⁆ :=
    (natural_commutator d (s.kernel_le.trans s.section_le) g hmark).symm.le.trans
      (commutator_mono s.kernel_le le_rfl)
  have h := steinberg_commutator_sup d s g hmark
  rw [sup_eq_left.mpr hV] at h
  exact h.symm

omit [Finite G] in
/-- T normalizes the actual two-residual of L intersected with the point
normalizer, by the flag invariance and characteristicity of the residual. -/
theorem T_normalizes_L₁ (hTL : (T : Subgroup G) ≤ normalizer L) :
    (T : Subgroup G) ≤ normalizer (F.Li L 1) := by
  change (T : Subgroup G) ≤ normalizer
    ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
  apply LE.le.trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ F.Gi 1) (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)))
  exact (le_inf hTL ((F.invariant 1).trans (F.Gi 1).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

omit [Finite G] in
/-- The source two-core identity and ambient Sylow maximality put S in T. -/
theorem S_le_T (hS : S L F = L.pCoreIn 2)
    (hTL : (T : Subgroup G) ≤ normalizer L) : S L F ≤ (T : Subgroup G) := by
  have hn : (T : Subgroup G) ≤ normalizer (S L F) := by
    rw [hS]
    exact hTL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hp : IsPGroup 2 (S L F) := hS.symm ▸ isPGroup_pCoreIn 2 L
  exact sup_eq_right.mp (T.is_maximal' (hp.to_sup_of_normal_left' T.isPGroup' hn) le_sup_right)

/-- Generation places S in the literal point residual L₁. -/
theorem S_le_L₁ (hS : S L F = L.pCoreIn 2)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    S L F ≤ F.Li L 1 := by
  rw [← steinberg_commutator d s g hmark]
  exact le_normalizer_iff_commutator_le_right.mp
    ((S_le_T hS hTL).trans (T_normalizes_L₁ hTL))

/-- The same S is a normal two-subgroup of L₁, hence belongs to O₂(L₁).
The reverse inclusion, and the full SP identity, are separate counting steps. -/
theorem S_le_parabolic_twoCore (hS : S L F = L.pCoreIn 2)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    S L F ≤ (F.Li L 1).pCoreIn 2 := by
  exact le_pCoreIn_of_normalizes (hS.symm ▸ isPGroup_pCoreIn 2 L)
    (S_le_L₁ d hS hTL s g hmark)
    (((F.Li_le L 1).trans inf_le_left).trans s.normalized)

/-- The marked image has order twelve, including the specified conjugation. -/
theorem marked_image_card (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    Nat.card (((F.Li L 1).subgroupOf L).map d.qL) = 12 := by
  rw [hmark]
  exact (Nat.card_congr (Matrix.PSL3Two.MarkedAutomorphisms.pointA.equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).symm.trans
      Matrix.PSL3Two.MarkedAutomorphisms.card_pointA

/-- Actual application to the previously proved fixed-kernel count. Its
parabolic cardinality premise is discharged by the original marked equality. -/
theorem source_fixed_kernel_count_marked (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (hpoint : d.U₀ = F.Vi 1)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom)
    (B : Sylow 3 (F.Li L 1)) :
    F.U.relIndex (E L F k) = 4 ∧ Nat.card ((K F).pCoreIn 2) = 2 ^ 11 :=
  source_fixed_kernel_count d k hS hPhi hgen hpoint s n (marked_image_card d g hmark) B
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.SteinbergGeneration
