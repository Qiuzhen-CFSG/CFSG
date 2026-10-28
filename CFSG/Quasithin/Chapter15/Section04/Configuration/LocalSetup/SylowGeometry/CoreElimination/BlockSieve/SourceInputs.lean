module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Basic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.InternalModule
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.PCoreRestriction

/-!
# Source inputs and target for the block sieve in 15.4.20

The contrary overgroup retains the full placed geometry, including the
marked S₃ × S₃ quotient and the outside Y-factor. The residual and relative
normal-closure identities concern the same K in H=KU. The two embedding
alternatives are exactly those preceding the characteristic-two argument
on printed p.1164. The target keeps the exchanged component product and
an actual even-field natural-module block, without specializing its field.

These are contracts for the remaining sieve, not an assertion of its
classification. The source input contains neither a block conclusion nor
a Borel placement. Relative C-components and intrinsic quotients are retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.4.20,
printed p.1164; C.2.7(3), pp.145–147; C.1.34, pp.136–137.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G]

/-- Earlier source geometry, before any of the block alternatives is selected. -/
structure Input (d : Source.Geometry G) (i j : Bool) (H U K : Subgroup G) where
  placed : EmbeddingReduction.PlacedX d i j H U
  seed : d.Z = omegaOneCenterAmbient (d.T : Subgroup G)
  seed_card : Nat.card d.Z = 4
  seed_centralizer : centralizer (d.Z : Set G) = (d.T : Subgroup G)
  thompson : d.J = elementaryAbelianMaxJ (d.T : Subgroup G)
  factor_commutator : d.X i = ⁅d.X i, d.J⁆
  generation : K ⊔ U = H
  closure : K = EmbeddingReduction.normalClosureIn d.wholeX H
  residual : K = (primeToResidual 3 H).map H.subtype
  characteristic_two : generalizedFitting K = pCore 2 K

/-- The binary-linear alternative uses the whole automorphism-group quotient. -/
def BinaryEmbedding (H K : Subgroup G) : Prop :=
  K ∈ Chapter1.cComponentsIn H ∧ ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
    Nonempty ((H ⧸ pCore 2 H) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))

/-- The literal exchanged-component alternative, including both field possibilities. -/
def ExchangedEmbedding (H U K : Subgroup G) : Prop :=
  ∃ (K₁ : Subgroup G) (r : G), K₁ ∈ Chapter1.cComponentsIn H ∧
    r ∈ U ∧ r ∉ normalizer (K₁ : Set G) ∧
    K₁ ⊔ K₁.map (MulAut.conj r).toMonoidHom = K ∧
    (K : Set G) = (K₁ : Set G) * (K₁.map (MulAut.conj r).toMonoidHom : Set G) ∧
    Chapter1.XiEmbedding.SwappedModel 3 (K₁ ⧸ pCore 2 K₁)

/-- The two embedding alternatives on p.1164, with no component or module
classification silently built into the characteristic-two input. -/
def EmbeddingCases (H U K : Subgroup G) : Prop :=
  BinaryEmbedding H K ∨ ExchangedEmbedding H U K

/-- Desired output of the sieve. `IsL2EvenBlock` includes the actual field,
core-quotient isomorphism, and compatible natural-module model. -/
def ExchangedL2Block (H U K : Subgroup G) : Prop :=
  ∃ (K₁ : Subgroup G) (r : G) (n : ℕ), K₁ ∈ Chapter1.cComponentsIn H ∧
    (K₁.subgroupOf H).IsSubnormal ∧
    r ∈ U ∧ r ∉ normalizer (K₁ : Set G) ∧
    K₁ ⊔ K₁.map (MulAut.conj r).toMonoidHom = K ∧
    (K : Set G) = (K₁ : Set G) * (K₁.map (MulAut.conj r).toMonoidHom : Set G) ∧
    Even n ∧ Nat.ModEq 3 (2 ^ n) 1 ∧ ChapterC.IsL2EvenBlock K₁ n

/-- The source radical is the intrinsic two-core of XU, mapped into G. -/
def sourceRadical (d : Source.Geometry G) (U : Subgroup G) : Subgroup G :=
  (d.wholeX ⊔ U).pCoreIn 2

variable {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- The source normal-closure identity supplies relative containment. -/
theorem Input.K_le (h : Input d i j H U K) : K ≤ H := by
  rw [h.closure]
  exact EmbeddingReduction.normalClosureIn_le_overgroup _ _

/-- The source normal closure is normal in H, not necessarily in G. -/
theorem Input.K_normalized (h : Input d i j H U K) : H ≤ normalizer (K : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer h.K_le).mp
  rw [h.closure]
  exact EmbeddingReduction.normalClosureIn_normal _ _

/-- Source geometry constructs the seed and Thompson inputs inside H. -/
theorem Input.seed_inputs [Finite G] (h : Input d i j H U K) :
    d.Z ≤ H ∧ IsElementaryAbelian 2 (d.Z.subgroupOf H) ∧
      centralizer (d.Z.subgroupOf H : Set H) = (h.placed.sylow : Subgroup H) ∧
      d.Z.subgroupOf H ≤ omegaOneCenterAmbient (h.placed.sylow : Subgroup H) ∧
      (d.X i).subgroupOf H = ⁅(d.X i).subgroupOf H,
        elementaryAbelianMaxJ (h.placed.sylow : Subgroup H)⁆ ∧
      ⁅d.Z.subgroupOf H, (d.X i).subgroupOf H⁆ ≠ ⊥ := by
  apply source_seed_inputs d.T H U d.Z (d.X i) h.placed.sylow h.placed.sylow_image
    h.placed.upper.le h.placed.baumann_le h.seed h.seed_centralizer
    ((d.X_le_I i j).trans h.placed.overgroup.2)
  · simpa only [← h.thompson] using h.factor_commutator
  · exact seed_moved_of_factor_quotient d.T d.Z (d.X i) h.seed_centralizer
      h.placed.first_quotient_card

/-- The internal module is elementary, and its two-core kernel and omega
containment come from the actual source geometry. -/
theorem Input.module_properties [Finite G] (h : Input d i j H U K) :
    let V := TwoFactors.FFBranch.moduleClosure (d.Z.subgroupOf H)
    IsElementaryAbelian 2 V ∧
      V.map H.subtype = conjugateModule K d.Z ∧
      V ≤ omegaOneCenterAmbient (pCore 2 H) ∧
      centralizer (V : Set H) = pCore 2 H := by
  obtain ⟨_, hm, hVQ, hc, _, hV, _⟩ := source_internal_module d.T H K U d.Z
    (d.X i) h.placed.sylow h.placed.sylow_image h.placed.upper.le
    h.placed.baumann_le h.seed h.seed_centralizer h.K_le h.K_normalized
    h.generation h.characteristic_two ((d.X_le_I i j).trans h.placed.overgroup.2)
    (by simpa only [← h.thompson] using h.factor_commutator)
    h.placed.first_quotient_card
  exact ⟨hV, hm, hVQ, hc⟩

/-- The seed lies in the intrinsic core of H, not in the core of the ambient G. -/
theorem Input.seed_le_core [Finite G] (h : Input d i j H U K) :
    d.Z.subgroupOf H ≤ pCore 2 H := by
  intro z hz
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp
    (h.module_properties.2.2.1 (le_normalClosure hz))).1

/-- The actual Sylow subgroup U bounds O₂(XU). -/
theorem Input.radical_le_sylow (h : Input d i j H U K) : sourceRadical d U ≤ U := by
  have hUH : U ≤ H := h.placed.sylow_image ▸ map_subtype_le _
  have hs : Chapter1.IsSylowIn 2 U H := ⟨h.placed.sylow, h.placed.sylow_image⟩
  obtain ⟨P, hP⟩ := hs.restrict le_sup_right (sup_le h.placed.whole_le hUH)
  exact (pCoreIn_le_sylow _ P).trans_eq hP

/-- The internal core containment places Z in the actual radical O₂(XU). -/
theorem Input.seed_le_radical [Finite G] (h : Input d i j H U K) :
    d.Z ≤ sourceRadical d U := by
  have hZH := h.seed_inputs.1
  have hZQ : d.Z ≤ H.pCoreIn 2 := by
    intro z hz
    exact ⟨⟨z, hZH hz⟩, h.seed_le_core hz, rfl⟩
  have hZU : d.Z ≤ U := h.seed ▸ (omegaCenter_le_baumann _).trans h.placed.baumann_le
  have hUH : U ≤ H := h.placed.sylow_image ▸ map_subtype_le _
  exact (le_inf (hZU.trans le_sup_right) hZQ).trans
    (inf_pCoreIn_le_of_le 2 (sup_le h.placed.whole_le hUH))

/-- The radical centralizes the seed because it lies in the actual ambient Sylow group. -/
theorem Input.radical_centralizes_seed (h : Input d i j H U K) :
    sourceRadical d U ≤ centralizer (d.Z : Set G) := by
  rw [h.seed_centralizer]
  exact h.radical_le_sylow.trans h.placed.upper.le

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
