module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.QuartetSplitting.Levi
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.QuartetSplitting.ClassTwo
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting
public import Theory.GroupTheory.CentralExtensionSections
public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity
public import Mathlib.Algebra.Group.Shrink

/-!
# Prescribed Suzuki lifts and the four nonabelian Ree sections

Pull the given central extension back along the genuine middle-node Suzuki
embedding, and pass to its derived subgroup. For m≥2, the established Suzuki
kernel theorem makes this derived projection bijective. Invert that literal
map and transport its lift to all four B₂ blocks.

For m=1, the same construction works provided ambient commutators force the
lifted Suzuki root group to have class two. The three-dimensional pairing
calculation and torus norm then kill its stem kernel. This ambient premise is
still explicit; this module does not claim the q=8 Ree splitting without it.

Source: Aschbacher–Smith I.1.1–4, pp.407–408; GLS3 §6.1 and §§2.3–2.4.
-/

@[expose] public noncomputable section
namespace ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
open Subgroup PerfectCentralCovering ElementaryTwoBound
open BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.SchurCover.Family
open scoped commutatorElement
universe u
variable {m : ℕ} {E : Type u} [Group E]

/-- The exact ambient commutator obligation. All three elements lie over the
root subgroup of the actual embedded Suzuki matrix group. -/
def LiftedRootClassTwo (m : ℕ) (f : E →* Model m) : Prop :=
  ∀ a b c : E,
    f a ∈ (SuzukiRootSubgroup m).map (suzukiEmbedding m) →
    f b ∈ (SuzukiRootSubgroup m).map (suzukiEmbedding m) →
    f c ∈ (SuzukiRootSubgroup m).map (suzukiEmbedding m) → ⁅⁅a,b⁆,c⁆ = 1

/-- The literal preimage of the embedded Suzuki Levi. -/
def leviPreimage (f : E →* Model m) : Subgroup E := (suzukiEmbedding m).range.comap f

/-- Its projection to the concrete Suzuki carrier, retaining the embedding. -/
def leviProjection (f : E →* Model m) : leviPreimage f →* SuzukiMatrixGroup m :=
  (MonoidHom.ofInjective (suzukiEmbedding_injective m)).symm.toMonoidHom.comp
    (f.subgroupComap (suzukiEmbedding m).range)

theorem leviProjection_triangle (f : E →* Model m) (x : leviPreimage f) :
    suzukiEmbedding m (leviProjection f x) = f x :=
  congrArg Subtype.val ((MonoidHom.ofInjective (suzukiEmbedding_injective m)).apply_symm_apply _)

theorem leviProjection_surjective (f : E →* Model m) (hf : Function.Surjective f) :
    Function.Surjective (leviProjection f) :=
  (MonoidHom.ofInjective (suzukiEmbedding_injective m)).symm.surjective.comp
    (f.subgroupComap_surjective_of_surjective _ hf)

theorem leviProjection_ker_le_center (f : E →* Model m) (hk : f.ker ≤ center E) :
    (leviProjection f).ker ≤ center (leviPreimage f) := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply mem_center_iff.mp (hk ?_) y
  change f x = 1
  rw [← leviProjection_triangle, MonoidHom.mem_ker.mp hx, map_one]

/-- The derived pullback, with the same specified projection. -/
def leviCover [Fact (0 < m)] (f : E →* Model m) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) : Cover (_root_.commutator (leviPreimage f)) (SuzukiMatrixGroup m) :=
  CentralExtension.derivedCover (leviProjection f) (leviProjection_surjective f hf)
    (leviProjection_ker_le_center f hk)

private theorem exists_suzuki_lift_of_leviCover_injective [Fact (0 < m)]
    (f : E →* Model m) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (hi : Function.Injective (leviCover f hf hk).toMonoidHom) :
    ∃ s : SuzukiMatrixGroup m →* E, f.comp s = suzukiEmbedding m := by
  let c := leviCover f hf hk
  let e := MulEquiv.ofBijective c.toMonoidHom ⟨hi, c.surjective⟩
  refine ⟨(leviPreimage f).subtype.comp
    ((_root_.commutator (leviPreimage f)).subtype.comp e.symm.toMonoidHom), ?_⟩
  apply MonoidHom.ext
  intro x
  change f (e.symm x).val.val = suzukiEmbedding m x
  rw [← leviProjection_triangle]
  exact congrArg (suzukiEmbedding m) (e.apply_symm_apply x)

/-- Every central extension lifts the specified Suzuki Levi when m≥2. The
map triangle, not just an abstract splitting, is retained. -/
theorem exists_suzuki_lift_of_two_le (m : ℕ) (hm : 2 ≤ m)
    (f : E →* Model m) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ∃ s : SuzukiMatrixGroup m →* E, f.comp s = suzukiEmbedding m := by
  let : Fact (0 < m) := ⟨by omega⟩
  apply exists_suzuki_lift_of_leviCover_injective f hf hk
  exact (leviCover f hf hk).injective_of_universalProjection_ker_eq_bot
    (canonicalKernel_eq_bot m hm)

private theorem leviCover_root_class_two [Fact (0 < m)]
    (f : E →* Model m) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (hc : LiftedRootClassTwo m f) :
    _root_.commutator (rootPreimage (leviCover f hf hk)) ≤
      center (rootPreimage (leviCover f hf hk)) := by
  let c := leviCover f hf hk
  let R := rootPreimage c
  let r : R →* E := (leviPreimage f).subtype.comp
    ((_root_.commutator (leviPreimage f)).subtype.comp R.subtype)
  have hr : Function.Injective r :=
    Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  have hmemb (x : R) : f (r x) ∈ (SuzukiRootSubgroup m).map (suzukiEmbedding m) :=
    ⟨c.toMonoidHom x.val, x.property, leviProjection_triangle f x.val.val⟩
  have ht (x y z : R) : ⁅⁅x,y⁆,z⁆ = 1 := by
    apply hr
    simpa only [map_commutatorElement, map_one] using
      hc (r x) (r y) (r z) (hmemb x) (hmemb y) (hmemb z)
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  exact mem_center_iff.mpr (fun z =>
    (commutatorElement_eq_one_iff_mul_comm.mp (ht x y z)).symm)

private theorem exists_suzuki_lift_of_class_two_small {E : Type} [Group E] [Finite E]
    (m : ℕ) (hm : 1 ≤ m) (f : E →* Model m) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hc : LiftedRootClassTwo m f) :
    ∃ s : SuzukiMatrixGroup m →* E, f.comp s = suzukiEmbedding m := by
  let : Fact (0 < m) := ⟨by omega⟩
  apply exists_suzuki_lift_of_leviCover_injective f hf hk
  apply (leviCover f hf hk).toMonoidHom.ker_eq_bot_iff.mp
  exact suzuki_kernel_eq_bot_of_class_two m hm (leviCover f hf hk)
    (leviCover_root_class_two f hf hk hc)

/-- Class two of the ambient lifted root group suffices, including m=1.
Finite carriers in arbitrary universes are transported without changing maps. -/
theorem exists_suzuki_lift_of_class_two [Finite E] (m : ℕ) (hm : 1 ≤ m)
    (f : E →* Model m) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (hc : LiftedRootClassTwo m f) :
    ∃ s : SuzukiMatrixGroup m →* E, f.comp s = suzukiEmbedding m := by
  let e : Shrink.{0} E ≃* E := Shrink.mulEquiv
  let : Finite (Shrink.{0} E) := Finite.of_injective e e.injective
  let g := f.comp e.toMonoidHom
  have hg : Function.Surjective g := hf.comp e.surjective
  have hgk : g.ker ≤ center (Shrink.{0} E) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using mem_center_iff.mp (hk hx) (e y)
  have hgc : LiftedRootClassTwo m g := by
    intro x y z hx hy hz
    apply e.injective
    simpa only [map_commutatorElement, map_one] using hc (e x) (e y) (e z) hx hy hz
  obtain ⟨s, hs⟩ := exists_suzuki_lift_of_class_two_small m hm g hg hgk hgc
  refine ⟨e.toMonoidHom.comp s, ?_⟩
  apply MonoidHom.ext
  intro x
  exact DFunLike.congr_fun hs x

/-- The four nonabelian sections for all ordinary parameters. No relation,
splitting, torus-equivariance or Ree multiplier premise remains. -/
theorem quartet_sections_of_two_le (m : ℕ) (hm : 2 ≤ m)
    (f : E →* Model m) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ∀ j : Fin 4, ∃ s : X m (rootIndex (.inr j)) →* E,
      f.comp s = (X m (rootIndex (.inr j))).subtype := by
  obtain ⟨s, hs⟩ := exists_suzuki_lift_of_two_le m hm f hf hk
  exact quartet_sections_of_suzuki_lift m f hf s hs

/-- The complete parameter range, with only the exceptional ambient
class-two calculation left explicit. -/
theorem quartet_sections_of_small_class_two [Finite E] (m : ℕ) (hm : 1 ≤ m)
    (f : E →* Model m) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (hc : m = 1 → LiftedRootClassTwo m f) :
    ∀ j : Fin 4, ∃ s : X m (rootIndex (.inr j)) →* E,
      f.comp s = (X m (rootIndex (.inr j))).subtype := by
  by_cases hm2 : 2 ≤ m
  · exact quartet_sections_of_two_le m hm2 f hf hk
  · obtain ⟨s, hs⟩ := exists_suzuki_lift_of_class_two m hm f hf hk (hc (by omega))
    exact quartet_sections_of_suzuki_lift m f hf s hs

/-- Two-coordinate points of each literal quartet subgroup. -/
def quartetPoint (m : ℕ) (j : Fin 4) (a b : CoefficientField m) :
    X m (rootIndex (.inr j)) :=
  ⟨blockPoint m _ a b, (mem_X_even m _
    (Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.positiveRootWordLayout.quartet_even j)
      _).mpr ⟨a,b,rfl⟩⟩

/-- The complete internal multiplication law in the subgroup carrier. -/
theorem quartetPoint_mul (m : ℕ) (j : Fin 4) (a b c d : CoefficientField m) :
    quartetPoint m j a b * quartetPoint m j c d =
      quartetPoint m j (a+c) (titsEnd m a * c + (b+d)) :=
  Subtype.ext (blockPoint_mul m _
    (Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.positiveRootWordLayout.quartet_even j)
      a b c d)

/-- Every constructed section obeys the full nonabelian law upstairs, with
exactly the prescribed Tits-endomorphism correction. -/
theorem section_multiplication (m : ℕ) (j : Fin 4)
    (s : X m (rootIndex (.inr j)) →* E) (a b c d : CoefficientField m) :
    s (quartetPoint m j a b) * s (quartetPoint m j c d) =
      s (quartetPoint m j (a+c) (titsEnd m a * c + (b+d))) := by
  rw [← map_mul, quartetPoint_mul]

/-- Unconditional ordinary-parameter sections together with their full
internal laws upstairs. -/
theorem quartet_sections_with_multiplication_of_two_le (m : ℕ) (hm : 2 ≤ m)
    (f : E →* Model m) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ∀ j : Fin 4, ∃ s : X m (rootIndex (.inr j)) →* E,
      f.comp s = (X m (rootIndex (.inr j))).subtype ∧
      ∀ a b c d : CoefficientField m,
        s (quartetPoint m j a b) * s (quartetPoint m j c d) =
          s (quartetPoint m j (a+c) (titsEnd m a * c + (b+d))) := by
  intro j
  obtain ⟨s, hs⟩ := quartet_sections_of_two_le m hm f hf hk j
  exact ⟨s,hs,section_multiplication m j s⟩

end ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
