module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Kernel
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import Theory.Representation.SL2NaturalOffenders.OddDegree

/-!
# Half-Sylow actors on odd-degree rank-one covers

The original full moved factor and its fixed quotient have the same
normalizer kernel. The induced automizer therefore embeds faithfully in
the binary normalizer of the marked natural SL₂ action. Over an odd-degree
field every two-element of this normalizer belongs to the original SL₂
image. Lifting through the common kernel makes every original two-subgroup
of the component normalizer act through L on the full moved factor.
It consequently fixes the entire component-fixed kernel, including when
the cover is nonsplit.

Source: Aschbacher--Smith, 10.1.1(1) and10.2.9, printed pp.741 and750,
using the natural normalizer calculation in B.4.2(1), printed p.86.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance oddActorBinaryAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2
local instance oddActorMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
  (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

include e c

/-- Over an odd-degree field, every two-subgroup of the common normalizer
acts on the original full moved factor through the component. -/
theorem two_subgroup_le_linear_actor_of_odd_degree
    {n : ℕ} (hn : Odd n) (hcard : Nat.card F = 2 ^ n)
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G)) :
    P ≤ L ⊔ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let M := D.maximalLocal ⊓ normalizer (L : Set G)
  let N := M ⊓ normalizer (W : Set G)
  let q := localNormalizerAction W M
  let σ := SL2.BinarySmall.natural (K := F)
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hLM : L ≤ M := le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
  have hNL : N ≤ normalizer (L : Set G) := inf_le_left.trans inf_le_right
  have hNZ := (le_inf hNL (show N ≤ normalizer (W : Set G) from inf_le_right)).trans
    (source_original_moved_fixed_normalizer D)
  have hk : commutatorPreimage N W (sourceMovedFixed D) ≤ centralizer (W : Set G) := by
    have hh : commutatorPreimage N W (sourceMovedFixed D) ≤
        commutatorPreimage (normalizer (L : Set G) ⊓ normalizer (W : Set G)) W (sourceMovedFixed D) :=
      le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans (le_inf hNL inf_le_right))
        (commutator_commutatorPreimage_le _ _ _ hNZ)
    rw [moved_normalizer_quotient_kernel D e c] at hh
    exact hh.trans inf_le_right
  obtain ⟨τ,ι,hι,hιτ,hact⟩ := exists_local_section_normalizer L W (sourceMovedFixed D) M
    σ π hπ c hLM hNL hNZ hk
  have hLN : L ≤ N := le_inf hLM c.normalized
  have hPW : P ≤ normalizer (W : Set G) := by
    intro p hp
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj p).toMonoidHom = ⁅D.fullModule,L⁆
    have hV : D.fullModule.map (MulAut.conj p).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule (hPM hp))
    have hL : L.map (MulAut.conj p).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (hPL hp)
    rw [map_commutator,hV,hL]
  have hPN : P ≤ N := le_inf (le_inf hPM hPL) hPW
  have hmark (l : L) : τ (q (inclusion hLN l)) = σ (π l) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := c.onto (Multiplicative.ofAdd v)
    exact (hact (inclusion hLN l) w).trans (c.equivariant l w)
  intro a ha
  let aN : N := ⟨a,hPN ha⟩
  have hpow : ∃ k : ℕ, (ι (q aN)) ^ (2 ^ k) = 1 := by
    obtain ⟨k,hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hP) ⟨a,ha⟩
    refine ⟨k,?_⟩
    have hk' : aN ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      exact congrArg (fun x : P => (x : G)) hk
    rw [←map_pow,←map_pow,hk',map_one,map_one]
  obtain ⟨g,hg⟩ := SL2NaturalOffenders.natural_normalizer_two_element_mem_layer
    hn hcard (ι (q aN)) hpow
  have hg' : τ (q aN) = σ g := by
    have hh := congrArg (fun x : (Module.End (ZMod 2) (Fin 2 → F))ˣ => x.val) hg
    exact (LinearMap.ext (fun v => (hιτ (q aN) v).symm)).trans hh.symm
  obtain ⟨l,hl⟩ := hπ g
  have he : q aN = q (inclusion hLN l) := by
    apply hι
    apply Subtype.ext
    apply Units.ext
    calc
      (ι (q aN)).val.val = τ (q aN) := LinearMap.ext (fun v => hιτ (q aN) v)
      _ = σ g := hg'
      _ = σ (π l) := (congrArg σ hl).symm
      _ = τ (q (inclusion hLN l)) := (hmark l).symm
      _ = (ι (q (inclusion hLN l))).val.val := LinearMap.ext (fun v => (hιτ _ v).symm)
  have hc : (a : G) * (l : G)⁻¹ ∈ centralizer (W : Set G) := by
    apply (localNormalizerAction_eq_one_iff W M (aN * (inclusion hLN l)⁻¹)).mp
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hm := (L ⊔ centralizer (W : Set G)).mul_mem
    ((show centralizer (W : Set G) ≤ L ⊔ centralizer (W : Set G) from le_sup_right) hc)
    ((show L ≤ L ⊔ centralizer (W : Set G) from le_sup_left) l.property)
  simpa only [inv_mul_cancel_right] using hm

/-- The same two-actors fix every vector in the original component-fixed kernel. -/
theorem two_subgroup_centralizes_kernel_of_odd_degree
    {n : ℕ} (hn : Odd n) (hcard : Nat.card F = 2 ^ n)
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G)) :
    P ≤ centralizer (sourceMovedFixed D : Set G) := by
  apply (two_subgroup_le_linear_actor_of_odd_degree D e c hn hcard P hP hPM hPL).trans
  exact sup_le (le_centralizer_iff.mp (show sourceMovedFixed D ≤ centralizer (L : Set G) from inf_le_right))
    (centralizer_le inf_le_left)

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
