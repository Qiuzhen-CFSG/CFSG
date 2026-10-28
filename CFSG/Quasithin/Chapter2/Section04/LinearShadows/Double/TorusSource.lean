module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.MarkedSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.TorusGeometrySource

/-!
# The original invariant square torus in the double linear branch

The two actual Borel complements give D=D₁×D₂. The four-member elementary
family controls its outside conjugate; Hall conjugacy and rank-one torus
rigidity make their joint odd Hall group abelian. The strongly quasithin
rank bound and the full square torus order force this group to be D itself.
The original normalizer barrier kills C_R(D), giving Q=U₁U₂ and direct
Sylow factors. Adjusting the marked outside element inside R preserves
both conjugate modules and makes it normalize each torus and Sylow factor.

Source: Aschbacher--Smith, proof of 2.4.7, printed p.540.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearDouble
open ChapterC.Section05.ConjugateSource LinearShadows.Double
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- All torus data on the actual original paired setup, including the
preserved marked conjugate modules and the two normalized cores. -/
structure SourceTorusData {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}
    (c : DoubleLinearSourceSetup d M₀ n) where
  borel : PairedBorelData M ((d.S : Subgroup d.H).map d.H.subtype)
    (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (d.block.map d.H.subtype) c.second d.H n
  x : G
  x_mem : x ∈ M₀
  x_outside : x ∉ (d.S : Subgroup d.H).map d.H.subtype
  geometry : TorusGeometryData c borel x
  first_mark : (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom =
    (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj c.x⁻¹).toMonoidHom
  second_mark : (sourceModule c.second).map (MulAut.conj x⁻¹).toMonoidHom =
    (sourceModule c.second).map (MulAut.conj c.x⁻¹).toMonoidHom
  core_mark : (twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom =
    (twoCore d.H).map (MulAut.conj c.x⁻¹).toMonoidHom
  normalizes_core : borel.torus ≤ normalizer (twoCore d.H : Set G)
  normalizes_opposite : borel.torus ≤ normalizer
    ((twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom : Set G)
  fixed_free : Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
    centralizer (borel.torus : Set G) = ⊥

end CFSG.Quasithin.Chapter2.LinearDouble
namespace CFSG.Quasithin.Chapter2
open LinearDouble LinearShadows.Double ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The full torus producer for the literal double-linear setup has no
independent torus, representation, or classification premise. -/
theorem DoubleLinearSourceSetup.torus_data
    {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀) (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    Nonempty (SourceTorusData c) := by
  obtain ⟨b⟩ := source_borel_torus d hG T hST c hL hSM hMT hi
  obtain ⟨x,hxM,hxS,hxR,hxD,hxU₁,hxU₂,hxQ,hfixed⟩ :=
    source_marked_fixed_free_torus d hG T hM hTM hu hST c hL hSM hMT hi b
  obtain ⟨hb₁,hb₂⟩ := factor_core_central_bounds d hG T hST c
  obtain ⟨a⟩ := source_torus_geometry d hG T hST c hL hSM hMT hi b hfixed hb₁ hb₂
    (source_core_decomposition d hG T hST c) x hxR hxD hxU₁ hxU₂
  have hDL : b.torus ≤ d.L0.map d.H.subtype :=
    (sup_le_sup (b.first.le_intersection.trans inf_le_right)
      (b.second.le_intersection.trans inf_le_right)).trans_eq c.join
  have hDQ : b.torus ≤ normalizer (twoCore d.H : Set G) :=
    hDL.trans ((map_subtype_le _).trans (le_normalizer_twoCore _))
  refine ⟨{
    borel := b
    x := x
    x_mem := hxM
    x_outside := hxS
    geometry := a
    first_mark := hxU₁
    second_mark := hxU₂
    core_mark := hxQ
    normalizes_core := hDQ
    normalizes_opposite := ?_
    fixed_free := hfixed }⟩
  rw [hxQ]
  exact c.normalizes_opposite_core hi b.normalizes_R hDQ

/-- The actual original hypotheses construct both the paired setup and all
of its invariant torus data. -/
theorem MinimalBlockSetup.double_linear_torus_data
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block) {n : ℕ}
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    ∃ c : DoubleLinearSourceSetup d M₀ n, Nonempty (SourceTorusData c) := by
  obtain ⟨c⟩ := d.double_linear_configuration hG T hST.le hpair hL M₀ hSM hMT hi
  exact ⟨c,c.torus_data hG T hM hTM hu hST hL hSM hMT hi⟩

end CFSG.Quasithin.Chapter2
