module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Action
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PGroup.CoprimeFrattiniCommutator

/-!
# Detection and generation on the original Frattini quotient

The actual odd image P is a quotient of X/O₂(X). Its existing projection
to X/O₂,Φ(X) has kernel exactly Φ(P), so a subgroup generating that image
generates P. Original T-irreducibility gives the required image generation
once a nonzero invariant image is known. Coprime Frattini detection proves
that a moved odd-core commutator has nonzero image under this very map.
Source: Aschbacher--Smith, Lemma3.2.13, printed pp.584--585.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
variable {G : Type*} [Group G] {T X : Subgroup G}

@[expose] noncomputable def sourceOddQuotientProjection (hX : X ∈ Chapter1.Xi G T) :
    Chapter1.XiQuotient X →* sourceOddImage hX :=
  QuotientGroup.lift (pCore 2 X) (sourceOddProjection hX) (by
    intro x hx
    apply Subtype.ext
    exact source_twoCore_le_action_kernel hX hx)

theorem sourceOddQuotientProjection_apply (hX : X ∈ Chapter1.Xi G T) (x : X) :
    sourceOddQuotientProjection hX (QuotientGroup.mk' (pCore 2 X) x) =
      sourceOddProjection hX x := rfl

theorem sourceOddQuotientProjection_surjective (hX : X ∈ Chapter1.Xi G T) :
    Function.Surjective (sourceOddQuotientProjection hX) := by
  intro y
  obtain ⟨x, rfl⟩ := sourceOddProjection_surjective hX y
  exact ⟨QuotientGroup.mk' (pCore 2 X) x, rfl⟩

theorem sourceFrattiniProjection_ker_le_frattini (hX : X ∈ Chapter1.Xi G T)
    (hk : SourceKernelInFrattini hX) :
    (sourceFrattiniProjection hX hk).ker ≤ frattini (sourceOddImage hX) := by
  intro y hy
  obtain ⟨x, rfl⟩ := sourceOddProjection_surjective hX y
  change sourceFrattiniProjection hX hk (sourceOddProjection hX x) = 1 at hy
  rw [sourceFrattiniProjection_apply] at hy
  have hx : QuotientGroup.mk' (pCore 2 X) x ∈ frattini (Chapter1.XiQuotient X) :=
    (QuotientGroup.eq_one_iff _).mp hy
  exact frattini_le_comap_frattini_of_surjective
    (φ := sourceOddQuotientProjection hX) (sourceOddQuotientProjection_surjective hX) hx

variable [Finite G]

theorem sourceFrattiniProjection_ker_eq_frattini (hX : X ∈ Chapter1.Xi G T)
    (hk : SourceKernelInFrattini hX) :
    (sourceFrattiniProjection hX hk).ker = frattini (sourceOddImage hX) := by
  apply le_antisymm (sourceFrattiniProjection_ker_le_frattini hX hk)
  obtain ⟨p, hp, _, hq⟩ := hX.odd_quotient
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p (Chapter1.XiQuotient X)) := ⟨hq.isPGroup⟩
  let : IsElementaryAbelian p (Chapter1.XiFrattiniQuotient X) :=
    isElementaryAbelian_quotient_frattini
  let : Fact (IsPGroup p (Chapter1.XiFrattiniQuotient X)) :=
    ⟨IsElementaryAbelian.isPGroup p _⟩
  have he : frattini (Chapter1.XiFrattiniQuotient X) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := p)
  have hh := frattini_le_comap_frattini_of_surjective
    (φ := sourceFrattiniProjection hX hk) (sourceFrattiniProjection_surjective hX hk)
  rw [he] at hh
  exact hh

theorem sourceOddImage_generate_of_frattini_image (hX : X ∈ Chapter1.Xi G T)
    (hk : SourceKernelInFrattini hX) (S : Subgroup (sourceOddImage hX))
    (hS : S.map (sourceFrattiniProjection hX hk) = ⊤) : S = ⊤ := by
  apply frattini_nongenerating
  rw [← sourceFrattiniProjection_ker_eq_frattini hX hk, ← comap_map_eq, hS, comap_top]

theorem sourceOddImage_generate_of_invariant_image (hX : X ∈ Chapter1.Xi G T)
    (hk : SourceKernelInFrattini hX) (S : Subgroup (sourceOddImage hX))
    (hne : S.map (sourceFrattiniProjection hX hk) ≠ ⊥)
    (hinv : ∀ t : T, ∀ a ∈ S.map (sourceFrattiniProjection hX hk),
      Chapter1.xiFrattiniAction T X hX.invariant t a ∈
        S.map (sourceFrattiniProjection hX hk)) : S = ⊤ := by
  apply sourceOddImage_generate_of_frattini_image hX hk S
  exact (hX.irreducible _ hinv).resolve_left hne

theorem source_moved_frattini_image_ne_bot (hX : X ∈ Chapter1.Xi G T)
    (hk : SourceKernelInFrattini hX)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X))
    (A : Subgroup (sourceActionGroup hX)) (hA : IsPGroup 2 A)
    (hm : ⁅sourceOddImage hX, A⁆ ≠ ⊥) :
    (⁅sourceOddImage hX, A⁆.subgroupOf (sourceOddImage hX)).map
      (sourceFrattiniProjection hX hk) ≠ ⊥ := by
  intro he
  let P := sourceOddImage hX
  let := sourceOddImage_normal hX
  apply hm
  apply commutator_eq_bot_of_le_frattini_of_isPGroup (p := 5) (q := 2)
    (by decide) P A (sourceOddImage_isPGroup hX hp) hA le_normalizer_of_normal
  intro d hd
  have hdP : d ∈ P := commutator_le_left P A hd
  have hz : sourceFrattiniProjection hX hk (⟨d, hdP⟩ : P) = 1 := by
    have hh := mem_map_of_mem (sourceFrattiniProjection hX hk)
      (show (⟨d, hdP⟩ : P) ∈ ⁅P, A⁆.subgroupOf P from hd)
    rw [he] at hh
    exact hh
  exact mem_map_of_mem P.subtype (sourceFrattiniProjection_ker_le_frattini hX hk hz)

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
