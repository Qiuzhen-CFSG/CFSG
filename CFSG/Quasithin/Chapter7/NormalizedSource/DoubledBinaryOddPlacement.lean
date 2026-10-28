module
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.Basic
public import Theory.GroupTheory.PerfectNormalizerInner.SimpleSection
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.Representation.PSL3Two.NaturalDualNonFF
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank

/-!
# The actual binary-three residual at a moved odd-local component

A noninner action of the perfect residual retains SL₃(2) as an actual
section of the component's outer automorphism group. Central descent and
the proved shared C, alternating and odd PSL₂ automorphism calculations
exclude those model rows. In the inner branch, the entire central kernel
of the residual's embedding lies in its original two-core.

The chosen-module application in `NonFFSourceDoubledBinaryOddPlacement`
uses this kernel to retain the residual's simple section in the component
central quotient. No complete Theorem B Schreier input is assumed.
Source: Aschbacher–Smith 4.4.10–12, printed pp.621–622, in the proof of
7.3.4 and 7.6.1, printed pp.699,702, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddPlacement
open ChapterA.Section02 ChapterA.Section03.SourceComponents
open BinaryLinearThree

private instance : IsSimpleGroup BinaryLinearThree.Group := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup

private instance : _root_.Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)

/-- A nontrivial outer image of a perfect binary-three cover retains the
actual simple quotient as a section. -/
theorem inner_or_outer_section {N : Type*} [_root_.Group N] [Finite N]
    (K R : Subgroup N) [_root_.Group.IsPerfect R]
    (q : R →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (hn : R ≤ normalizer (K : Set N)) :
    R ≤ K ⊔ centralizer (K : Set N) ∨
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
        Function.Surjective f := by
  by_cases he : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f
  · exact Or.inr he
  · let : _root_.Group.IsNilpotent q.ker := hk.isNilpotent
    exact Or.inl (perfect_le_sup_centralizer_of_no_simple_outer_section K R q hq
      (fun U f hf => he ⟨U,f,hf⟩) hn)

/-- Shared C rows, all alternating rows and odd PSL₂ rows have no such
outer section, including for a nontrivial perfect central cover. -/
theorem outer_section_exclusions {K : Type*} [_root_.Group K] [Finite K]
    [IsQuasisimple K]
    (he : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) :
    ¬ IsTheoremCModel (K ⧸ center K) ∧
    (∀ n : ℕ, ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin n))) ∧
    ∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : _root_.Group.IsPerfect (K ⧸ center K) :=
    _root_.Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  have hn := _root_.Group.IsPerfect.not_isMulCommutative (K ⧸ center K)
  have hbad (hs : _root_.Group.IsSolvable (MulAut.Outer (K ⧸ center K))) : False := by
    let := hs
    let : _root_.Group.IsSolvable (MulAut.Outer K) :=
      _root_.Group.isSolvable_of_isSolvable_injective
        (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
    obtain ⟨U,f,hf⟩ := he
    exact _root_.Group.IsPerfect.not_isSolvable BinaryLinearThree.Group
      (_root_.Group.isSolvable_of_surjective hf)
  exact ⟨fun hm => hbad (TheoremBOuter.of_theoremC hn hm),
    fun n hm => hbad (TheoremBOuter.alternating hn hm),
    fun q ho hm => hbad (TheoremBOuter.linear_two_odd hn ho hm)⟩

/-- The whole center of a containing group is killed by the actual simple
two-core quotient. This retains the original central covering kernel. -/
theorem central_kernel_le_twoCore {R K : Type*} [_root_.Group R] [Finite R] [_root_.Group K]
    (e : (R ⧸ pCore 2 R) ≃* BinaryLinearThree.Group)
    (j : R →* K) (hj : Function.Injective j) :
    ((QuotientGroup.mk' (center K)).comp j).ker ≤ pCore 2 R := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  intro x hx
  have hc : j x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcx : x ∈ center R := mem_center_iff.mpr (fun y => hj (by
    simpa only [map_mul] using mem_center_iff.mp hc (j y)))
  have hqx : q x ∈ center BinaryLinearThree.Group := mem_center_iff.mpr (by
    intro y
    obtain ⟨z,rfl⟩ := hq y
    simpa only [map_mul] using congrArg q (mem_center_iff.mp hcx z))
  have hz : center BinaryLinearThree.Group = ⊥ :=
    Matrix.PSL3Two.center_eq_bot
  have he : q x = 1 := by simpa only [hz,mem_bot] using hqx
  exact (QuotientGroup.eq_one_iff x).mp (e.injective (he.trans (map_one e).symm))

/-- Either actual outcome excludes all odd PSL₂ components and both
prime-field degree-three rows. In the inner case this uses the whole
six-space; in the outer case it uses the proved automorphism calculations. -/
theorem small_model_exclusions {K : Type*} [_root_.Group K] [Finite K] [IsQuasisimple K]
    (hc : 6 ≤ primeRank 2 (K ⧸ center K) ∨
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
        Function.Surjective f) :
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q) ∧
    ∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 p) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 p) := by
  rcases hc with hr | he
  · refine ⟨fun q ho hm => ?_, fun p hp ho => ⟨?_,?_⟩⟩
    · have := odd_psl_two_twoRank_le_two ho hm
      omega
    · intro hm
      have := odd_psl_three_twoRank_le_two ho hm
      omega
    · intro hm
      have := odd_psu_three_twoRank_le_two ho hm
      omega
  · obtain ⟨hC,_,h2⟩ := outer_section_exclusions he
    exact ⟨h2, fun p hp ho =>
      ⟨fun hm => hC (.odd (.linear_three p hp ho hm)),
        fun hm => hC (.odd (.unitary_three p hp ho hm))⟩⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddPlacement
