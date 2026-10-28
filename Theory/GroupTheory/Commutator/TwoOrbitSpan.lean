module

public import Theory.GroupTheory.Commutator.ConjugateGeneration
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.Frattini.SquareImage
public import Mathlib.GroupTheory.Abelianization.Defs
/-!
# Derived and Frattini subgroups of a two-orbit elementary span

Let U be normal in Q and let L normalize Q. Suppose the L-conjugates of U
consist of U and the P-conjugates of a second L-conjugate A, where P ≤ L
normalizes U. Then every pair commutator of conjugates lies in the L-span
of [U,A]. Q normalizes this span, so it equals the derived subgroup of
the U-span. If U has exponent two and the span is a finite two-group,
its abelianization also has exponent two, giving Frattini = derived.

Source: the group-theoretic argument in Aschbacher–Smith 14.7.13(4), p.1046.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup.TwoOrbitSpan
variable {G : Type*} [Group G]

theorem normalizes_conjugate (U L Q : Subgroup G) (hQU : Q ≤ normalizer U)
    (hLQ : L ≤ normalizer Q) (l : L) : Q ≤ normalizer (U.conjBy (l : G)) := by
  have hm := (map_mono (f := (MulAut.conj (l : G)).toMonoidHom) hQU).trans
    (U.le_normalizer_map (MulAut.conj (l : G)).toMonoidHom)
  have he : Q.map (MulAut.conj (l : G)).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (hLQ l.property)
  rwa [he] at hm

theorem normalizes_span (U L Q : Subgroup G) (hQU : Q ≤ normalizer U)
    (hLQ : L ≤ normalizer Q) : Q ≤ normalizer (conjugateSpanBy U L) := by
  rw [conjugateSpanBy_eq_iSup_conj]
  exact (le_iInf (normalizes_conjugate U L Q hQU hLQ)).trans
    (iInf_normalizer_le_normalizer_iSup _)

theorem commutator_iSup_le {ι : Type*} (C : ι → Subgroup G) (Q B : Subgroup G)
    (hCQ : ∀ i, C i ≤ Q) (hQB : Q ≤ normalizer B)
    (hp : ∀ i j, ⁅C i,C j⁆ ≤ B) : ⁅⨆ i,C i,⨆ i,C i⁆ ≤ B := by
  have hsingle (i) : ⁅C i,⨆ j,C j⁆ ≤ B := by
    rw [commutator_comm]
    have hpre : (⨆ j,C j) ≤ commutatorPreimage Q (C i) B :=
      iSup_le fun j => le_commutatorPreimage (hCQ j) (hp j i)
    exact (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le Q _ B hQB)
  have hpre : (⨆ i,C i) ≤ commutatorPreimage Q (⨆ i,C i) B :=
    iSup_le fun i => le_commutatorPreimage (hCQ i) (hsingle i)
  exact (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le Q _ B hQB)

theorem derived_span (U A L P Q : Subgroup G)
    (hUQ : U ≤ Q) (hQU : Q ≤ normalizer U) (hLQ : L ≤ normalizer Q)
    (hPU : P ≤ normalizer U) (hPL : P ≤ L)
    (hUU : ⁅U,U⁆ = ⊥) (hA : ∃ a : L, A = U.conjBy (a : G))
    (hcover : ∀ l : L, U.conjBy (l : G) = U ∨
      ∃ p : P, U.conjBy (l : G) = A.conjBy (p : G)) :
    ⁅conjugateSpanBy U L,conjugateSpanBy U L⁆ = conjugateSpanBy ⁅U,A⁆ L := by
  let B := conjugateSpanBy ⁅U,A⁆ L
  have hLB : L ≤ normalizer B := le_normalizer_conjugateSpanBy _ _
  have hUA (l : L) : ⁅U,U.conjBy (l : G)⁆ ≤ B := by
    rcases hcover l with hh | ⟨p,hh⟩
    · rw [hh,hUU]; exact bot_le
    · have hm : ⁅U,A.conjBy (p : G)⁆ = (⁅U,A⁆).conjBy (p : G) := by
        change ⁅U,A.map _⁆ = (⁅U,A⁆).map _
        have he : U.map (MulAut.conj (p : G)).toMonoidHom = U :=
          mem_normalizer_iff_map_conj_eq.mp (hPU p.property)
        rw [map_commutator,he]
      rw [hh,hm]
      change (⁅U,A⁆).map _ ≤ B
      rw [←mem_normalizer_iff_map_conj_eq.mp (hLB (hPL p.property))]
      exact map_mono (le_conjugateSpanBy _ _)
  have hp (l k : L) : ⁅U.conjBy (l : G),U.conjBy (k : G)⁆ ≤ B := by
    have hh := map_mono (f := (MulAut.conj (l : G)).toMonoidHom) (hUA (l⁻¹*k))
    change (⁅U,U.conjBy ((l : G)⁻¹*(k : G))⁆).conjBy (l : G) ≤ B.conjBy (l : G) at hh
    change ⁅U.conjBy (l : G),U.conjBy (k : G)⁆ ≤ B
    change (⁅U,U.conjBy ((l : G)⁻¹*(k : G))⁆).map _ ≤ B.map _ at hh
    rw [map_commutator] at hh
    change ⁅U.conjBy (l : G),(U.conjBy ((l : G)⁻¹*(k : G))).conjBy (l : G)⁆ ≤
      B.conjBy (l : G) at hh
    rw [conjBy_conjBy,mul_inv_cancel_left] at hh
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp (hLB l.property))
  have hQA : Q ≤ normalizer A := by
    obtain ⟨a,rfl⟩ := hA
    exact normalizes_conjugate U L Q hQU hLQ a
  have hQB : Q ≤ normalizer B := by
    apply normalizes_span _ _ _ _ hLQ
    intro q hq
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hQU hq),
      mem_normalizer_iff_map_conj_eq.mp (hQA hq)]
  apply le_antisymm
  · rw [conjugateSpanBy_eq_iSup_conj]
    exact commutator_iSup_le _ Q B (fun l => by
      rw [←mem_normalizer_iff_map_conj_eq.mp (hLQ l.property)]
      exact map_mono hUQ) hQB hp
  · apply conjugateSpanBy_le
    · apply commutator_mono (le_conjugateSpanBy _ _)
      obtain ⟨a,rfl⟩ := hA
      rw [conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun t : L => U.map (MulAut.conj (t : G)).toMonoidHom) a
    · intro l hl
      rw [mem_normalizer_iff_map_conj_eq,map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy U L hl)]

variable [Finite G]
theorem frattini_span (U L : Subgroup G) (hp : IsPGroup 2 (conjugateSpanBy U L))
    (hsq : ∀ u ∈ U, u^2=1) :
    (frattini (conjugateSpanBy U L)).map (conjugateSpanBy U L).subtype =
      ⁅conjugateSpanBy U L,conjugateSpanBy U L⁆ := by
  let S := conjugateSpanBy U L
  let f : S →* Abelianization S := Abelianization.of
  let g : S →* Abelianization S := (powMonoidHom 2).comp f
  have hgen : S ≤ g.ker.map S.subtype := by
    apply (closure_le _).mpr
    rintro x ⟨l,hl,u,hu,rfl⟩
    have hx : l*u*l⁻¹ ∈ S := subset_closure ⟨l,hl,u,hu,rfl⟩
    refine ⟨⟨l*u*l⁻¹,hx⟩,?_,rfl⟩
    change f ⟨l*u*l⁻¹,hx⟩ ^2 =1
    rw [←map_pow]
    have hh : (⟨l*u*l⁻¹,hx⟩ : S)^2=1 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_pow,Subgroup.coe_one,←MulAut.conj_apply,←map_pow,map_one] using
        congrArg (MulAut.conj l) (hsq u hu)
    rw [hh,map_one]
  have hsqf (x:S) : f x ^2=1 := by
    obtain ⟨y,hy,he⟩ := hgen x.property
    have hh : y=x := Subtype.ext he
    exact hh ▸ hy
  have hPhi : frattini S ≤ _root_.commutator S := by
    have hh := Theory.GroupTheory.frattini_le_ker_of_square_image f hsqf
    simpa only [f,Abelianization.ker_of] using hh
  let : Fact (IsPGroup 2 S) := ⟨hp⟩
  have he : frattini S = _root_.commutator S :=
    le_antisymm hPhi (commutator_le_frattini_of_isPGroup (p := 2))
  change (frattini S).map S.subtype = ⁅S,S⁆
  rw [he,map_subtype_commutator]
end Subgroup.TwoOrbitSpan
