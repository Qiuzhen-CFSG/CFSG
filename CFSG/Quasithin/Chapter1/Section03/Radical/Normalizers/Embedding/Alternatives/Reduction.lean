module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.Models

/-!
# Elimination of the twenty-two embedding alternatives

The smaller group is perfect. In every ordinary proper case except (10),
its quotient by the two-core is quasisimple; this includes the nonsplit
extensions whose kernels are proved to be two-groups. The last two cases
put any solvable normal two-perfect marked subgroup inside the embedded
solvable radical, by the odd-core arguments. Thus a marked subgroup outside
that radical leaves precisely case (10).

The actual normalizer setup and the universal A.3.6 input are connected in
the parent Alternatives module. This lemma uses the intrinsic subgroup
inclusions, without assuming injectivity of any ambient quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.12, printed pp.47–48, and the proof of 1.3.8, printed p.513.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter1.RadicalNormalizers
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
universe u
variable {A : Type u} [Group A] [Finite A]

/-- The full A.3.12 list reduces to (10) under the marked radical obstruction. -/
theorem case_ten_of_embedding {X B K : Subgroup A} [Group.IsPerfect B]
    [Group.IsSolvable X] (hBK : B < K) (hXB : X ≤ B)
    (hXnormal : (X.subgroupOf B).Normal) (hXp : IsPPerfect 2 X)
    (hXrad : ¬ X ≤ (solvableRadical K).map K.subtype)
    (hB : ¬ IsQuasisimple (B ⧸ pCore 2 B)) (hcommon : A36Common K)
    (hemb : A312Embedding B K) :
    ∃ s : ℕ, s.Prime ∧ Odd s ∧ 3 < s ∧
      HasExtension B (ElementaryModel s 2) (fun U _ => IsSL U 2 s) ∧
      (ClassicalGroup.IsPSL K 3 s ∨ IsSL K 3 s) := by
  have hnot (h : IsQuasisimple B) : False := hB (core_quasisimple h)
  cases hemb with
  | one he => exact (hBK.ne he).elim
  | two n hn hs _ _ =>
      exact (hB (psl_quasisimple hs (.inr ⟨rfl,
        (show 4 = 2 ^ 2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn)⟩))).elim
  | three m hm hs _ _ => exact (hB (suzuki_quasisimple hs hm)).elim
  | four hs _ _ => exact (hB (psl_quasisimple hs (.inl (by decide)))).elim
  | five hs _ _ => exact (hB (psl_quasisimple hs (.inl (by decide)))).elim
  | six hs _ =>
      rcases hs with h | h
      · exact (hnot (alternating_quasisimple h (by decide))).elim
      · exact (hnot (psl_quasisimple h (.inl (by decide)))).elim
  | seven hs =>
      rcases hs with ⟨h, _⟩ | ⟨h, _⟩
      · exact (hnot (alternating_quasisimple h (by decide))).elim
      · exact (hnot h.1).elim
  | eight hs =>
      rcases hs with ⟨p, _, _, hp, h, _⟩ | ⟨p, _, h, _⟩
      · exact (hnot (psl_quasisimple h (.inr ⟨rfl, hp⟩))).elim
      · exact (hnot (alternating_quasisimple h (by decide))).elim
  | nine hs =>
      rcases hs with ⟨p, _, _, _, hp, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact (hnot (slTwo_quasisimple h hp)).elim
      · exact (hnot (alternating_quasisimple h (by decide))).elim
      · exact (hnot h.1).elim
  | ten p hp ho hl hs hk => exact ⟨p, hp, ho, hl, hs, hk⟩
  | eleven hs _ => exact (hnot (alternating_quasisimple hs (by decide))).elim
  | twelve hs =>
      exfalso
      rcases hs with ⟨h, _⟩ | ⟨h, _⟩
      · apply hB (extension_core_quasisimple h (fun _ _ h => elementary_twoGroup h) ?_)
        intro U _ _ h
        exact h.elim (fun h => alternating_quasisimple h (by decide))
          (fun h => alternating_quasisimple h (by decide))
      · apply hB (extension_core_quasisimple h (fun _ _ h => elementary_twoGroup h) ?_)
        intro U _ _ h
        exact h.elim (fun h => alternating_quasisimple h (by decide)) And.left
  | thirteen _ hs =>
      exfalso
      rcases hs with h | h | h | h
      · exact hnot (m22_quasisimple h)
      · exact hnot (psl_quasisimple h (.inl (by decide)))
      · apply hB (extension_core_quasisimple h (fun _ _ h => elementary_twoGroup h) ?_)
        intro U _ _ h
        rcases h with h | h | h | h
        · exact alternating_quasisimple h (by decide)
        · exact psl_quasisimple h (.inl (by decide))
        · exact alternating_quasisimple h (by decide)
        · exact alternating_quasisimple h (by decide)
      · exact hB (extension_core_quasisimple h (fun _ _ h => elementary_twoGroup h)
          (fun _ _ _ h => psl_quasisimple h (.inl (by decide))))
  | fourteen _ hs =>
      exfalso
      rcases hs with h | h | h
      · exact hB (extension_core_quasisimple h (fun _ _ h => elementary_twoGroup h)
          (fun _ _ _ h => psl_quasisimple h (.inl (by decide))))
      · apply hB (extension_core_quasisimple h (fun _ _ h => elementary_twoGroup h) ?_)
        intro U _ _ h
        exact h.elim (fun h => psl_quasisimple h (.inl (by decide))) And.left
      · exact hB (extension_core_quasisimple h (fun _ _ h => extraspecial_twoGroup h)
          (fun _ _ _ h => psl_quasisimple h (.inl (by decide))))
  | fifteen hs _ => exact (hnot (alternating_quasisimple hs (by decide))).elim
  | sixteen hs _ =>
      exact (hB (extension_core_quasisimple hs (fun _ _ h => extraspecial_twoGroup h)
        (fun _ _ _ h => alternating_quasisimple h (by decide)))).elim
  | seventeen _ hs =>
      exfalso
      rcases hs with h | h | h | h | h | h
      · exact hB (extension_core_quasisimple h (fun _ _ h => extraspecial_twoGroup h)
          (fun _ _ _ h => h.1))
      · exact hB (extension_core_quasisimple h (fun _ _ h => elementary_twoGroup h)
          (fun _ _ _ h => m24_quasisimple h))
      · exact hB (alternating_quasisimple h (by decide))
      · exact hB h.1
      · exact hB (psl_quasisimple h (.inl (by decide)))
      · exact hB (psl_quasisimple h (.inl (by decide)))
  | eighteen _ hs =>
      exfalso
      rcases hs with h | h
      · exact hB (extension_core_quasisimple h (fun _ _ h => cyclicFourProduct_twoGroup h)
          (fun _ _ _ h => alternating_quasisimple h (by decide)))
      · exact hB (extension_core_quasisimple h (fun _ _ h => fourCube_twoGroup h)
          (fun _ _ _ h => psl_quasisimple h (.inl (by decide))))
  | nineteen _ hs =>
      exfalso
      rcases hs with h | h
      · exact hB (extension_core_quasisimple h (fun _ _ h => extraspecial_twoGroup h)
          (fun _ _ _ h => psl_quasisimple h (.inl (by decide))))
      · exact hB (extension_core_quasisimple h (fun _ _ h => elementary_twoGroup h)
          (fun _ _ _ h => h.1))
  | twenty _ hs _ =>
      exfalso
      exact hs.elim (fun h => hB (alternating_quasisimple h (by decide)))
        (fun h => hB (psl_quasisimple h (.inl (by decide))))
  | twenty_one _ _ _ _ hgen _ =>
      exact (hXrad (embedded_radical_of_cover hcommon hXB hBK.le hXnormal hgen)).elim
  | twenty_two _ _ _ _ himage =>
      exact (hXrad (embedded_radical_of_slFive_image hcommon hXB hBK.le hXnormal
        hXp himage)).elim
end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
