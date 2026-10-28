module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.WordChecks.Tables

/-!
# The thirteen J₂ normalizer checks

For each of the seven fixed subgroup generators and the first six representatives,
we check the images of all six radical generators under conjugation in both
directions. Each image is an explicit word in the radical generators and their
inverses. Closure then gives membership in the actual subgroup normalizer.

The words are transcribed from `../source/normalizer-words.json`, with positive
letters 0–5 and inverse letters 6–11. These are witness data, not assumed facts.
Source: Aschbacher–Smith, proof of 1.3.4, printed p.511/PDF p.528, and GLS3
Table 5.3g; the underlying ATLAS attribution is retained with the carrier.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.WordChecks
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open GeneratorPair GeneratorPair.SecondOrbitCertificate Theory.GroupTheory
open Theory.GroupTheory.SubgroupEnumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

/-- The seven subgroup generators followed by representatives 0–5. -/
def normalizerElement (i : Fin 13) : Carrier :=
  if h : i.val < 7 then Seed.sGenerator ⟨i.val, h⟩
  else representative ⟨i.val - 7, by omega⟩

def normalizerTable (i : Fin 13) : Equiv.Perm (Fin 100) :=
  if h : i.val < 7 then sTable ⟨i.val, h⟩
  else repTable ⟨i.val - 7, by omega⟩

def conjugator (i : Fin 13) (d : Fin 2) : Carrier :=
  if d = 0 then normalizerElement i else (normalizerElement i)⁻¹

def conjugatorTable (i : Fin 13) (d : Fin 2) : Equiv.Perm (Fin 100) :=
  if d = 0 then normalizerTable i else (normalizerTable i)⁻¹

/-- Signed letters in the six retained radical generators. -/
def qLetter (j : Fin 12) : Carrier :=
  if h : j.val < 6 then Seed.q₂Generator ⟨j.val, h⟩
  else (Seed.q₂Generator ⟨j.val - 6, by omega⟩)⁻¹

def qLetterTable (j : Fin 12) : Equiv.Perm (Fin 100) :=
  if h : j.val < 6 then qTable ⟨j.val, h⟩
  else (qTable ⟨j.val - 6, by omega⟩)⁻¹

/-- The retained conjugation words, in the same representative numbering. -/
def conjugationWords (i : Fin 13) (d : Fin 2) (j : Fin 6) : List (Fin 12) :=
  (#[
    [11, 9, 6, 9],
    [8, 7, 8],
    [8],
    [3],
    [10],
    [11],
    [11, 9, 6, 9],
    [8, 7, 8],
    [8],
    [3],
    [10],
    [11],
    [6],
    [7],
    [4, 2],
    [9, 10],
    [10],
    [11],
    [6],
    [7],
    [4, 2],
    [9, 10],
    [10],
    [11],
    [6],
    [7],
    [8],
    [4, 3],
    [10],
    [11],
    [6],
    [7],
    [8],
    [4, 3],
    [10],
    [11],
    [11, 8, 9, 6, 9],
    [9, 7, 8],
    [2],
    [3],
    [11, 10],
    [11],
    [11, 8, 9, 6, 9],
    [9, 7, 8],
    [2],
    [3],
    [11, 10],
    [11],
    [9, 6, 9],
    [11, 7],
    [8],
    [9],
    [10],
    [11],
    [9, 6, 9],
    [11, 7],
    [8],
    [9],
    [10],
    [11],
    [8, 9, 6, 9],
    [8, 9, 7],
    [2],
    [9],
    [11, 10],
    [11],
    [8, 9, 6, 9],
    [8, 9, 7],
    [2],
    [9],
    [11, 10],
    [11],
    [6],
    [7],
    [2],
    [3],
    [10],
    [11],
    [6],
    [7],
    [2],
    [3],
    [10],
    [11],
    [6],
    [7],
    [2],
    [3],
    [10],
    [11],
    [6],
    [7],
    [2],
    [3],
    [10],
    [11],
    [11, 8, 6, 7, 8],
    [11, 6],
    [8, 6, 9],
    [1, 0, 2],
    [11, 10],
    [10],
    [8, 7, 8],
    [11, 6, 7],
    [3, 0],
    [2, 1, 0, 3],
    [11],
    [11, 10],
    [8, 9, 6, 9],
    [11, 9, 7, 8],
    [6, 7, 8],
    [11, 9, 7],
    [11],
    [10],
    [11, 9, 6, 7],
    [8, 6],
    [1, 3],
    [8, 9, 6],
    [11],
    [10],
    [9, 6, 7],
    [11, 8, 6],
    [3],
    [3, 2],
    [11, 10],
    [11],
    [8, 9, 7],
    [8, 9, 6, 7, 8],
    [3, 2],
    [2],
    [11, 10],
    [11],
    [8, 7, 8],
    [8, 6, 7, 8],
    [8, 9],
    [8, 10],
    [10],
    [11],
    [11, 6, 7],
    [9, 6, 9],
    [9, 10],
    [4, 3, 2],
    [10],
    [11],
    [6],
    [11, 7],
    [11, 9, 7],
    [11, 8, 6, 9],
    [11, 10],
    [10],
    [6],
    [8, 7, 8],
    [9, 6, 7, 8],
    [7, 8],
    [11],
    [11, 10]
  ] : Array (List (Fin 12)))[(i.val * 2 + d.val) * 6 + j.val]!

theorem normalizer_eq (i : Fin 13) :
    inclusion (normalizerElement i) = normalizerTable i := by
  unfold normalizerElement normalizerTable
  split
  · exact s_eq _
  · exact rep_eq _

theorem conjugator_eq (i : Fin 13) (d : Fin 2) :
    inclusion (conjugator i d) = conjugatorTable i d := by
  unfold conjugator conjugatorTable
  split
  · exact normalizer_eq i
  · rw [map_inv, normalizer_eq]

theorem qLetter_eq (j : Fin 12) : inclusion (qLetter j) = qLetterTable j := by
  unfold qLetter qLetterTable
  split
  · exact q_eq _
  · rw [map_inv, q_eq]

/-- All 156 permutation identities, checked at every point. -/
theorem conjugation_tables : ∀ i d j x,
    (conjugatorTable i d * qTable j * (conjugatorTable i d)⁻¹) x =
      wordMap (fun k => qLetterTable k) (conjugationWords i d j) x := by
  apply allFin
  decide +kernel

/-- Each displayed word is the conjugate in the actual J₂ carrier. -/
theorem conjugation_word (i : Fin 13) (d : Fin 2) (j : Fin 6) :
    conjugator i d * Seed.q₂Generator j * (conjugator i d)⁻¹ =
      evalWord qLetter (conjugationWords i d j) := by
  apply inclusion_injective
  simp only [map_mul, map_inv, conjugator_eq, q_eq, map_evalWord]
  simp only [qLetter_eq]
  apply Equiv.ext
  intro x
  rw [evalWord_apply _ _ (fun _ _ => rfl)]
  exact conjugation_tables i d j x

private theorem qLetter_mem (j : Fin 12) : qLetter j ∈ Seed.q₂ := by
  unfold qLetter
  split
  · exact Subgroup.subset_closure ⟨_, rfl⟩
  · exact Seed.q₂.inv_mem (Subgroup.subset_closure ⟨_, rfl⟩)

private theorem conjugate_generator_mem (i : Fin 13) (d : Fin 2) (j : Fin 6) :
    conjugator i d * Seed.q₂Generator j * (conjugator i d)⁻¹ ∈ Seed.q₂ := by
  rw [conjugation_word]
  exact evalWord_mem qLetter Seed.q₂ qLetter_mem _

private theorem conjugate_mem (g : Carrier)
    (h : ∀ j, g * Seed.q₂Generator j * g⁻¹ ∈ Seed.q₂) :
    ∀ y ∈ Seed.q₂, g * y * g⁻¹ ∈ Seed.q₂ := by
  have hle : Seed.q₂ ≤ Seed.q₂.comap (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact h j
  exact fun _ hy => hle hy

/-- Each of the thirteen elements normalizes the generated radical subgroup. -/
theorem normalizerElement_mem (i : Fin 13) : normalizerElement i ∈ Seed.p₂ := by
  change normalizerElement i ∈ Subgroup.normalizer (Seed.q₂ : Set Carrier)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hf : ∀ j, normalizerElement i * Seed.q₂Generator j *
      (normalizerElement i)⁻¹ ∈ Seed.q₂ := by
    simpa only [conjugator, if_pos rfl, if_true] using conjugate_generator_mem i 0
  have hb : ∀ j, (normalizerElement i)⁻¹ * Seed.q₂Generator j *
      ((normalizerElement i)⁻¹)⁻¹ ∈ Seed.q₂ := by
    simpa only [conjugator, show (1 : Fin 2) ≠ 0 by decide, if_false]
      using conjugate_generator_mem i 1
  constructor
  · exact conjugate_mem _ hf y
  · intro hy
    have h := conjugate_mem _ hb _ hy
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using h

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.WordChecks
