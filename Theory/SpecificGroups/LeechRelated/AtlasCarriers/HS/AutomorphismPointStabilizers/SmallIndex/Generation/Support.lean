module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Elementary
import Mathlib.Tactic.FinCases

/-!
# Words for conjugate-pair generation in the auxiliary HS stabilizer

The two fixed generators are recovered by words in each conjugate pair.
All supplied permutation identities are checked by kernel reduction.
Source context: GLS3 Table 5.3m, p.274; Aschbacher–Smith p.510.
The discovery scripts are original CFSG code; the ATLAS permutation attribution
is retained in `HS.lean`. No computational output is used as an axiom.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
open Theory.GroupTheory Subgroup
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signed (a b : CertifiedStabilizer) (j : Fin 4) : CertifiedStabilizer :=
  match j.val with
  | 0 => a
  | 1 => a⁻¹
  | 2 => b
  | _ => b⁻¹

def conjugateElement (i : Fin 150) : CertifiedStabilizer :=
  representative i * elevenElement * (representative i)⁻¹

def pairSubgroup (i : Fin 150) : Subgroup CertifiedStabilizer :=
  primeSubgroup ⊔ primeSubgroup.map (MulAut.conj (representative i)).toMonoidHom

def pairWord (i : Fin 150) (w : List (Fin 4)) : CertifiedStabilizer :=
  evalWord (signed elevenElement (conjugateElement i)) w

def basisWord (w : List (Fin 4)) : CertifiedStabilizer :=
  evalWord (signed (generator 0) (generator 1)) w

theorem eval_mem (K : Subgroup CertifiedStabilizer) (a b : CertifiedStabilizer)
    (ha : a ∈ K) (hb : b ∈ K) (w : List (Fin 4)) :
    evalWord (signed a b) w ∈ K := by
  have hs : ∀ j, signed a b j ∈ K := by
    intro j
    fin_cases j
    · exact ha
    · exact K.inv_mem ha
    · exact hb
    · exact K.inv_mem hb
  induction w with
  | nil => exact K.one_mem
  | cons j w ih => exact K.mul_mem (hs j) ih

theorem pairWord_mem (i : Fin 150) (w : List (Fin 4)) : pairWord i w ∈ pairSubgroup i := by
  apply eval_mem
  · exact (le_sup_left : primeSubgroup ≤ pairSubgroup i) (Subgroup.mem_zpowers elevenElement)
  · exact (le_sup_right : primeSubgroup.map (MulAut.conj (representative i)).toMonoidHom ≤ pairSubgroup i) (Subgroup.mem_map.mpr
      ⟨elevenElement, Subgroup.mem_zpowers elevenElement, rfl⟩)

def basisRecoveryWord (i : Fin 17) : List (Fin 4) :=
  match i.val with
  | 0 => [1]
  | 1 => [2]
  | 2 => [3]
  | 3 => [2, 2, 1, 3, 3, 3, 3, 1, 3, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 3, 1]
  | 4 => [0, 2, 2, 2, 2, 0, 2, 2, 2, 0, 2, 2, 2, 2, 0, 2, 2, 2, 2, 0, 3, 3]
  | 5 => [3, 3, 1, 2, 2, 2, 0, 2, 2, 2]
  | 6 => [3, 3, 3, 1, 3, 3, 3, 0, 2, 2]
  | 7 => [1, 2, 2, 1, 2, 2, 0, 3, 3, 0, 2, 2, 0, 3, 3, 3, 0, 3, 3, 0, 2, 2, 0, 3, 0, 2, 1, 2, 1, 2, 2, 2, 1]
  | 8 => [0, 3, 3, 3, 0, 3, 0, 3, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 1, 3, 3, 0, 3, 3, 0]
  | 9 => [2, 2, 1, 3, 1, 3, 3, 3, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 0, 2, 2, 2, 2, 2, 2, 0, 3, 3, 0]
  | 10 => [1, 2, 2, 1, 3, 3, 3, 3, 3, 3, 1, 3, 0, 3, 3, 0, 2, 2, 0, 3, 0, 2, 2, 2, 0, 2, 0, 3, 3]
  | 11 => [1, 2, 2, 1, 3, 3, 1, 2, 0, 3, 3, 0, 2, 2, 0, 3, 0, 2, 2, 1, 2, 0, 2, 0, 2, 2, 2, 2]
  | 12 => [3, 3, 3, 3, 1, 3, 1, 3, 0, 3, 3, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 0, 2, 2, 0, 3, 3, 0]
  | 13 => [3, 3, 1, 2, 2, 1, 3, 3, 3, 3, 1, 2, 0, 2, 0, 2, 0, 3, 0, 2, 0, 3, 3, 0, 2, 2, 0, 3, 0, 2]
  | 14 => [3, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 0, 2, 2, 2, 2, 0, 3, 3, 0, 2, 2]
  | 15 => [0, 2, 0, 2, 0, 3, 0, 2, 0, 3, 0, 3, 3, 0, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 0, 3, 3]
  | _ => [2, 2, 1, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1]

theorem basisRecovery : ∀ j, basisWord (basisRecoveryWord j) = generator j := by
  have h : ∀ j : Fin 17, ∀ x : Fin 100,
      (basisWord (basisRecoveryWord j) : Equiv.Perm (Fin 100)) x =
        (generator j : Equiv.Perm (Fin 100)) x := by
    apply OrderCertificate.allFin
    decide +kernel
  intro j
  exact Subtype.ext (Equiv.ext (h j))

theorem eq_top_of_generators (K : Subgroup CertifiedStabilizer)
    (h0 : generator 0 ∈ K) (h1 : generator 1 ∈ K) : K = ⊤ := by
  have hgen (j : Fin 17) : generator j ∈ K := by
    rw [← basisRecovery j]
    exact eval_mem K _ _ h0 h1 _
  apply top_unique
  intro g _
  rcases g.property with ⟨w, hw⟩
  have hword : ∀ w : List (Fin 17), word w ∈ K := by
    intro w
    induction w with
    | nil => exact K.one_mem
    | cons j w ih => exact K.mul_mem (hgen j) ih
  have hval : ∀ w : List (Fin 17), (word w : Equiv.Perm (Fin 100)) =
      evalWord OrderCertificate.gen1 w := by
    intro w
    induction w with
    | nil => rfl
    | cons j w ih => exact congrArg (OrderCertificate.gen1 j * ·) ih
  have heq : word w = g := Subtype.ext ((hval w).trans hw)
  exact heq ▸ hword w

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
