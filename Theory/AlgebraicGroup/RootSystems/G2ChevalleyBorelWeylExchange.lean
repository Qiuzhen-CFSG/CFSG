module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyRootSwap
public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyRankOneExchange
public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyFiniteTitsNormalizer

/-!
# Finite Borel--Weyl exchange for the G2 Chevalley carrier

This module defines the positive unipotent factor as the product of the six
explicit root curves in the convex order
`alpha, 3 alpha + beta, 2 alpha + beta, 3 alpha + 2 beta, alpha + beta, beta`.
A positive-Borel factor is a point of the explicit rank-two split torus
followed by that six-slot product.  The main theorem exchanges such a factor
between two of the twelve canonical Weyl lifts, retaining explicit torus and
six root parameters on both sides.

The proof first collects same-sign root words by absolute root height.  Adjacent
distinct roots are exchanged with `rootCurve_swap_relation`; every emitted
correction has strictly larger height, as certified by the finite G2 root table,
while equal roots combine by parameter addition.  The height-collection
argument is kept local so this concrete carrier theorem has no dependency on a
general root realization or on an abstract filtered-collection API.

For a simple exchange, the corresponding simple-root coordinate is collected
to the front.  Split-torus and Weyl conjugation move the remaining five positive
coordinates past the lift.  An ascent is normalized by the finite G2 Tits
normalizer.  In a descent, the nonsingular rank-one branch handles the zero
coordinate and the singular branch factors a nonzero negative-simple point
through one Weyl lift; the explicit length-six braid closes the longest-word
case.  Induction over the second canonical word gives the stated two-sided
factorization.  All identities come from the integral fourteen-dimensional G2
Chevalley representation and the characteristic-free carrier swap, rank-one
exchange, and finite normalizer modules, following the standard Chevalley and
Bruhat reductions in Steinberg's *Lectures on Chevalley Groups*.
-/

open scoped BigOperators Matrix
open Theory AlgebraicGroup

namespace Theory.AlgebraicGroup.G2Chevalley

namespace LocalHeightCollection

variable {I A G : Type*} [AddMonoid A] [Group G]

def wordProduct (factor : I → A → G) (word : List (I × A)) : G :=
  (word.map fun z => factor z.1 z.2).prod

omit [AddMonoid A] in
lemma wordProduct_append (factor : I → A → G) (left right : List (I × A)) :
    wordProduct factor (left ++ right) =
      wordProduct factor left * wordProduct factor right := by
  simp [wordProduct]

lemma factor_zero (factor : I → A → G)
    (hadd : ∀ i a b, factor i a * factor i b = factor i (a + b)) (i : I) :
    factor i 0 = 1 := by
  have h := hadd i 0 0
  have hcancel : factor i 0 * factor i 0 = factor i 0 * 1 := by
    simpa using h
  exact mul_left_cancel hcancel

section MoveHigh

variable (degree : I → ℕ) (factor : I → A → G) (support : List I)
variable (hswap : ∀ i j a b, i ∈ support → j ∈ support → i ≠ j →
  ∃ correction : List (I × A),
    (∀ z ∈ correction,
      z.1 ∈ support ∧ max (degree i) (degree j) < degree z.1) ∧
    factor i a * factor j b =
      factor j b * factor i a * wordProduct factor correction)

include hswap

omit [AddMonoid A] in
lemma highWord_mul_factor_exists (d : ℕ)
    (highWord : List (I × A))
    (hhigh : ∀ z ∈ highWord, z.1 ∈ support ∧ d < degree z.1)
    (q : I) (b : A) (hq : q ∈ support) (hqDegree : degree q ≤ d) :
    ∃ highWord' : List (I × A),
      (∀ z ∈ highWord', z.1 ∈ support ∧ d < degree z.1) ∧
      wordProduct factor highWord * factor q b =
        factor q b * wordProduct factor highWord' := by
  induction highWord with
  | nil =>
      exact ⟨[], by simp, by simp [wordProduct]⟩
  | cons z tail ih =>
      have hz := hhigh z (by simp)
      have htail : ∀ y ∈ tail, y.1 ∈ support ∧ d < degree y.1 := by
        intro y hy
        exact hhigh y (by simp [hy])
      obtain ⟨tail', htail', hmove⟩ := ih htail
      have hne : z.1 ≠ q := by
        intro heq
        subst q
        omega
      obtain ⟨correction, hcorrection, hexchange⟩ :=
        hswap z.1 q z.2 b hz.1 hq hne
      refine ⟨z :: correction ++ tail', ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hz
        rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨hys, hyDegree⟩ := hcorrection y hy
          exact ⟨hys, by omega⟩
        · exact htail' y hy
      · change factor z.1 z.2 * wordProduct factor tail * factor q b =
          factor q b * wordProduct factor (z :: correction ++ tail')
        calc
          factor z.1 z.2 * wordProduct factor tail * factor q b =
              factor z.1 z.2 * (wordProduct factor tail * factor q b) := by
                rw [mul_assoc]
          _ = factor z.1 z.2 *
                (factor q b * wordProduct factor tail') := by rw [hmove]
          _ = (factor z.1 z.2 * factor q b) *
                wordProduct factor tail' := by rw [mul_assoc]
          _ = (factor q b * factor z.1 z.2 *
                wordProduct factor correction) *
                wordProduct factor tail' := by rw [hexchange]
          _ = factor q b *
                wordProduct factor (z :: correction ++ tail') := by
                  simp [wordProduct, mul_assoc]

omit [AddMonoid A] in
lemma highWord_mul_lowWord_exists (d : ℕ)
    (highWord lowWord : List (I × A))
    (hhigh : ∀ z ∈ highWord, z.1 ∈ support ∧ d < degree z.1)
    (hlow : ∀ z ∈ lowWord, z.1 ∈ support ∧ degree z.1 ≤ d) :
    ∃ highWord' : List (I × A),
      (∀ z ∈ highWord', z.1 ∈ support ∧ d < degree z.1) ∧
      wordProduct factor highWord * wordProduct factor lowWord =
        wordProduct factor lowWord * wordProduct factor highWord' := by
  induction lowWord generalizing highWord with
  | nil =>
      exact ⟨highWord, hhigh, by simp [wordProduct]⟩
  | cons z tail ih =>
      have hz := hlow z (by simp)
      have htail : ∀ y ∈ tail, y.1 ∈ support ∧ degree y.1 ≤ d := by
        intro y hy
        exact hlow y (by simp [hy])
      obtain ⟨highWord', hhighWord', hmoveHead⟩ :=
        highWord_mul_factor_exists degree factor support hswap d highWord hhigh
          z.1 z.2 hz.1 hz.2
      obtain ⟨highWord'', hhighWord'', hmoveTail⟩ :=
        ih highWord' hhighWord' htail
      refine ⟨highWord'', hhighWord'', ?_⟩
      change wordProduct factor highWord *
          (factor z.1 z.2 * wordProduct factor tail) =
        (factor z.1 z.2 * wordProduct factor tail) *
          wordProduct factor highWord''
      calc
        wordProduct factor highWord *
              (factor z.1 z.2 * wordProduct factor tail) =
            (wordProduct factor highWord * factor z.1 z.2) *
              wordProduct factor tail := by rw [mul_assoc]
        _ = (factor z.1 z.2 *
              wordProduct factor highWord') * wordProduct factor tail := by
                rw [hmoveHead]
        _ = factor z.1 z.2 *
              (wordProduct factor highWord' * wordProduct factor tail) := by
                rw [mul_assoc]
        _ = factor z.1 z.2 *
              (wordProduct factor tail * wordProduct factor highWord'') := by
                rw [hmoveTail]
        _ = (factor z.1 z.2 * wordProduct factor tail) *
              wordProduct factor highWord'' := by rw [mul_assoc]

end MoveHigh

section ExtractLayer

variable (degree : I → ℕ) (factor : I → A → G) (support : List I)
variable (hadd : ∀ i a b, factor i a * factor i b = factor i (a + b))
variable (hswap : ∀ i j a b, i ∈ support → j ∈ support → i ≠ j →
  ∃ correction : List (I × A),
    (∀ z ∈ correction,
      z.1 ∈ support ∧ max (degree i) (degree j) < degree z.1) ∧
    factor i a * factor j b =
      factor j b * factor i a * wordProduct factor correction)

include hadd hswap

lemma extract_one (d : ℕ) (forbidden : List I)
    (hforbidden : ∀ i ∈ forbidden, degree i = d)
    (q : I) (hqSupport : q ∈ support) (hqDegree : degree q = d)
    (word : List (I × A))
    (hword : ∀ z ∈ word,
      z.1 ∈ support ∧ d ≤ degree z.1 ∧ z.1 ∉ forbidden) :
    ∃ t : A, ∃ residual : List (I × A),
      (∀ z ∈ residual,
        z.1 ∈ support ∧ d ≤ degree z.1 ∧ z.1 ∉ q :: forbidden) ∧
      wordProduct factor word = factor q t * wordProduct factor residual := by
  induction word with
  | nil =>
      refine ⟨0, [], by simp, ?_⟩
      rw [factor_zero factor hadd q]
      simp [wordProduct]
  | cons z tail ih =>
      have hz := hword z (by simp)
      have htail : ∀ y ∈ tail,
          y.1 ∈ support ∧ d ≤ degree y.1 ∧ y.1 ∉ forbidden := by
        intro y hy
        exact hword y (by simp [hy])
      obtain ⟨t, residual, hresidual, hproduct⟩ := ih htail
      by_cases heq : z.1 = q
      · subst q
        refine ⟨z.2 + t, residual, hresidual, ?_⟩
        change factor z.1 z.2 * wordProduct factor tail =
          factor z.1 (z.2 + t) * wordProduct factor residual
        rw [hproduct, ← mul_assoc, hadd]
      · obtain ⟨correction, hcorrection, hexchange⟩ :=
          hswap z.1 q z.2 t hz.1 hqSupport heq
        refine ⟨t, z :: correction ++ residual, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨hz.1, hz.2.1, by simp [heq, hz.2.2]⟩
          rcases List.mem_append.mp hy with hy | hy
          · obtain ⟨hySupport, hyDegree⟩ := hcorrection y hy
            refine ⟨hySupport, ?_, ?_⟩
            · omega
            · simp only [List.mem_cons, not_or]
              constructor
              · intro hyq
                subst q
                omega
              · intro hyForbidden
                have := hforbidden y.1 hyForbidden
                omega
          · exact hresidual y hy
        · simp only [wordProduct, List.map_cons, List.prod_cons]
          simp only [wordProduct] at hproduct
          rw [hproduct, ← mul_assoc, hexchange]
          simp [wordProduct, mul_assoc]

lemma extract_layer (d : ℕ) (forbidden layer : List I)
    (hforbidden : ∀ i ∈ forbidden, degree i = d)
    (hlayerNodup : layer.Nodup)
    (hlayerSupport : ∀ i ∈ layer, i ∈ support)
    (hlayerDegree : ∀ i ∈ layer, degree i = d)
    (hlayerDisjoint : ∀ i ∈ layer, i ∉ forbidden)
    (word : List (I × A))
    (hword : ∀ z ∈ word,
      z.1 ∈ support ∧ d ≤ degree z.1 ∧ z.1 ∉ forbidden) :
    ∃ layerWord residual : List (I × A),
      layerWord.map Prod.fst = layer ∧
      (∀ z ∈ residual,
        z.1 ∈ support ∧ d ≤ degree z.1 ∧
          z.1 ∉ layer ++ forbidden) ∧
      wordProduct factor word =
        wordProduct factor layerWord * wordProduct factor residual := by
  induction layer generalizing forbidden word with
  | nil =>
      exact ⟨[], word, by simp, by simpa using hword, by simp [wordProduct]⟩
  | cons q tail ih =>
      have hqDegree := hlayerDegree q (by simp)
      have hqSupport := hlayerSupport q (by simp)
      obtain ⟨t, word', hword', hproduct⟩ :=
        extract_one degree factor support hadd hswap d forbidden hforbidden
          q hqSupport hqDegree word hword
      have hforbidden' : ∀ i ∈ q :: forbidden, degree i = d := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hqDegree
        · exact hforbidden i hi
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hlayerNodup).2
      have htailSupport : ∀ i ∈ tail, i ∈ support := by
        intro i hi
        exact hlayerSupport i (by simp [hi])
      have htailDegree : ∀ i ∈ tail, degree i = d := by
        intro i hi
        exact hlayerDegree i (by simp [hi])
      have htailDisjoint : ∀ i ∈ tail, i ∉ q :: forbidden := by
        intro i hi
        simp only [List.mem_cons, not_or]
        exact ⟨fun hiq => (List.nodup_cons.mp hlayerNodup).1 (hiq ▸ hi),
          hlayerDisjoint i (by simp [hi])⟩
      obtain ⟨tailWord, residual, htailMap, hresidual, htailProduct⟩ :=
        ih (forbidden := q :: forbidden) (word := word') hforbidden'
          htailNodup htailSupport htailDegree htailDisjoint hword'
      refine ⟨(q, t) :: tailWord, residual, ?_, ?_, ?_⟩
      · simp [htailMap]
      · intro z hz
        obtain ⟨hzSupport, hzDegree, hzNot⟩ := hresidual z hz
        refine ⟨hzSupport, hzDegree, ?_⟩
        intro hzMem
        apply hzNot
        rw [List.mem_append] at hzMem ⊢
        rcases hzMem with hzMem | hzMem
        · rcases List.mem_cons.mp hzMem with hzq | hztail
          · exact Or.inr (by simp [hzq])
          · exact Or.inl hztail
        · exact Or.inr (by simp [hzMem])
      · rw [hproduct, htailProduct]
        simp [wordProduct, mul_assoc]

end ExtractLayer

section ShuffleLayer

variable (degree : I → ℕ) (factor : I → A → G) (support : List I)
variable (hswap : ∀ i j a b, i ∈ support → j ∈ support → i ≠ j →
  ∃ correction : List (I × A),
    (∀ z ∈ correction,
      z.1 ∈ support ∧ max (degree i) (degree j) < degree z.1) ∧
    factor i a * factor j b =
      factor j b * factor i a * wordProduct factor correction)

include hswap

omit [AddMonoid A] in
lemma lowWord_mul_layerFactor_exists (d : ℕ)
    (lowWord : List (I × A))
    (hlow : ∀ z ∈ lowWord, z.1 ∈ support ∧ degree z.1 < d)
    (q : I) (b : A) (hqSupport : q ∈ support) (hqDegree : degree q = d) :
    ∃ highWord : List (I × A),
      (∀ z ∈ highWord, z.1 ∈ support ∧ d < degree z.1) ∧
      wordProduct factor lowWord * factor q b =
        factor q b * wordProduct factor lowWord * wordProduct factor highWord := by
  induction lowWord with
  | nil =>
      exact ⟨[], by simp, by simp [wordProduct]⟩
  | cons z tail ih =>
      have hz := hlow z (by simp)
      have htail : ∀ y ∈ tail, y.1 ∈ support ∧ degree y.1 < d := by
        intro y hy
        exact hlow y (by simp [hy])
      obtain ⟨tailHigh, htailHigh, hmoveTail⟩ := ih htail
      have hne : z.1 ≠ q := by
        intro heq
        subst q
        omega
      obtain ⟨correction, hcorrection, hexchange⟩ :=
        hswap z.1 q z.2 b hz.1 hqSupport hne
      have hcorrectionHigh : ∀ y ∈ correction,
          y.1 ∈ support ∧ d < degree y.1 := by
        intro y hy
        obtain ⟨hySupport, hyDegree⟩ := hcorrection y hy
        exact ⟨hySupport, by omega⟩
      obtain ⟨correction', hcorrection', hmoveCorrection⟩ :=
        highWord_mul_lowWord_exists degree factor support hswap d correction tail
          hcorrectionHigh (by
            intro y hy
            obtain ⟨hySupport, hyDegree⟩ := htail y hy
            exact ⟨hySupport, Nat.le_of_lt hyDegree⟩)
      refine ⟨correction' ++ tailHigh, ?_, ?_⟩
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hcorrection' y hy
        · exact htailHigh y hy
      · change factor z.1 z.2 * wordProduct factor tail * factor q b =
          factor q b * (factor z.1 z.2 * wordProduct factor tail) *
            wordProduct factor (correction' ++ tailHigh)
        calc
          factor z.1 z.2 * wordProduct factor tail * factor q b =
              factor z.1 z.2 * (wordProduct factor tail * factor q b) := by
                rw [mul_assoc]
          _ = factor z.1 z.2 *
                (factor q b * wordProduct factor tail *
                  wordProduct factor tailHigh) := by rw [hmoveTail]
          _ = (factor z.1 z.2 * factor q b) *
                wordProduct factor tail * wordProduct factor tailHigh := by
                  simp [mul_assoc]
          _ = (factor q b * factor z.1 z.2 * wordProduct factor correction) *
                wordProduct factor tail * wordProduct factor tailHigh := by
                  rw [hexchange]
          _ = factor q b * factor z.1 z.2 *
                (wordProduct factor correction * wordProduct factor tail) *
                  wordProduct factor tailHigh := by simp [mul_assoc]
          _ = factor q b * factor z.1 z.2 *
                (wordProduct factor tail * wordProduct factor correction') *
                  wordProduct factor tailHigh := by rw [hmoveCorrection]
          _ = factor q b * (factor z.1 z.2 * wordProduct factor tail) *
                wordProduct factor (correction' ++ tailHigh) := by
                  simp [wordProduct_append, mul_assoc]

omit [AddMonoid A] in
lemma shuffle_degree_layer (d : ℕ) (order : List I)
    (horderSupport : ∀ i ∈ order, i ∈ support)
    (lowWord layerWord : List (I × A))
    (hlowMap : lowWord.map Prod.fst = order.filter (fun i => degree i < d))
    (hlayerMap : layerWord.map Prod.fst = order.filter (fun i => degree i = d)) :
    ∃ collected highWord : List (I × A),
      collected.map Prod.fst = order.filter (fun i => degree i < d + 1) ∧
      (∀ z ∈ highWord, z.1 ∈ support ∧ d < degree z.1) ∧
      wordProduct factor lowWord * wordProduct factor layerWord =
        wordProduct factor collected * wordProduct factor highWord := by
  classical
  induction order generalizing lowWord layerWord with
  | nil =>
      have hlowNil : lowWord = [] := by simpa using hlowMap
      have hlayerNil : layerWord = [] := by simpa using hlayerMap
      subst lowWord
      subst layerWord
      exact ⟨[], [], by simp, by simp, by simp [wordProduct]⟩
  | cons i tail ih =>
      have htailSupport : ∀ j ∈ tail, j ∈ support := by
        intro j hj
        exact horderSupport j (by simp [hj])
      by_cases hiLow : degree i < d
      · cases lowWord with
        | nil => simp [hiLow] at hlowMap
        | cons z lowTail =>
            have hlowMap' : z.1 :: lowTail.map Prod.fst =
                i :: tail.filter (fun j => degree j < d) := by
              simpa [hiLow] using hlowMap
            have hz : z.1 = i := (List.cons.inj hlowMap').1
            have hlowTail : lowTail.map Prod.fst =
                tail.filter (fun j => degree j < d) := (List.cons.inj hlowMap').2
            have hiNotLayer : degree i ≠ d := by omega
            obtain ⟨collected, highWord, hcollected, hhigh, hproduct⟩ :=
              ih htailSupport lowTail layerWord hlowTail
                (by simpa [hiNotLayer] using hlayerMap)
            refine ⟨z :: collected, highWord, ?_, hhigh, ?_⟩
            · simp only [List.map_cons]
              rw [hz, hcollected]
              exact (List.filter_cons_of_pos (by
                simpa using show degree i < d + 1 by omega)).symm
            · change factor z.1 z.2 * wordProduct factor lowTail *
                  wordProduct factor layerWord =
                (factor z.1 z.2 * wordProduct factor collected) *
                  wordProduct factor highWord
              rw [mul_assoc, hproduct, ← mul_assoc]
      · by_cases hiLayer : degree i = d
        · cases layerWord with
          | nil => simp [hiLayer] at hlayerMap
          | cons z layerTail =>
              have hlayerMap' : z.1 :: layerTail.map Prod.fst =
                  i :: tail.filter (fun j => degree j = d) := by
                simpa [hiLayer] using hlayerMap
              have hz : z.1 = i := (List.cons.inj hlayerMap').1
              have hlayerTail : layerTail.map Prod.fst =
                  tail.filter (fun j => degree j = d) := (List.cons.inj hlayerMap').2
              subst i
              have hlow : ∀ y ∈ lowWord,
                  y.1 ∈ support ∧ degree y.1 < d := by
                intro y hy
                have hyMap : y.1 ∈ lowWord.map Prod.fst := by
                  rw [List.mem_map]
                  exact ⟨y, hy, rfl⟩
                rw [hlowMap] at hyMap
                obtain ⟨hyOrder, hyDegreeBool⟩ := List.mem_filter.mp hyMap
                have hyDegree : degree y.1 < d := by simpa using hyDegreeBool
                have hyNe : y.1 ≠ z.1 := by
                  intro heq
                  rw [heq, hiLayer] at hyDegree
                  omega
                have hyTail : y.1 ∈ tail := (List.mem_cons.mp hyOrder).resolve_left hyNe
                exact ⟨htailSupport y.1 hyTail, hyDegree⟩
              obtain ⟨movedHigh, hmovedHigh, hmoveLeft⟩ :=
                lowWord_mul_layerFactor_exists degree factor support hswap d lowWord
                  hlow z.1 z.2 (horderSupport z.1 (by simp)) hiLayer
              have hlayerTailData : ∀ y ∈ layerTail,
                  y.1 ∈ support ∧ degree y.1 ≤ d := by
                intro y hy
                have hyMap : y.1 ∈ layerTail.map Prod.fst := by
                  rw [List.mem_map]
                  exact ⟨y, hy, rfl⟩
                rw [hlayerTail] at hyMap
                obtain ⟨hyTail, hyDegreeBool⟩ := List.mem_filter.mp hyMap
                have hyDegree : degree y.1 = d := by simpa using hyDegreeBool
                exact ⟨htailSupport y.1 hyTail, hyDegree.le⟩
              obtain ⟨movedHigh', hmovedHigh', hmoveRight⟩ :=
                highWord_mul_lowWord_exists degree factor support hswap d
                  movedHigh layerTail hmovedHigh hlayerTailData
              obtain ⟨collected, highWord, hcollected, hhigh, hproduct⟩ :=
                ih htailSupport lowWord layerTail (by simpa [hiLayer] using hlowMap)
                  hlayerTail
              refine ⟨z :: collected, highWord ++ movedHigh', ?_, ?_, ?_⟩
              · simp [hiLayer, hcollected]
              · intro y hy
                rcases List.mem_append.mp hy with hy | hy
                · exact hhigh y hy
                · exact hmovedHigh' y hy
              · change wordProduct factor lowWord *
                    (factor z.1 z.2 * wordProduct factor layerTail) =
                  (factor z.1 z.2 * wordProduct factor collected) *
                    wordProduct factor (highWord ++ movedHigh')
                calc
                  wordProduct factor lowWord *
                        (factor z.1 z.2 * wordProduct factor layerTail) =
                      (wordProduct factor lowWord * factor z.1 z.2) *
                        wordProduct factor layerTail := by rw [mul_assoc]
                  _ = (factor z.1 z.2 * wordProduct factor lowWord *
                        wordProduct factor movedHigh) *
                        wordProduct factor layerTail := by rw [hmoveLeft]
                  _ = factor z.1 z.2 * wordProduct factor lowWord *
                        (wordProduct factor movedHigh *
                          wordProduct factor layerTail) := by simp [mul_assoc]
                  _ = factor z.1 z.2 * wordProduct factor lowWord *
                        (wordProduct factor layerTail *
                          wordProduct factor movedHigh') := by rw [hmoveRight]
                  _ = factor z.1 z.2 *
                        (wordProduct factor lowWord *
                          wordProduct factor layerTail) *
                            wordProduct factor movedHigh' := by simp [mul_assoc]
                  _ = factor z.1 z.2 *
                        (wordProduct factor collected *
                          wordProduct factor highWord) *
                            wordProduct factor movedHigh' := by rw [hproduct]
                  _ = (factor z.1 z.2 * wordProduct factor collected) *
                        wordProduct factor (highWord ++ movedHigh') := by
                          simp [wordProduct_append, mul_assoc]
        · obtain ⟨collected, highWord, hcollected, hhigh, hproduct⟩ :=
            ih htailSupport lowWord layerWord (by simpa [hiLow] using hlowMap)
              (by simpa [hiLayer] using hlayerMap)
          refine ⟨collected, highWord, ?_, hhigh, hproduct⟩
          simpa [Nat.lt_succ_iff, show ¬ degree i ≤ d by omega] using hcollected

end ShuffleLayer

section DegreeAccumulator

variable (degree : I → ℕ) (factor : I → A → G) (order : List I)
variable (hadd : ∀ i a b, factor i a * factor i b = factor i (a + b))
variable (hswap : ∀ i j a b, i ∈ order → j ∈ order → i ≠ j →
  ∃ correction : List (I × A),
    (∀ z ∈ correction,
      z.1 ∈ order ∧ max (degree i) (degree j) < degree z.1) ∧
    factor i a * factor j b =
      factor j b * factor i a * wordProduct factor correction)

include hadd hswap

lemma collect_to_degree (horderNodup : order.Nodup) (n : ℕ)
    (word : List (I × A)) (hword : ∀ z ∈ word, z.1 ∈ order) :
    ∃ collected residual : List (I × A),
      collected.map Prod.fst = order.filter (fun i => degree i < n) ∧
      (∀ z ∈ residual, z.1 ∈ order ∧ n ≤ degree z.1) ∧
      wordProduct factor word =
        wordProduct factor collected * wordProduct factor residual := by
  classical
  induction n generalizing word with
  | zero =>
      refine ⟨[], word, by simp, ?_, by simp [wordProduct]⟩
      intro z hz
      exact ⟨hword z hz, Nat.zero_le _⟩
  | succ n ih =>
      obtain ⟨collected, residual, hcollected, hresidual, hproduct⟩ :=
        ih word hword
      let layer := order.filter (fun i => degree i = n)
      have hlayerNodup : layer.Nodup := horderNodup.filter _
      have hlayerSupport : ∀ i ∈ layer, i ∈ order := by
        intro i hi
        exact (List.mem_filter.mp hi).1
      have hlayerDegree : ∀ i ∈ layer, degree i = n := by
        intro i hi
        simpa using (List.mem_filter.mp hi).2
      obtain ⟨layerWord, residual', hlayerMap, hresidual', hlayerProduct⟩ :=
        extract_layer degree factor order hadd hswap n [] layer (by simp)
          hlayerNodup hlayerSupport hlayerDegree (by simp) residual (by
            intro z hz
            obtain ⟨hzSupport, hzDegree⟩ := hresidual z hz
            exact ⟨hzSupport, hzDegree, by simp⟩)
      have hresidualSucc : ∀ z ∈ residual',
          z.1 ∈ order ∧ n + 1 ≤ degree z.1 := by
        intro z hz
        obtain ⟨hzSupport, hzDegree, hzNotLayer⟩ := hresidual' z hz
        refine ⟨hzSupport, ?_⟩
        by_contra hnot
        have heq : degree z.1 = n := by omega
        apply hzNotLayer
        simp [layer, heq, hzSupport]
      obtain ⟨collected', correction, hcollected', hcorrection, hshuffle⟩ :=
        shuffle_degree_layer degree factor order hswap n order (by simp)
          collected layerWord hcollected (by simpa [layer] using hlayerMap)
      refine ⟨collected', correction ++ residual', hcollected', ?_, ?_⟩
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · obtain ⟨hzSupport, hzDegree⟩ := hcorrection z hz
          exact ⟨hzSupport, Nat.succ_le_iff.mpr hzDegree⟩
        · exact hresidualSucc z hz
      · calc
          wordProduct factor word =
              wordProduct factor collected * wordProduct factor residual := hproduct
          _ = wordProduct factor collected *
                (wordProduct factor layerWord * wordProduct factor residual') := by
                  rw [hlayerProduct]
          _ = (wordProduct factor collected * wordProduct factor layerWord) *
                wordProduct factor residual' := by rw [mul_assoc]
          _ = (wordProduct factor collected' * wordProduct factor correction) *
                wordProduct factor residual' := by rw [hshuffle]
          _ = wordProduct factor collected' *
                wordProduct factor (correction ++ residual') := by
                  simp [wordProduct_append, mul_assoc]

end DegreeAccumulator

lemma aligned_word_exists_params (factor : I → A → G)
    (order : List I) (horderNodup : order.Nodup)
    (word : List (I × A)) (hmap : word.map Prod.fst = order) :
    ∃ params : I → A,
      wordProduct factor word =
        (order.map fun i => factor i (params i)).prod := by
  classical
  induction order generalizing word with
  | nil =>
      have hword : word = [] := by simpa using hmap
      subst word
      exact ⟨fun _ => 0, by simp [wordProduct]⟩
  | cons i tail ih =>
      cases word with
      | nil => cases hmap
      | cons z rest =>
          have hmap' : z.1 :: rest.map Prod.fst = i :: tail := by simpa using hmap
          have hz : z.1 = i := (List.cons.inj hmap').1
          have hrest : rest.map Prod.fst = tail := (List.cons.inj hmap').2
          subst i
          obtain ⟨params, hparams⟩ :=
            ih (List.nodup_cons.mp horderNodup).2 rest hrest
          refine ⟨fun j => if j = z.1 then z.2 else params j, ?_⟩
          change factor z.1 z.2 * wordProduct factor rest =
            factor z.1 (if z.1 = z.1 then z.2 else params z.1) *
              (tail.map fun j => factor j (if j = z.1 then z.2 else params j)).prod
          rw [hparams]
          simp only [if_pos, mul_left_cancel_iff]
          apply congrArg List.prod
          apply List.map_congr_left
          intro j hj
          have hne : j ≠ z.1 := by
            intro heq
            subst j
            exact (List.nodup_cons.mp horderNodup).1 hj
          simp [hne]

/-- Abstract arbitrary-order collection for a finite degree-filtered family.

The only algebraic inputs are same-index additivity and, for indices in the
finite support, an adjacent exchange formula with an explicit correction word
strictly above both exchanged degrees.
The result supplies parameters in the caller's chosen order. -/
theorem filteredCollection_exists_params
    (degree : I → ℕ) (factor : I → A → G) (order : List I)
    (horderNodup : order.Nodup) (degreeBound : ℕ)
    (hdegreeBound : ∀ i ∈ order, degree i < degreeBound)
    (hadd : ∀ i a b, factor i a * factor i b = factor i (a + b))
    (hswap : ∀ i j a b, i ∈ order → j ∈ order → i ≠ j →
      ∃ correction : List (I × A),
        (∀ z ∈ correction,
          z.1 ∈ order ∧ max (degree i) (degree j) < degree z.1) ∧
        factor i a * factor j b =
          factor j b * factor i a * wordProduct factor correction)
    (word : List (I × A)) (hword : ∀ z ∈ word, z.1 ∈ order) :
    ∃ params : I → A,
      wordProduct factor word =
        (order.map fun i => factor i (params i)).prod := by
  classical
  obtain ⟨collected, residual, hcollected, hresidual, hproduct⟩ :=
    collect_to_degree degree factor order hadd hswap horderNodup degreeBound word hword
  have hresidualNil : residual = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    obtain ⟨hzSupport, hzDegree⟩ := hresidual z hz
    exact (Nat.not_le_of_lt (hdegreeBound z.1 hzSupport)) hzDegree
  subst residual
  have hcollectedMap : collected.map Prod.fst = order := by
    rw [hcollected]
    apply List.filter_eq_self.mpr
    intro i hi
    simpa using hdegreeBound i hi
  obtain ⟨params, hparams⟩ :=
    aligned_word_exists_params factor order horderNodup collected hcollectedMap
  refine ⟨params, ?_⟩
  simpa [wordProduct] using hproduct.trans (by simpa [wordProduct] using hparams)

end LocalHeightCollection


universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The convex order associated to the alternating reduced word for the longest element. -/
@[expose] public def positiveConvexRoot : Fin 6 → Root
  | 0 => Root.short
  | 1 => Root.threeShortLong
  | 2 => Root.twoShortLong
  | 3 => Root.threeShortTwoLong
  | 4 => Root.shortLong
  | 5 => Root.long

/-- The six-slot positive-root product in the fixed convex order. -/
@[expose] public noncomputable def carrierPositiveRootProduct (a : Fin 6 → k) :
    CarrierPoint (k := k) :=
  ([0, 1, 2, 3, 4, 5].map fun i : Fin 6 =>
    (rootMorphism (k := k) (positiveConvexRoot i)).onPoints (kPlusPoint (a i))).prod

/-- A split-torus point followed by the fixed positive-root product. -/
@[expose] public noncomputable def carrierPositiveBorelFactor
    (t : Variety.Point (dVariety k 2)) (a : Fin 6 → k) : CarrierPoint (k := k) :=
  (splitTorusMorphism (k := k)).onPoints t * carrierPositiveRootProduct a

private noncomputable abbrev X (r : Root) (a : k) : CarrierPoint (k := k) :=
  (rootMorphism (k := k) r).onPoints (kPlusPoint a)

private noncomputable abbrev H (t : Variety.Point (dVariety k 2)) :
    CarrierPoint (k := k) :=
  (splitTorusMorphism (k := k)).onPoints t

private def positiveConvexOrder : List Root :=
  [positiveConvexRoot 0, positiveConvexRoot 1, positiveConvexRoot 2,
    positiveConvexRoot 3, positiveConvexRoot 4, positiveConvexRoot 5]

private def absoluteHeight (r : Root) : ℕ :=
  r.coord.1.natAbs + r.coord.2.natAbs

private noncomputable def rootWordProduct (word : List (Root × k)) :
    CarrierPoint (k := k) :=
  (word.map fun z => X z.1 z.2).prod

private noncomputable def ambientPointHom :
    LinearMap.GeneralLinearGroup k (Basis → k) →*
      Variety.Point (Ambient k) where
  toFun g := generalLinearRepresentationPoint (carrierBasis (k := k)) g
  map_one' := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_one (carrierBasis (k := k))
  map_mul' g h := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_mul (carrierBasis (k := k)) g h

private lemma X_ambient (r : Root) (a : k) :
    (ambientClosedCarrier (k := k)).inclusion.onPoints (X r a) =
      ambientPointHom
        (Matrix.GeneralLinearGroup.toLin (rootCurveUnit r a)) := by
  rw [rootMorphism_inclusion_apply, rootAmbientMorphism_apply]
  rfl

private lemma rootWordProduct_ambient (word : List (Root × k)) :
    (ambientClosedCarrier (k := k)).inclusion.onPoints (rootWordProduct word) =
      ambientPointHom
        (Matrix.GeneralLinearGroup.toLin
          ((word.map fun z => rootCurveUnit z.1 z.2).prod)) := by
  induction word with
  | nil => simp [rootWordProduct]
  | cons z word ih =>
      change (ambientClosedCarrier (k := k)).inclusion.onPoints
          (X z.1 z.2 * rootWordProduct word) =
        ambientPointHom
          (Matrix.GeneralLinearGroup.toLin
            (rootCurveUnit z.1 z.2 *
              (word.map fun y => rootCurveUnit y.1 y.2).prod))
      rw [map_mul, X_ambient, ih, ← map_mul,
        ← Matrix.GeneralLinearGroup.toLin.map_mul]

private lemma X_zero (r : Root) : X (k := k) r 0 = 1 := by
  have hk : kPlusPoint (0 : k) = 1 := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  change (rootMorphism (k := k) r).onPoints (kPlusPoint 0) = 1
  rw [hk]
  exact (rootMorphism (k := k) r).onPoints.map_one

private lemma X_add (r : Root) (a b : k) :
    X (k := k) r a * X r b = X r (a + b) := by
  change (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
      (rootMorphism (k := k) r).onPoints (kPlusPoint b) =
    (rootMorphism (k := k) r).onPoints (kPlusPoint (a + b))
  rw [← (rootMorphism (k := k) r).onPoints.map_mul, kPlusPoint_mul]

omit [IsAlgClosed k] in
private lemma kPlusPoint_neg_local (a : k) :
    (kPlusPoint a)⁻¹ = kPlusPoint (-a) := by
  apply (additiveGroupPointEquiv k).injective
  change (Multiplicative.ofAdd a)⁻¹ = Multiplicative.ofAdd (-a)
  rfl

private lemma X_inv (r : Root) (a : k) :
    (X (k := k) r a)⁻¹ = X r (-a) := by
  change ((rootMorphism (k := k) r).onPoints (kPlusPoint a))⁻¹ =
    (rootMorphism (k := k) r).onPoints (kPlusPoint (-a))
  rw [← (rootMorphism (k := k) r).onPoints.map_inv, kPlusPoint_neg_local]

private theorem carrier_root_swap (r s : Root) (a b : k)
    (hne : r ≠ s) (hneg : s ≠ -r) :
    X (k := k) r a * X s b =
      X s b * X r a *
        rootWordProduct
          ((rootCurveCommutatorTerms r s).map fun q =>
            (q.root, rootCurveTermParameter a b q)) := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  simp only [map_mul]
  rw [rootWordProduct_ambient]
  simp_rw [X_ambient]
  simp only [← map_mul, ← Matrix.GeneralLinearGroup.toLin.map_mul]
  apply congrArg ambientPointHom
  apply congrArg Matrix.GeneralLinearGroup.toLin
  simpa [rootCurveSwapRelation, rootCurveCorrectionWord, List.map_map,
    Function.comp_def] using rootCurve_swap_relation r s a b hne hneg

private theorem correction_positive_height_table :
    ∀ r s : Root,
      r ∈ positiveConvexOrder → s ∈ positiveConvexOrder →
        (rootCurveCommutatorTerms r s).Forall fun q =>
          q.root ∈ positiveConvexOrder ∧
            max (absoluteHeight r) (absoluteHeight s) < absoluteHeight q.root := by
  decide

private theorem correction_positive_height (r s : Root)
    (hr : r ∈ positiveConvexOrder) (hs : s ∈ positiveConvexOrder)
    (q : RootCurveCommutatorTerm) (hq : q ∈ rootCurveCommutatorTerms r s) :
    q.root ∈ positiveConvexOrder ∧
      max (absoluteHeight r) (absoluteHeight s) < absoluteHeight q.root := by
  exact (List.forall_iff_forall_mem.mp
    (correction_positive_height_table r s hr hs)) q hq

private theorem positive_not_opposite_table :
    ∀ r s : Root,
      r ∈ positiveConvexOrder → s ∈ positiveConvexOrder → s ≠ -r := by
  decide

private theorem positiveWord_exists_params
    (order : List Root) (horderNodup : order.Nodup)
    (horder : ∀ r, r ∈ order ↔ r ∈ positiveConvexOrder)
    (word : List (Root × k))
    (hword : ∀ z ∈ word, z.1 ∈ positiveConvexOrder) :
    ∃ params : Root → k,
      rootWordProduct word =
        (order.map fun r => X (k := k) r (params r)).prod := by
  let factor : Root → k → CarrierPoint (k := k) := fun r a => X r a
  have hdegreeBound : ∀ r ∈ order, absoluteHeight r < 6 := by
    intro r hr
    have hp := (horder r).mp hr
    fin_cases r <;>
      simp [positiveConvexOrder, positiveConvexRoot, absoluteHeight, Root.coord] at hp ⊢
  have hadd : ∀ r a b, factor r a * factor r b = factor r (a + b) := by
    exact fun r a b => X_add r a b
  have hswap : ∀ r s a b, r ∈ order → s ∈ order → r ≠ s →
      ∃ correction : List (Root × k),
        (∀ z ∈ correction,
          z.1 ∈ order ∧ max (absoluteHeight r) (absoluteHeight s) < absoluteHeight z.1) ∧
        factor r a * factor s b = factor s b * factor r a *
          LocalHeightCollection.wordProduct factor correction := by
    intro r s a b hr hs hne
    have hrp := (horder r).mp hr
    have hsp := (horder s).mp hs
    have hneg : s ≠ -r := by
      exact positive_not_opposite_table r s hrp hsp
    let correction : List (Root × k) :=
      (rootCurveCommutatorTerms r s).map fun q =>
        (q.root, rootCurveTermParameter a b q)
    refine ⟨correction, ?_, ?_⟩
    · intro z hz
      simp only [correction, List.mem_map] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      have hqh := correction_positive_height r s hrp hsp q hq
      exact ⟨(horder q.root).mpr hqh.1, hqh.2⟩
    · simpa [factor, correction, LocalHeightCollection.wordProduct, rootWordProduct] using
        carrier_root_swap (k := k) r s a b hne hneg
  have hword' : ∀ z ∈ word, z.1 ∈ order := by
    intro z hz
    exact (horder z.1).mpr (hword z hz)
  obtain ⟨params, hparams⟩ :=
    LocalHeightCollection.filteredCollection_exists_params absoluteHeight factor order
      horderNodup 6 hdegreeBound hadd hswap word hword'
  exact ⟨params, by simpa [factor, rootWordProduct, LocalHeightCollection.wordProduct] using hparams⟩

private theorem positiveWord_exists_fixed_params
    (word : List (Root × k))
    (hword : ∀ z ∈ word, z.1 ∈ positiveConvexOrder) :
    ∃ a : Fin 6 → k,
      rootWordProduct word = carrierPositiveRootProduct a := by
  have hn : positiveConvexOrder.Nodup := by decide
  obtain ⟨params, hp⟩ := positiveWord_exists_params positiveConvexOrder hn
    (fun _ => Iff.rfl) word hword
  refine ⟨fun i => params (positiveConvexRoot i), ?_⟩
  simpa [positiveConvexOrder, positiveConvexRoot, carrierPositiveRootProduct,
    rootWordProduct] using hp

private def positiveParameterWord (a : Fin 6 → k) : List (Root × k) :=
  [0, 1, 2, 3, 4, 5].map fun i : Fin 6 => (positiveConvexRoot i, a i)

private lemma carrierPositiveRootProduct_eq_word (a : Fin 6 → k) :
    carrierPositiveRootProduct a = rootWordProduct (positiveParameterWord a) := by
  rfl

omit [Field k] [IsAlgClosed k] in
private lemma positiveParameterWord_root_mem (a : Fin 6 → k) (z : Root × k)
    (hz : z ∈ positiveParameterWord a) : z.1 ∈ positiveConvexOrder := by
  simp [positiveParameterWord] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [positiveConvexOrder]

private lemma rootWordProduct_append (u v : List (Root × k)) :
    rootWordProduct (u ++ v) = rootWordProduct u * rootWordProduct v := by
  simp [rootWordProduct, List.map_append]

private lemma H_one : H (k := k) 1 = 1 := by
  exact (splitTorusMorphism (k := k)).onPoints.map_one

private lemma H_mul (t s : Variety.Point (dVariety k 2)) :
    H (k := k) t * H s = H (t * s) := by
  exact ((splitTorusMorphism (k := k)).onPoints.map_mul t s).symm

private lemma H_inv (t : Variety.Point (dVariety k 2)) :
    H (k := k) t⁻¹ = (H t)⁻¹ := by
  exact (splitTorusMorphism (k := k)).onPoints.map_inv t

private noncomputable def dRootScale (r : Root)
    (t : Variety.Point (dVariety k 2)) : k := by
  letI := (splitTorus (k := k)).carrierAlgebraicGroup
  exact (rootWeight (k := k) r).pointCharacter
    ((splitTorusIso (k := k)).hom.onPoints t)

private theorem dTorus_root_conjugation (r : Root) (a : k)
    (t : Variety.Point (dVariety k 2)) :
    (H (k := k) t)⁻¹ * X r a * H t = X r (dRootScale r t * a) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  have h := rootMorphism_splitTorus_conjugation (k := k) r a
    ((splitTorusIso (k := k)).hom.onPoints t)
  change ((splitTorus (k := k)).inclusion.onPoints
      ((splitTorusIso (k := k)).hom.onPoints t))⁻¹ * X r a *
      (splitTorus (k := k)).inclusion.onPoints
        ((splitTorusIso (k := k)).hom.onPoints t) =
    X r (dRootScale r t * a) at h
  simpa only [splitTorusIso_inclusion_apply] using h

private lemma X_move_H (r : Root) (a : k)
    (t : Variety.Point (dVariety k 2)) :
    X (k := k) r a * H t = H t * X r (dRootScale r t * a) := by
  have h := dTorus_root_conjugation (k := k) r a t
  calc
    X r a * H t = H t * ((H t)⁻¹ * X r a * H t) := by group
    _ = H t * X r (dRootScale r t * a) := by rw [h]

private lemma H_move_X (t : Variety.Point (dVariety k 2))
    (r : Root) (a : k) :
    H (k := k) t * X r a =
      X r (dRootScale r t⁻¹ * a) * H t := by
  have h := dTorus_root_conjugation (k := k) r a t⁻¹
  rw [H_inv, inv_inv] at h
  calc
    H t * X r a = (H t * X r a * (H t)⁻¹) * H t := by group
    _ = X r (dRootScale r t⁻¹ * a) * H t := by rw [h]

private noncomputable def scaleRootWord (t : Variety.Point (dVariety k 2))
    (word : List (Root × k)) : List (Root × k) :=
  word.map fun z => (z.1, dRootScale z.1 t * z.2)

private lemma rootWordProduct_move_H (word : List (Root × k))
    (t : Variety.Point (dVariety k 2)) :
    rootWordProduct word * H (k := k) t =
      H t * rootWordProduct (scaleRootWord t word) := by
  induction word with
  | nil => simp [rootWordProduct, scaleRootWord]
  | cons z word ih =>
      change (X z.1 z.2 * rootWordProduct word) * H t =
        H t * (X z.1 (dRootScale z.1 t * z.2) *
          rootWordProduct (scaleRootWord t word))
      rw [mul_assoc, ih, ← mul_assoc, X_move_H]
      group

private def IsPositiveBorel (g : CarrierPoint (k := k)) : Prop :=
  ∃ t : Variety.Point (dVariety k 2), ∃ a : Fin 6 → k,
    g = carrierPositiveBorelFactor t a

private lemma isPositiveBorel_factor (t : Variety.Point (dVariety k 2))
    (a : Fin 6 → k) : IsPositiveBorel (carrierPositiveBorelFactor t a) :=
  ⟨t, a, rfl⟩

private lemma isPositiveBorel_one : IsPositiveBorel (k := k) 1 := by
  let a : Fin 6 → k := fun _ => 0
  refine ⟨1, a, ?_⟩
  simp [carrierPositiveBorelFactor, carrierPositiveRootProduct, a, H_one, X_zero]

private lemma isPositiveBorel_torus (t : Variety.Point (dVariety k 2)) :
    IsPositiveBorel (H (k := k) t) := by
  let a : Fin 6 → k := fun _ => 0
  refine ⟨t, a, ?_⟩
  simp [carrierPositiveBorelFactor, carrierPositiveRootProduct, a, X_zero]

private lemma isPositiveBorel_root (r : Root) (a : k)
    (hr : r ∈ positiveConvexOrder) : IsPositiveBorel (X (k := k) r a) := by
  obtain ⟨c, hc⟩ := positiveWord_exists_fixed_params (k := k) [(r, a)] (by
    intro z hz
    simp only [List.mem_singleton] at hz
    subst z
    exact hr)
  refine ⟨1, c, ?_⟩
  simpa [carrierPositiveBorelFactor, rootWordProduct, H_one] using hc

private lemma isPositiveBorel_mul {g h : CarrierPoint (k := k)}
    (hg : IsPositiveBorel g) (hh : IsPositiveBorel h) :
    IsPositiveBorel (g * h) := by
  obtain ⟨t, a, rfl⟩ := hg
  obtain ⟨s, b, rfl⟩ := hh
  let moved := scaleRootWord s (positiveParameterWord a)
  have hmoved : ∀ z ∈ moved, z.1 ∈ positiveConvexOrder := by
    intro z hz
    simp only [moved, scaleRootWord, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact positiveParameterWord_root_mem a y hy
  let word := moved ++ positiveParameterWord b
  have hword : ∀ z ∈ word, z.1 ∈ positiveConvexOrder := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hmoved z hz
    · exact positiveParameterWord_root_mem b z hz
  obtain ⟨c, hc⟩ := positiveWord_exists_fixed_params (k := k) word hword
  refine ⟨t * s, c, ?_⟩
  simp only [carrierPositiveBorelFactor]
  rw [carrierPositiveRootProduct_eq_word, carrierPositiveRootProduct_eq_word,
    carrierPositiveRootProduct_eq_word]
  calc
    (H t * rootWordProduct (positiveParameterWord a)) *
        (H s * rootWordProduct (positiveParameterWord b)) =
      H t * (rootWordProduct (positiveParameterWord a) * H s) *
        rootWordProduct (positiveParameterWord b) := by group
    _ = H t * (H s * rootWordProduct moved) *
        rootWordProduct (positiveParameterWord b) := by
          rw [rootWordProduct_move_H]
    _ = (H t * H s) *
        (rootWordProduct moved * rootWordProduct (positiveParameterWord b)) := by
          group
    _ = H (t * s) * rootWordProduct word := by
          rw [H_mul, ← rootWordProduct_append]
    _ = H (t * s) * carrierPositiveRootProduct c := by rw [hc]

private lemma isPositiveBorel_rootWord (word : List (Root × k))
    (hword : ∀ z ∈ word, z.1 ∈ positiveConvexOrder) :
    IsPositiveBorel (rootWordProduct (k := k) word) := by
  obtain ⟨a, ha⟩ := positiveWord_exists_fixed_params (k := k) word hword
  refine ⟨1, a, ?_⟩
  simpa [carrierPositiveBorelFactor, H_one] using ha

private def simpleTailOrder : Fin 2 → List Root
  | 0 => [Root.threeShortLong, Root.twoShortLong,
      Root.threeShortTwoLong, Root.shortLong, Root.long]
  | 1 => [Root.short, Root.threeShortLong, Root.twoShortLong,
      Root.threeShortTwoLong, Root.shortLong]

private def simpleFirstOrder (i : Fin 2) : List Root :=
  simpleRoot i :: simpleTailOrder i

private theorem simpleFirstOrder_nodup (i : Fin 2) :
    (simpleFirstOrder i).Nodup := by
  fin_cases i <;> decide

private theorem simpleFirstOrder_mem (i : Fin 2) (r : Root) :
    r ∈ simpleFirstOrder i ↔ r ∈ positiveConvexOrder := by
  fin_cases i <;> fin_cases r <;> decide

private theorem simpleTailOrder_spec (i : Fin 2) (r : Root)
    (hr : r ∈ simpleTailOrder i) :
    r ∈ positiveConvexOrder ∧ r ≠ simpleRoot i := by
  revert hr r i
  decide

private theorem positiveProduct_simple_decompose (i : Fin 2) (a : Fin 6 → k) :
    ∃ c : k, ∃ word : List (Root × k),
      (∀ z ∈ word, z.1 ∈ positiveConvexOrder ∧ z.1 ≠ simpleRoot i) ∧
      carrierPositiveRootProduct a =
        X (k := k) (simpleRoot i) c * rootWordProduct word := by
  have hsource : ∀ z ∈ positiveParameterWord a,
      z.1 ∈ positiveConvexOrder := positiveParameterWord_root_mem a
  obtain ⟨params, hp⟩ := positiveWord_exists_params (k := k)
    (simpleFirstOrder i) (simpleFirstOrder_nodup i)
    (simpleFirstOrder_mem i) (positiveParameterWord a) hsource
  let word := (simpleTailOrder i).map fun r => (r, params r)
  refine ⟨params (simpleRoot i), word, ?_, ?_⟩
  · intro z hz
    simp only [word, List.mem_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact simpleTailOrder_spec i r hr
  · rw [carrierPositiveRootProduct_eq_word, hp]
    fin_cases i <;>
      simp [simpleFirstOrder, simpleTailOrder, word, rootWordProduct, simpleRoot]

private theorem positiveBorel_simple_decompose
    (i : Fin 2) (t : Variety.Point (dVariety k 2)) (a : Fin 6 → k) :
    ∃ c : k, ∃ word : List (Root × k),
      (∀ z ∈ word, z.1 ∈ positiveConvexOrder ∧ z.1 ≠ simpleRoot i) ∧
      carrierPositiveBorelFactor t a =
        X (k := k) (simpleRoot i) c * (H t * rootWordProduct word) := by
  obtain ⟨c, word, hword, ha⟩ := positiveProduct_simple_decompose (k := k) i a
  refine ⟨dRootScale (simpleRoot i) t⁻¹ * c, word, hword, ?_⟩
  rw [carrierPositiveBorelFactor, ha]
  calc
    H t * (X (simpleRoot i) c * rootWordProduct word) =
        (H t * X (simpleRoot i) c) * rootWordProduct word := by group
    _ = (X (simpleRoot i) (dRootScale (simpleRoot i) t⁻¹ * c) * H t) *
        rootWordProduct word := by rw [H_move_X]
    _ = X (simpleRoot i) (dRootScale (simpleRoot i) t⁻¹ * c) *
        (H t * rootWordProduct word) := by group

private noncomputable def simpleReflectedWord (i : Fin 2)
    (word : List (Root × k)) : List (Root × k) :=
  word.map fun z =>
    (simpleReflection i z.1, (weylRootSign i z.1 : k) * z.2)

private lemma simpleWeyl_rootWord_conjugation (i : Fin 2)
    (word : List (Root × k)) :
    (carrierWeylRepresentative (k := k) i)⁻¹ * rootWordProduct word *
        carrierWeylRepresentative i =
      rootWordProduct (simpleReflectedWord i word) := by
  induction word with
  | nil => simp [rootWordProduct, simpleReflectedWord]
  | cons z word ih =>
      change (carrierWeylRepresentative (k := k) i)⁻¹ *
          (X z.1 z.2 * rootWordProduct word) * carrierWeylRepresentative i =
        X (simpleReflection i z.1) ((weylRootSign i z.1 : k) * z.2) *
          rootWordProduct (simpleReflectedWord i word)
      calc
        _ = ((carrierWeylRepresentative (k := k) i)⁻¹ * X z.1 z.2 *
              carrierWeylRepresentative i) *
            ((carrierWeylRepresentative (k := k) i)⁻¹ * rootWordProduct word *
              carrierWeylRepresentative i) := by group
        _ = _ := by
          rw [carrierWeylRepresentative_rootMorphism_conjugation, ih]

private theorem simpleReflection_preserves_tail_table :
    ∀ i : Fin 2, ∀ r : Root,
      r ∈ positiveConvexOrder → r ≠ simpleRoot i →
        simpleReflection i r ∈ positiveConvexOrder := by
  decide

omit [IsAlgClosed k] in
private theorem simpleReflectedWord_positive (i : Fin 2)
    (word : List (Root × k))
    (hword : ∀ z ∈ word, z.1 ∈ positiveConvexOrder ∧ z.1 ≠ simpleRoot i) :
    ∀ z ∈ simpleReflectedWord i word, z.1 ∈ positiveConvexOrder := by
  intro z hz
  simp only [simpleReflectedWord, List.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact simpleReflection_preserves_tail_table i y.1 (hword y hy).1 (hword y hy).2

private noncomputable def simpleReflectedTorusPoint (i : Fin 2)
    (t : Variety.Point (dVariety k 2)) : Variety.Point (dVariety k 2) :=
  (dPointEquiv 2).symm
    (simpleReflectionTorusParameter i (dPointEquiv 2 t))

private lemma simpleWeyl_torus_conjugation (i : Fin 2)
    (t : Variety.Point (dVariety k 2)) :
    (carrierWeylRepresentative (k := k) i)⁻¹ * H t *
        carrierWeylRepresentative i = H (simpleReflectedTorusPoint i t) := by
  fin_cases i
  · simpa [canonicalWeylWord, carrierWeylWord, wordTorusParameter,
      simpleReflectedTorusPoint] using
      canonicalWeyl_torus_conjugation (k := k) 1 t
  · simpa [canonicalWeylWord, carrierWeylWord, wordTorusParameter,
      simpleReflectedTorusPoint] using
      canonicalWeyl_torus_conjugation (k := k) 2 t

private theorem positiveTail_move_simpleWeyl (i : Fin 2)
    (t : Variety.Point (dVariety k 2)) (word : List (Root × k))
    (hword : ∀ z ∈ word, z.1 ∈ positiveConvexOrder ∧ z.1 ≠ simpleRoot i) :
    ∃ b : CarrierPoint (k := k), IsPositiveBorel b ∧
      (H t * rootWordProduct word) * carrierWeylRepresentative i =
        carrierWeylRepresentative i * b := by
  let reflected := simpleReflectedWord i word
  have hreflected : ∀ z ∈ reflected, z.1 ∈ positiveConvexOrder :=
    simpleReflectedWord_positive i word hword
  obtain ⟨a, ha⟩ := positiveWord_exists_fixed_params (k := k) reflected hreflected
  let b := carrierPositiveBorelFactor (simpleReflectedTorusPoint i t) a
  refine ⟨b, isPositiveBorel_factor _ _, ?_⟩
  have hconj : (carrierWeylRepresentative (k := k) i)⁻¹ *
      (H t * rootWordProduct word) * carrierWeylRepresentative i = b := by
    calc
      _ = ((carrierWeylRepresentative (k := k) i)⁻¹ * H t *
            carrierWeylRepresentative i) *
          ((carrierWeylRepresentative (k := k) i)⁻¹ * rootWordProduct word *
            carrierWeylRepresentative i) := by group
      _ = H (simpleReflectedTorusPoint i t) * rootWordProduct reflected := by
        rw [simpleWeyl_torus_conjugation, simpleWeyl_rootWord_conjugation]
      _ = b := by
        rw [ha]
        rfl
  calc
    (H t * rootWordProduct word) * carrierWeylRepresentative i =
        carrierWeylRepresentative i *
          ((carrierWeylRepresentative i)⁻¹ *
            (H t * rootWordProduct word) * carrierWeylRepresentative i) := by group
    _ = carrierWeylRepresentative i * b := by rw [hconj]

private def directRootAction : List (Fin 2) → Root → Root
  | [], r => r
  | i :: w, r => simpleReflection i (directRootAction w r)

private lemma simpleWeyl_root_conjugation_forward (i : Fin 2)
    (r : Root) (a : k) :
    carrierWeylRepresentative (k := k) i * X r a *
        (carrierWeylRepresentative i)⁻¹ =
      X (simpleReflection i r)
        ((weylRootSign i (simpleReflection i r) : k) * a) := by
  let c : k := (weylRootSign i (simpleReflection i r) : k) * a
  have h := carrierWeylRepresentative_rootMorphism_conjugation (k := k) i
    (simpleReflection i r) c
  have hsimp : (carrierWeylRepresentative (k := k) i)⁻¹ *
      X (simpleReflection i r) c * carrierWeylRepresentative i = X r a := by
    fin_cases i <;> fin_cases r <;>
      simpa [c, simpleReflection, weylRootSign] using h
  calc
    carrierWeylRepresentative (k := k) i * X r a *
        (carrierWeylRepresentative i)⁻¹ =
      carrierWeylRepresentative i *
        ((carrierWeylRepresentative i)⁻¹ * X (simpleReflection i r) c *
          carrierWeylRepresentative i) *
        (carrierWeylRepresentative i)⁻¹ := by rw [hsimp]
    _ = X (simpleReflection i r) c := by group

private theorem carrierWeylWord_root_conjugation_forward
    (w : List (Fin 2)) (r : Root) (a : k) :
    ∃ c : k,
      carrierWeylWord (k := k) w * X r a * (carrierWeylWord w)⁻¹ =
        X (directRootAction w r) c := by
  induction w generalizing r a with
  | nil => exact ⟨a, by simp [carrierWeylWord, directRootAction]⟩
  | cons i w ih =>
      obtain ⟨c, hc⟩ := ih r a
      let d : k := (weylRootSign i (simpleReflection i (directRootAction w r)) : k) * c
      refine ⟨d, ?_⟩
      rw [carrierWeylWord, mul_inv_rev]
      calc
        _ = carrierWeylRepresentative (k := k) i *
            (carrierWeylWord w * X r a * (carrierWeylWord w)⁻¹) *
            (carrierWeylRepresentative i)⁻¹ := by group
        _ = carrierWeylRepresentative (k := k) i * X (directRootAction w r) c *
            (carrierWeylRepresentative i)⁻¹ := by rw [hc]
        _ = X (simpleReflection i (directRootAction w r)) d := by
          rw [simpleWeyl_root_conjugation_forward]

private def rightDescent : Fin 12 → Fin 2 → Bool
  | 0, _ => false
  | 1, 0 => true | 1, 1 => false
  | 2, 0 => false | 2, 1 => true
  | 3, 0 => false | 3, 1 => true
  | 4, 0 => true | 4, 1 => false
  | 5, 0 => true | 5, 1 => false
  | 6, 0 => false | 6, 1 => true
  | 7, 0 => false | 7, 1 => true
  | 8, 0 => true | 8, 1 => false
  | 9, 0 => true | 9, 1 => false
  | 10, 0 => false | 10, 1 => true
  | 11, _ => true

private def rightDescentTarget : Fin 12 → Fin 2 → Fin 12
  | 1, 0 => 0 | 2, 1 => 0
  | 3, 1 => 1 | 4, 0 => 2
  | 5, 0 => 3 | 6, 1 => 4
  | 7, 1 => 5 | 8, 0 => 6
  | 9, 0 => 7 | 10, 1 => 8
  | 11, 0 => 10 | 11, 1 => 9
  | j, _ => j

private theorem non_descent_positive_table :
    ∀ j : Fin 12, ∀ i : Fin 2,
      rightDescent j i = false →
        directRootAction (canonicalWeylWord j) (simpleRoot i) ∈
          positiveConvexOrder := by
  decide

private theorem descent_target_positive_table :
    ∀ j : Fin 12, ∀ i : Fin 2,
      rightDescent j i = true →
        directRootAction (canonicalWeylWord (rightDescentTarget j i))
          (simpleRoot i) ∈ positiveConvexOrder := by
  decide

private lemma carrierWeylWord_append_singleton (w : List (Fin 2)) (i : Fin 2) :
    carrierWeylWord (k := k) (w ++ [i]) =
      carrierWeylWord w * carrierWeylRepresentative i := by
  induction w with
  | nil => simp [carrierWeylWord]
  | cons j w ih =>
      simp only [List.cons_append, carrierWeylWord, ih]
      group

private theorem descent_word_or_longest :
    ∀ j : Fin 12, ∀ i : Fin 2, rightDescent j i = true →
      (j = 11 ∧ i = 0) ∨
        canonicalWeylWord j =
          canonicalWeylWord (rightDescentTarget j i) ++ [i] := by
  decide

private theorem canonicalWeyl_descent_factor (j : Fin 12) (i : Fin 2)
    (hdesc : rightDescent j i = true) :
    carrierWeylWord (k := k) (canonicalWeylWord j) =
      carrierWeylWord (canonicalWeylWord (rightDescentTarget j i)) *
        carrierWeylRepresentative i := by
  rcases descent_word_or_longest j i hdesc with hlong | hword
  · obtain ⟨rfl, rfl⟩ := hlong
    change carrierWeylWord (k := k) [0, 1, 0, 1, 0, 1] =
      carrierWeylWord [1, 0, 1, 0, 1] * carrierWeylRepresentative 0
    calc
      carrierWeylWord (k := k) [0, 1, 0, 1, 0, 1] =
          carrierWeylWord [1, 0, 1, 0, 1, 0] :=
        carrierWeylRepresentative_braid_six
      _ = carrierWeylWord [1, 0, 1, 0, 1] *
          carrierWeylRepresentative 0 := by
        rw [← carrierWeylWord_append_singleton]
        rfl
  · rw [hword, carrierWeylWord_append_singleton]

private theorem root_ascent_exchange (j : Fin 12) (i : Fin 2) (a : k)
    (hpos : directRootAction (canonicalWeylWord j) (simpleRoot i) ∈
      positiveConvexOrder) :
    ∃ p : CarrierPoint (k := k), ∃ m : Fin 12,
      ∃ q : CarrierPoint (k := k),
        IsPositiveBorel p ∧ IsPositiveBorel q ∧
        carrierWeylWord (canonicalWeylWord j) * X (simpleRoot i) a *
            carrierWeylRepresentative i =
          p * carrierWeylWord (canonicalWeylWord m) * q := by
  obtain ⟨c, hc⟩ := carrierWeylWord_root_conjugation_forward (k := k)
    (canonicalWeylWord j) (simpleRoot i) a
  obtain ⟨m, t, hnorm⟩ := exists_canonicalWeyl_right_mul (k := k) j i false
  simp only [Bool.false_eq_true, if_false] at hnorm
  let p := X (k := k) (directRootAction (canonicalWeylWord j) (simpleRoot i)) c
  let q := H (k := k) t
  refine ⟨p, m, q, isPositiveBorel_root _ _ hpos,
    isPositiveBorel_torus t, ?_⟩
  have hmove : carrierWeylWord (k := k) (canonicalWeylWord j) *
      X (simpleRoot i) a = p * carrierWeylWord (canonicalWeylWord j) := by
    calc
      _ = (carrierWeylWord (canonicalWeylWord j) * X (simpleRoot i) a *
          (carrierWeylWord (canonicalWeylWord j))⁻¹) *
          carrierWeylWord (canonicalWeylWord j) := by group
      _ = p * carrierWeylWord (canonicalWeylWord j) := by rw [hc]
  calc
    carrierWeylWord (canonicalWeylWord j) * X (simpleRoot i) a *
        carrierWeylRepresentative i =
      p * (carrierWeylWord (canonicalWeylWord j) *
        carrierWeylRepresentative i) := by
          rw [hmove]
          group
    _ = p * (carrierWeylWord (canonicalWeylWord m) * q) := by rw [hnorm]
    _ = p * carrierWeylWord (canonicalWeylWord m) * q := by group

private theorem simpleRoot_positive (i : Fin 2) :
    simpleRoot i ∈ positiveConvexOrder := by
  fin_cases i <;> decide

private theorem rootWeylRepresentative_neg_simple (i : Fin 2) :
    rootWeylRepresentative (k := k) (-simpleRoot i) =
      carrierWeylRepresentative i := by
  fin_cases i
  · change carrierWeylWordInv (k := k) [0] * carrierWeylRepresentative 0 *
      carrierWeylWord [0] = carrierWeylRepresentative 0
    rw [carrierWeylWordInv_eq_inv]
    simp only [carrierWeylWord, mul_one]
    group
  · change carrierWeylWordInv (k := k) [1] * carrierWeylRepresentative 1 *
      carrierWeylWord [1] = carrierWeylRepresentative 1
    rw [carrierWeylWordInv_eq_inv]
    simp only [carrierWeylWord, mul_one]
    group

private theorem negativeSimple_zero_via_exchange (i : Fin 2) :
    X (k := k) (-simpleRoot i) 0 = 1 := by
  rcases carrier_oppositeRootProduct_exchange (k := k) (-simpleRoot i) 0 0 with
    hsingular | hnonsingular
  · have hzero : (1 : k) = 0 := by simpa using hsingular.1
    exact (one_ne_zero hzero).elim
  · obtain ⟨_, c, _, heq⟩ := hnonsingular
    have htorus : rootCorootTorusFactor (k := k) (-simpleRoot i) c⁻¹ = 1 := by
      simpa [X_zero] using heq.symm
    calc
      X (k := k) (-simpleRoot i) 0 =
          rootCorootTorusFactor (-simpleRoot i) c⁻¹ := by
            rw [X_zero, htorus]
      _ = 1 := htorus

private theorem negativeSimple_nonzero_factor (i : Fin 2) (c : k) (hc : c ≠ 0) :
    ∃ p q : CarrierPoint (k := k),
      IsPositiveBorel p ∧ IsPositiveBorel q ∧
      X (-simpleRoot i) c =
        p * carrierWeylRepresentative i * q := by
  let u : kˣ := Units.mk0 c hc
  let b : k := (u⁻¹ : kˣ)
  have hcb : c * b = 1 := by
    simp [b, u, hc]
  have hsing : 1 - c * b = 0 := by rw [hcb]; ring
  rcases carrier_oppositeRootProduct_exchange (k := k) (-simpleRoot i) c b with
    hsingular | hnonsingular
  · obtain ⟨_, d, _, heq⟩ := hsingular
    have heq' : X (k := k) (-simpleRoot i) c * X (simpleRoot i) b =
        X (simpleRoot i) (-b) * rootCorootTorusFactor (-simpleRoot i) d *
          rootWeylRepresentative (-simpleRoot i) := by
      simpa only [Root.neg_neg] using heq
    let p := X (k := k) (simpleRoot i) (-b) *
      rootCorootTorusFactor (-simpleRoot i) d
    let q := X (k := k) (simpleRoot i) (-b)
    have hp : IsPositiveBorel p := isPositiveBorel_mul
      (isPositiveBorel_root _ _ (simpleRoot_positive i))
      (isPositiveBorel_torus (rootCorootTorusPoint (-simpleRoot i) d))
    have hq : IsPositiveBorel q :=
      isPositiveBorel_root _ _ (simpleRoot_positive i)
    refine ⟨p, q, hp, hq, ?_⟩
    calc
      X (-simpleRoot i) c = X (-simpleRoot i) c * 1 := by group
      _ = X (-simpleRoot i) c *
          (X (simpleRoot i) b * X (simpleRoot i) (-b)) := by
            rw [X_add, add_neg_cancel, X_zero]
      _ = (X (-simpleRoot i) c * X (simpleRoot i) b) *
          X (simpleRoot i) (-b) := by group
      _ = (X (simpleRoot i) (-b) *
          rootCorootTorusFactor (-simpleRoot i) d *
          rootWeylRepresentative (-simpleRoot i)) *
          X (simpleRoot i) (-b) := by rw [heq']
      _ = p * carrierWeylRepresentative i * q := by
        rw [rootWeylRepresentative_neg_simple]
  · exact (hnonsingular.1 hsing).elim

private theorem positiveBorel_ascent_exchange
    (j : Fin 12) (i : Fin 2) (t : Variety.Point (dVariety k 2))
    (a : Fin 6 → k)
    (hpos : directRootAction (canonicalWeylWord j) (simpleRoot i) ∈
      positiveConvexOrder) :
    ∃ p : CarrierPoint (k := k), ∃ m : Fin 12,
      ∃ q : CarrierPoint (k := k),
        IsPositiveBorel p ∧ IsPositiveBorel q ∧
        carrierWeylWord (canonicalWeylWord j) *
            carrierPositiveBorelFactor t a * carrierWeylRepresentative i =
          p * carrierWeylWord (canonicalWeylWord m) * q := by
  obtain ⟨c, word, hword, hdecomp⟩ :=
    positiveBorel_simple_decompose (k := k) i t a
  obtain ⟨tail, htailB, htail⟩ :=
    positiveTail_move_simpleWeyl (k := k) i t word hword
  obtain ⟨p, m, q, hp, hq, hroot⟩ := root_ascent_exchange (k := k) j i c hpos
  refine ⟨p, m, q * tail, hp, isPositiveBorel_mul hq htailB, ?_⟩
  calc
    carrierWeylWord (canonicalWeylWord j) * carrierPositiveBorelFactor t a *
        carrierWeylRepresentative i =
      carrierWeylWord (canonicalWeylWord j) *
        (X (simpleRoot i) c * (H t * rootWordProduct word)) *
        carrierWeylRepresentative i := by rw [hdecomp]
    _ = carrierWeylWord (canonicalWeylWord j) * X (simpleRoot i) c *
        ((H t * rootWordProduct word) * carrierWeylRepresentative i) := by group
    _ = carrierWeylWord (canonicalWeylWord j) * X (simpleRoot i) c *
        (carrierWeylRepresentative i * tail) := by rw [htail]
    _ = (carrierWeylWord (canonicalWeylWord j) * X (simpleRoot i) c *
        carrierWeylRepresentative i) * tail := by group
    _ = (p * carrierWeylWord (canonicalWeylWord m) * q) * tail := by rw [hroot]
    _ = p * carrierWeylWord (canonicalWeylWord m) * (q * tail) := by group

private theorem positiveBorel_descent_exchange
    (j : Fin 12) (i : Fin 2) (t : Variety.Point (dVariety k 2))
    (a : Fin 6 → k) (hdesc : rightDescent j i = true) :
    ∃ p : CarrierPoint (k := k), ∃ m : Fin 12,
      ∃ q : CarrierPoint (k := k),
        IsPositiveBorel p ∧ IsPositiveBorel q ∧
        carrierWeylWord (canonicalWeylWord j) *
            carrierPositiveBorelFactor t a * carrierWeylRepresentative i =
          p * carrierWeylWord (canonicalWeylWord m) * q := by
  obtain ⟨c, word, hword, hdecomp⟩ :=
    positiveBorel_simple_decompose (k := k) i t a
  obtain ⟨tail, htailB, htail⟩ :=
    positiveTail_move_simpleWeyl (k := k) i t word hword
  let m := rightDescentTarget j i
  have hj := canonicalWeyl_descent_factor (k := k) j i hdesc
  let d : k := (weylRootSign i (simpleReflection i (simpleRoot i)) : k) * c
  have hconj := simpleWeyl_root_conjugation_forward (k := k) i (simpleRoot i) c
  have hreflect : simpleReflection i (simpleRoot i) = -simpleRoot i := by
    fin_cases i <;> rfl
  have hconj' : carrierWeylRepresentative (k := k) i * X (simpleRoot i) c *
      (carrierWeylRepresentative i)⁻¹ = X (-simpleRoot i) d := by
    simpa [d, hreflect] using hconj
  let s : Variety.Point (dVariety k 2) :=
    (dPointEquiv 2).symm (if i = 0 then titsSignParameter (R := k) 1
      else titsSignParameter (R := k) 2)
  have hsquare : carrierWeylRepresentative (k := k) i *
      carrierWeylRepresentative i = H s := by
    simpa [s] using carrierWeylRepresentative_square (k := k) i
  have hbase : carrierWeylWord (k := k) (canonicalWeylWord j) *
      carrierPositiveBorelFactor t a * carrierWeylRepresentative i =
      carrierWeylWord (canonicalWeylWord m) * X (-simpleRoot i) d *
        H s * tail := by
    calc
      carrierWeylWord (canonicalWeylWord j) * carrierPositiveBorelFactor t a *
          carrierWeylRepresentative i =
        carrierWeylWord (canonicalWeylWord j) *
          (X (simpleRoot i) c * (H t * rootWordProduct word)) *
          carrierWeylRepresentative i := by rw [hdecomp]
      _ = carrierWeylWord (canonicalWeylWord j) * X (simpleRoot i) c *
          ((H t * rootWordProduct word) * carrierWeylRepresentative i) := by group
      _ = carrierWeylWord (canonicalWeylWord j) * X (simpleRoot i) c *
          (carrierWeylRepresentative i * tail) := by rw [htail]
      _ = (carrierWeylWord (canonicalWeylWord m) * carrierWeylRepresentative i) *
          X (simpleRoot i) c * carrierWeylRepresentative i * tail := by
            rw [hj]
            simp only [m]
            group
      _ = carrierWeylWord (canonicalWeylWord m) *
          (carrierWeylRepresentative i * X (simpleRoot i) c *
            (carrierWeylRepresentative i)⁻¹) *
          (carrierWeylRepresentative i * carrierWeylRepresentative i) * tail := by
            group
      _ = carrierWeylWord (canonicalWeylWord m) * X (-simpleRoot i) d *
          H s * tail := by rw [hconj', hsquare]
  by_cases hd : d = 0
  · have hzero := negativeSimple_zero_via_exchange (k := k) i
    let q := H (k := k) s * tail
    refine ⟨1, m, q, isPositiveBorel_one,
      isPositiveBorel_mul (isPositiveBorel_torus s) htailB, ?_⟩
    rw [hbase, hd, hzero]
    simp only [q, one_mul, mul_one, mul_assoc]
  · obtain ⟨p₀, q₀, hp₀, hq₀, hnegative⟩ :=
      negativeSimple_nonzero_factor (k := k) i d hd
    obtain ⟨t₀, a₀, hp₀eq⟩ := hp₀
    have hmpos : directRootAction (canonicalWeylWord m) (simpleRoot i) ∈
        positiveConvexOrder := descent_target_positive_table j i hdesc
    obtain ⟨p, n, q, hp, hq, hascent⟩ :=
      positiveBorel_ascent_exchange (k := k) m i t₀ a₀ hmpos
    let right := q * q₀ * H (k := k) s * tail
    have hright : IsPositiveBorel right :=
      isPositiveBorel_mul
        (isPositiveBorel_mul (isPositiveBorel_mul hq hq₀)
          (isPositiveBorel_torus s)) htailB
    refine ⟨p, n, right, hp, hright, ?_⟩
    rw [hbase, hnegative]
    calc
      carrierWeylWord (canonicalWeylWord m) *
          (p₀ * carrierWeylRepresentative i * q₀) * H s * tail =
        (carrierWeylWord (canonicalWeylWord m) * p₀ *
          carrierWeylRepresentative i) * q₀ * H s * tail := by group
      _ = (p * carrierWeylWord (canonicalWeylWord n) * q) *
          q₀ * H s * tail := by
            rw [hp₀eq, hascent]
      _ = p * carrierWeylWord (canonicalWeylWord n) * right := by
        simp only [right]
        group

private theorem positiveBorel_simple_exchange
    (j : Fin 12) (i : Fin 2) (t : Variety.Point (dVariety k 2))
    (a : Fin 6 → k) :
    ∃ p : CarrierPoint (k := k), ∃ m : Fin 12,
      ∃ q : CarrierPoint (k := k),
        IsPositiveBorel p ∧ IsPositiveBorel q ∧
        carrierWeylWord (canonicalWeylWord j) *
            carrierPositiveBorelFactor t a * carrierWeylRepresentative i =
          p * carrierWeylWord (canonicalWeylWord m) * q := by
  by_cases hdesc : rightDescent j i = true
  · exact positiveBorel_descent_exchange (k := k) j i t a hdesc
  · have hn : rightDescent j i = false := Bool.eq_false_of_not_eq_true hdesc
    exact positiveBorel_ascent_exchange (k := k) j i t a
      (non_descent_positive_table j i hn)

private theorem positiveBorel_word_exchange
    (j : Fin 12) (b : CarrierPoint (k := k)) (hb : IsPositiveBorel b) :
    ∀ w : List (Fin 2),
      ∃ p : CarrierPoint (k := k), ∃ m : Fin 12,
        ∃ q : CarrierPoint (k := k),
          IsPositiveBorel p ∧ IsPositiveBorel q ∧
          carrierWeylWord (canonicalWeylWord j) * b * carrierWeylWord w =
            p * carrierWeylWord (canonicalWeylWord m) * q
  | [] => by
      refine ⟨1, j, b, isPositiveBorel_one, hb, ?_⟩
      simp [carrierWeylWord]
  | i :: w => by
      obtain ⟨t, a, hb⟩ := hb
      obtain ⟨p, m, q, hp, hq, hsimple⟩ :=
        positiveBorel_simple_exchange (k := k) j i t a
      obtain ⟨p', n, q', hp', hq', hword⟩ :=
        positiveBorel_word_exchange m q hq w
      refine ⟨p * p', n, q', isPositiveBorel_mul hp hp', hq', ?_⟩
      rw [hb, carrierWeylWord]
      calc
        carrierWeylWord (canonicalWeylWord j) * carrierPositiveBorelFactor t a *
            (carrierWeylRepresentative i * carrierWeylWord w) =
          (carrierWeylWord (canonicalWeylWord j) * carrierPositiveBorelFactor t a *
            carrierWeylRepresentative i) * carrierWeylWord w := by group
        _ = (p * carrierWeylWord (canonicalWeylWord m) * q) *
            carrierWeylWord w := by rw [hsimple]
        _ = p * (carrierWeylWord (canonicalWeylWord m) * q *
            carrierWeylWord w) := by group
        _ = p * (p' * carrierWeylWord (canonicalWeylWord n) * q') := by rw [hword]
        _ = (p * p') * carrierWeylWord (canonicalWeylWord n) * q' := by group

/-- An explicit positive-Borel factor between two canonical G2 Weyl lifts can
be exchanged into positive-Borel factors on the two sides of one canonical lift. -/
public theorem carrierWeyl_positiveBorel_canonical_exchange
    (j l : Fin 12) (t : Variety.Point (dVariety k 2)) (a : Fin 6 → k) :
    ∃ tLeft : Variety.Point (dVariety k 2), ∃ aLeft : Fin 6 → k,
      ∃ m : Fin 12, ∃ tRight : Variety.Point (dVariety k 2),
        ∃ aRight : Fin 6 → k,
          carrierWeylWord (canonicalWeylWord j) * carrierPositiveBorelFactor t a *
              carrierWeylWord (canonicalWeylWord l) =
            carrierPositiveBorelFactor tLeft aLeft *
              carrierWeylWord (canonicalWeylWord m) *
                carrierPositiveBorelFactor tRight aRight := by
  obtain ⟨p, m, q, hp, hq, heq⟩ :=
    positiveBorel_word_exchange (k := k) j (carrierPositiveBorelFactor t a)
      (isPositiveBorel_factor t a) (canonicalWeylWord l)
  obtain ⟨tLeft, aLeft, hp⟩ := hp
  obtain ⟨tRight, aRight, hq⟩ := hq
  exact ⟨tLeft, aLeft, m, tRight, aRight, by simpa [hp, hq] using heq⟩

/-! Public wrappers for the finite six-slot positive-Borel algebra.  The
internal proof keeps the collector and its carrier word private; these
elementwise interfaces are the only data needed by later mixed-word modules.
-/

public theorem carrierPositiveBorelFactor_mul_exists
    (t s : Variety.Point (dVariety k 2)) (a b : Fin 6 → k) :
    ∃ u : Variety.Point (dVariety k 2), ∃ c : Fin 6 → k,
      carrierPositiveBorelFactor t a * carrierPositiveBorelFactor s b =
        carrierPositiveBorelFactor u c := by
  obtain ⟨u, c, hu⟩ := isPositiveBorel_mul (k := k)
    (isPositiveBorel_factor t a) (isPositiveBorel_factor s b)
  exact ⟨u, c, hu⟩

public theorem carrierPositiveBorelFactor_one :
    carrierPositiveBorelFactor (k := k) 1 (fun _ => 0) = 1 := by
  simp [carrierPositiveBorelFactor, carrierPositiveRootProduct, H_one, X_zero]

public theorem carrierRootFactor_positiveBorel_exists (r : Root) (a : k)
    (hr : r.val < 6) :
    ∃ t : Variety.Point (dVariety k 2), ∃ c : Fin 6 → k,
      (rootMorphism (k := k) r).onPoints (kPlusPoint a) =
        carrierPositiveBorelFactor t c := by
  have hr' : r ∈ positiveConvexOrder := by
    fin_cases r <;>
      simp_all [positiveConvexOrder, positiveConvexRoot, Root.short, Root.long,
        Root.shortLong, Root.twoShortLong, Root.threeShortLong,
        Root.threeShortTwoLong]
  obtain ⟨t, c, hc⟩ := isPositiveBorel_root (k := k) r a hr'
  exact ⟨t, c, hc⟩

/-- The longest canonical lift sends every displayed root curve to its
opposite root curve, with the integral normalization absorbed in the
parameter. -/
public theorem carrierLongestWeyl_root_conjugation_exists (r : Root) (a : k) :
    ∃ c : k,
      carrierWeylWord (k := k) (canonicalWeylWord 11) *
          (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
          (carrierWeylWord (k := k) (canonicalWeylWord 11))⁻¹ =
        (rootMorphism (k := k) (-r)).onPoints (kPlusPoint c) := by
  obtain ⟨c, hc⟩ := carrierWeylWord_root_conjugation_forward (k := k)
    (canonicalWeylWord 11) r a
  refine ⟨c, ?_⟩
  change carrierWeylWord (k := k) (canonicalWeylWord 11) *
      (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
        (carrierWeylWord (k := k) (canonicalWeylWord 11))⁻¹ =
    (rootMorphism (k := k)
      (directRootAction (canonicalWeylWord 11) r)).onPoints (kPlusPoint c) at hc
  have hroot : directRootAction (canonicalWeylWord 11) r = -r := by
    fin_cases r <;> rfl
  rw [hroot] at hc
  exact hc

end Theory.AlgebraicGroup.G2Chevalley
