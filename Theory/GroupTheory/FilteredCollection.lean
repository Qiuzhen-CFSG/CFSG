module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Order.Lemmas
public meta import Lean.Elab.Tactic.Omega

/-!
This module proves the abstract collection theorem needed for arbitrary-order
Chevalley products.  Factors with a common index combine additively.  Exchanging two
distinct adjacent supported factors leaves them in the opposite order and emits an
explicit word whose indices have strictly larger degree than both exchanged indices.

The proof first carries an explicit residual word through the degree filtration.  At
stage `n`, indices of degree `< n` already occur in the requested relative order and the
residual has degree at least `n`.  The next exact-degree layer is extracted, interleaved
with the collected prefix modulo an explicit correction word, and the correction word
is appended to the next residual.  A common finite degree bound makes the final residual
empty.  Thus the argument constructs the distributed correction words rather than
assuming an ordered-product membership or parameter-distribution conclusion.
-/

namespace FilteredCollection

variable {I A G : Type*} [AddMonoid A] [Group G]

@[expose] public def wordProduct (factor : I → A → G) (word : List (I × A)) : G :=
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
public theorem filteredCollection_exists_params
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

end FilteredCollection
