module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentNodeWords
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeCertificateChecks
public import Theory.GroupTheory.SubgroupClosureFinite
public import Theory.GroupTheory.SubgroupEnumerationBinary

/-!
# Finite certificates for the upper small even maximal-subgroup census

A short subfamily of the recorded node generators is certified by words for
all the original generators. For every nonzero binary membership signature,
a selected outside generator gives a Schreier generating family. Word equations
identify an edge, character equations prove core containment, or a finite
transition table bounds the subgroup and excludes a commuting element.

All numerical tests use the proved packed arithmetic. No diagnostic subgroup
or maximality assertion is assumed.

Source: Schreier's lemma, the finite two-group maximal-index theorem, and
Shinoda (1975), (2.3), pp. 81–82; the original numbering and root conventions
are those of `SmallEvenDescentEdgeData`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallEvenUpperCertificates
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
open SmallEvenDescentEdges SmallEvenDescentEdges.Certificates Collected

/-- The required three alternatives, with the original edge numbering. -/
def Classified (H : Subgroup SylowModel) : Prop :=
  H ≤ coreCharacter.ker ∨
  (∃ c, c ∈ Subgroup.centralizer (H : Set SylowModel) ∧ c ∉ H) ∨
  (∃ e : Fin 3617, H = edge e)

/-- A finite orbit bound for a generated subgroup and an excluded centralizer element. -/
structure OutsideData (m : Nat) where
  element : Nat
  size : Nat
  values : Fin size → Nat
  base : Fin size
  next : Fin size → Fin m → Fin size
  prev : Fin size → Fin m → Fin size

def OutsideData.Valid {m : Nat} (d : OutsideData m) (a : Fin m → Nat) : Prop :=
  code (decode (d.values d.base)) = code 1 ∧
  (∀ x k, packedMul (code (decode (d.values x))) (a k) =
    code (decode (d.values (d.next x k)))) ∧
  (∀ x k, d.next (d.prev x k) k = x) ∧
  (∀ x, code (decode (d.values x)) ≠ code (decode d.element)) ∧
  (∀ k, packedMul (a k) (code (decode d.element)) =
    packedMul (code (decode d.element)) (a k))

instance {m : Nat} (d : OutsideData m) (a : Fin m → Nat) : Decidable (d.Valid a) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem OutsideData.sound {m : Nat} (d : OutsideData m) (s : Fin m → SylowModel)
    (hv : d.Valid (fun k => code (s k))) :
    ∃ c, c ∈ Subgroup.centralizer
      (Subgroup.closure (Set.range s) : Set SylowModel) ∧
      c ∉ Subgroup.closure (Set.range s) := by
  obtain ⟨hb, hn, hp, ho, hc⟩ := hv
  refine ⟨decode d.element, ?_, ?_⟩
  · rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    apply code_injective
    simpa only [packedMul_code] using hc k
  · intro hm
    have hbound := closure_range_subset_range_of_transitions s
      (fun x => decode (d.values x)) d.base d.next d.prev
      (code_injective hb)
      (fun x k => code_injective (by simpa only [packedMul_code] using hn x k)) hp
    obtain ⟨x, hx⟩ := hbound hm
    exact ho x (congrArg code hx)

/-- The three types of finite branch certificate. -/
inductive BranchData (m : Nat) where
  | core
  | edge (index : Fin 3617) (words : ClosureWords m 10)
  | outside (data : OutsideData m)

def BranchData.Valid {m : Nat} (d : BranchData m) (a : Fin m → Nat) : Prop :=
  match d with
  | .core => ∀ k, coreCharacter (decode (a k)) = 1
  | .edge e w =>
      (∀ k, packedEval (fun j => code (fastGenerator e j)) (w.forward k) = a k) ∧
      (∀ k, packedEval a (w.backward k) = code (fastGenerator e k))
  | .outside d => d.Valid a

instance {m : Nat} (d : BranchData m) (a : Fin m → Nat) : Decidable (d.Valid a) := by
  cases d <;> unfold BranchData.Valid <;> infer_instance

theorem BranchData.sound {m : Nat} (d : BranchData m) (s : Fin m → SylowModel)
    (hv : d.Valid (fun k => code (s k))) :
    Classified (Subgroup.closure (Set.range s)) := by
  cases d with
  | core =>
    left
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact (show coreCharacter (s k) = 1 from by simpa only [decode_code] using hv k)
  | edge e w =>
    right; right
    refine ⟨e, ?_⟩
    have hg : fastGenerator e = generator e := by
      funext k
      exact congrFun (rawWord_eq.trans fastWord_eq) ((row e).generatorIndex k)
    have he := w.sound s (fastGenerator e) (MonoidHom.id SylowModel) ?_
    · simpa only [Subgroup.map_id, hg, SmallEvenDescentEdges.edge] using he
    · constructor
      · intro k
        apply code_injective
        simpa only [packedEval_code, MonoidHom.id_apply] using hv.1 k
      · intro k
        apply code_injective
        simpa only [packedEval_code, MonoidHom.id_apply] using hv.2 k
  | outside d => exact Or.inr (Or.inl (d.sound s hv))

/-- Flatten the two Schreier generators for each original generator. -/
def schreier {n : Nat} (s : Fin n → SylowModel) (σ : Fin n → Bool) (j : Fin n) :
    Fin (n+n) → SylowModel :=
  Fin.addCases (fun k => binarySchreierGenerator s (s j) σ (false, k))
    (fun k => binarySchreierGenerator s (s j) σ (true, k))

theorem range_schreier {n : Nat} (s : Fin n → SylowModel) (σ : Fin n → Bool) (j : Fin n) :
    Set.range (schreier s σ j) =
      Set.range (binarySchreierGenerator s (s j) σ) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine Fin.addCases ?_ ?_ k
    · intro k
      exact ⟨(false,k), by simp only [schreier, Fin.addCases_left]⟩
    · intro k
      exact ⟨(true,k), by simp only [schreier, Fin.addCases_right]⟩
  · rintro ⟨⟨b,k⟩, rfl⟩
    cases b
    · exact ⟨Fin.castAdd n k, Fin.addCases_left k⟩
    · exact ⟨Fin.natAdd n k, Fin.addCases_right k⟩

/-- Integer operations for the flattened Schreier generators. -/
def schreierCode {n : Nat} (s : Fin n → SylowModel) (σ : Fin n → Bool) (j : Fin n) :
    Fin (n+n) → Nat :=
  Fin.addCases
    (fun k => if σ k then packedMul (code (s k)) (packedInv (code (s j))) else code (s k))
    (fun k => if σ k then packedMul (code (s j)) (code (s k))
      else packedMul (packedMul (code (s j)) (code (s k))) (packedInv (code (s j))))

theorem schreierCode_eq {n : Nat} (s : Fin n → SylowModel) (σ : Fin n → Bool) (j : Fin n) :
    schreierCode s σ j = fun k => code (schreier s σ j k) := by
  funext k
  refine Fin.addCases ?_ ?_ k <;> intro k <;>
    cases h : σ k <;>
    simp only [schreierCode, schreier, Fin.addCases_left, Fin.addCases_right,
      binarySchreierGenerator, h, Bool.false_eq_true, if_false, if_true, packedMul_code, packedInv_code]

/-- A short generating subfamily and a checked row for each binary signature. -/
structure NodeData where
  rank : Nat
  select : Fin rank → Fin 10
  generate : Fin 10 → List (Fin rank)
  pivot : (Fin rank → Bool) → Fin rank
  branch : (Fin rank → Bool) → BranchData (rank+rank)

def NodeData.generators (d : NodeData) (i : Fin 599) : Fin d.rank → SylowModel :=
  fun k => fastNodeGenerator i (d.select k)

def NodeData.Valid (d : NodeData) (i : Fin 599) : Prop :=
  (∀ k, packedEval (fun j => code (d.generators i j)) (d.generate k) =
    code (fastNodeGenerator i k)) ∧
  (∀ σ : Fin d.rank → Bool,
    (∀ k, σ k = false) ∨
      (σ (d.pivot σ) = true ∧
        (d.branch σ).Valid (schreierCode (d.generators i) σ (d.pivot σ))))

instance (d : NodeData) (i : Fin 599) : Decidable (d.Valid i) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem NodeData.generates (d : NodeData) (i : Fin 599) (hv : d.Valid i) :
    Subgroup.closure (Set.range (d.generators i)) = smallEvenDescentNode i.succ := by
  have hg : fastNodeGenerator i = nodeGenerator i := by
    funext k
    exact congrFun (rawWord_eq.trans fastWord_eq) (nodeGeneratorIndex i k)
  rw [← nodeClosure_eq i]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    change d.generators i k ∈ Subgroup.closure (Set.range (nodeGenerator i))
    apply Subgroup.subset_closure
    exact ⟨d.select k, (congrFun hg (d.select k)).symm⟩
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    have he : evalWord (d.generators i) (d.generate k) = nodeGenerator i k := by
      apply code_injective
      simpa only [packedEval_code, hg] using hv.1 k
    rw [← he]
    exact evalWord_mem (d.generators i) (Subgroup.closure (Set.range (d.generators i)))
      (fun j => Subgroup.subset_closure (Set.mem_range_self j)) (d.generate k)

/-- Finite equation checks imply the classification for the original node. -/
theorem NodeData.sound (d : NodeData) (i : Fin 599) (hv : d.Valid i)
    (H : Subgroup SylowModel) (hmax : H ⋖ smallEvenDescentNode i.succ) : Classified H := by
  classical
  let s := d.generators i
  have hs := d.generates i hv
  let σ : Fin d.rank → Bool := fun k => decide (s k ∉ H)
  have hσ : ∀ k, σ k = true ↔ s k ∉ H := fun k => by simp [σ]
  rcases hv.2 σ with hz | ⟨hj,hb⟩
  · have hh : smallEvenDescentNode i.succ ≤ H := by
      rw [← hs, Subgroup.closure_le]
      rintro _ ⟨k,rfl⟩
      have := hz k
      simpa [σ] using this
    exact (hmax.lt.not_ge hh).elim
  · have he := binarySchreier_eq_relative hmax.le
      (relIndex_two_of_covBy (IsPGroup.of_card (p := 2) (n := 12) ReeTwo.SylowModel.card) hmax)
      s hs (s (d.pivot σ)) (hs ▸ Subgroup.subset_closure ⟨d.pivot σ,rfl⟩)
      ((hσ _).mp hj) σ hσ
    rw [schreierCode_eq] at hb
    have hc := (d.branch σ).sound (schreier s σ (d.pivot σ)) hb
    simpa only [range_schreier, he] using hc

end ReeTwo.SylowModel.SmallEvenUpperCertificates
