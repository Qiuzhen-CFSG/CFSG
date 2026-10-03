module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdges
public import Theory.GroupTheory.SubgroupEnumerationBinary
public import Theory.SpecificGroups.ReeTwo.SylowPackedArithmetic

/-!+# Word certificates for maximal subgroups of the small even nodes

A chosen outside generator gives the binary Schreier generators of an actual
maximal subgroup. Packed word equations identify their closure with an edge,
put it in the core-character kernel, or exhibit a commuting element. In the
last case a separate nonmembership certificate completes the alternative.

Source: Schreier's lemma and the root coordinates of Shinoda (1975), (2.3),
pp. 81–82. Diagnostic word searches only supply witnesses to these equations.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallEvenMaximalBranches
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
open SmallEvenDescentEdges Collected

def signatureIndex {n : Nat} (σ : Fin n → Bool) : Nat :=
  (List.ofFn σ).foldr (fun b v => b.toNat + 2 * v) 0

def schreier {n : Nat} (s : Fin n → SylowModel) (σ : Fin n → Bool) (j : Fin n) :
    Fin (n + n) → SylowModel :=
  Fin.addCases (fun k => binarySchreierGenerator s (s j) σ (false, k))
    (fun k => binarySchreierGenerator s (s j) σ (true, k))

theorem range_schreier {n : Nat} (s : Fin n → SylowModel) (σ : Fin n → Bool)
    (j : Fin n) :
    Set.range (schreier s σ j) = Set.range (binarySchreierGenerator s (s j) σ) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · exact ⟨(false, k), by simp only [schreier, Fin.addCases_left]⟩
    · exact ⟨(true, k), by simp only [schreier, Fin.addCases_right]⟩
  · rintro ⟨⟨b, k⟩, rfl⟩
    cases b
    · exact ⟨k.castAdd n, by simp only [schreier, Fin.addCases_left]⟩
    · exact ⟨k.natAdd n, by simp only [schreier, Fin.addCases_right]⟩

def packedSchreier {n : Nat} (s : Fin n → SylowModel) (σ : Fin n → Bool)
    (j : Fin n) : Fin (n + n) → Nat :=
  Fin.addCases
    (fun k => if σ k then packedMul (code (s k)) (packedInv (code (s j))) else code (s k))
    (fun k => if σ k then packedMul (code (s j)) (code (s k))
      else packedMul (packedMul (code (s j)) (code (s k))) (packedInv (code (s j))))

theorem packedSchreier_eq {n : Nat} (s : Fin n → SylowModel) (σ : Fin n → Bool)
    (j : Fin n) : packedSchreier s σ j = fun k => code (schreier s σ j k) := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;>
    simp only [packedSchreier, schreier, Fin.addCases_left, Fin.addCases_right,
      binarySchreierGenerator] <;> split <;>
    simp_all only [packedInv_code, packedMul_code]

def PackedEquality {n m : Nat} (w : ClosureWords n m)
    (a : Fin n → SylowModel) (b : Fin m → SylowModel) : Prop :=
  (∀ k, packedEval (fun j => code (b j)) (w.forward k) = code (a k)) ∧
    ∀ k, packedEval (fun j => code (a j)) (w.backward k) = code (b k)

instance {n m : Nat} (w : ClosureWords n m)
    (a : Fin n → SylowModel) (b : Fin m → SylowModel) : Decidable (PackedEquality w a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem PackedEquality.sound {n m : Nat} (w : ClosureWords n m)
    (a : Fin n → SylowModel) (b : Fin m → SylowModel) (h : PackedEquality w a b) :
    Subgroup.closure (Set.range a) = Subgroup.closure (Set.range b) := by
  have hv : w.Valid a b (MonoidHom.id _) := by
    constructor
    · intro k
      apply code_injective
      simpa only [packedEval_code, MonoidHom.id_apply] using h.1 k
    · intro k
      apply code_injective
      simpa only [packedEval_code, MonoidHom.id_apply] using h.2 k
  simpa only [Subgroup.map_id] using w.sound a b (MonoidHom.id _) hv

theorem fastGenerator_eq (e : Fin 3617) : Certificates.fastGenerator e = generator e := by
  funext k
  exact congrFun (Certificates.rawWord_eq.trans Certificates.fastWord_eq)
    ((row e).generatorIndex k)

theorem fastNodeGenerator_eq (i : Fin 599) :
    Certificates.fastNodeGenerator i = nodeGenerator i := by
  funext k
  exact congrFun (Certificates.rawWord_eq.trans Certificates.fastWord_eq)
    (nodeGeneratorIndex i k)

theorem generated_of_packed {n : Nat} (i : Fin 599) (s : Fin n → SylowModel)
    (w : ClosureWords n 10) (h : PackedEquality w s (Certificates.fastNodeGenerator i)) :
    Subgroup.closure (Set.range s) = smallEvenDescentNode i.succ := by
  have he := h.sound w s (Certificates.fastNodeGenerator i)
  rw [fastNodeGenerator_eq] at he
  exact he.trans (nodeClosure_eq i)

inductive BranchData (n : Nat) where
  | core
  | edge (index : Fin 3617) (words : ClosureWords (n + n) 10)
  | noncentric (witness : Nat)

def BranchData.Equations {n : Nat} (d : BranchData n) (s : Fin n → SylowModel)
    (σ : Fin n → Bool) (j : Fin n) : Prop :=
  let a := packedSchreier s σ j
  match d with
  | .core => ∀ k, coreCharacter (decode (a k)) = 1
  | .edge e w =>
      (∀ k, packedEval (fun k => code (Certificates.fastGenerator e k)) (w.forward k) = a k) ∧
        ∀ k, packedEval a (w.backward k) = code (Certificates.fastGenerator e k)
  | .noncentric c => ∀ k, packedMul c (a k) = packedMul (a k) c

instance {n : Nat} (d : BranchData n) (s : Fin n → SylowModel)
    (σ : Fin n → Bool) (j : Fin n) : Decidable (d.Equations s σ j) := by
  cases d <;> unfold BranchData.Equations <;> infer_instance

def BranchData.Separation {n : Nat} (d : BranchData n) (s : Fin n → SylowModel)
    (σ : Fin n → Bool) (j : Fin n) : Prop :=
  match d with
  | .noncentric c => decode c ∉ Subgroup.closure (Set.range (schreier s σ j))
  | _ => True

def BranchData.needsSeparation {n : Nat} (d : BranchData n) : Bool :=
  match d with
  | .noncentric _ => true
  | _ => false

theorem BranchData.separation_of_false {n : Nat} (d : BranchData n)
    (h : d.needsSeparation = false) (s : Fin n → SylowModel)
    (σ : Fin n → Bool) (j : Fin n) : d.Separation s σ j := by
  cases d <;> simp_all only [needsSeparation, Bool.true_eq_false, Separation]

def Classified (H : Subgroup SylowModel) : Prop :=
  H ≤ coreCharacter.ker ∨
    (∃ c, c ∈ Subgroup.centralizer (H : Set SylowModel) ∧ c ∉ H) ∨
    ∃ e : Fin 3617, H = edge e

theorem BranchData.sound {n : Nat} (d : BranchData n) (s : Fin n → SylowModel)
    (σ : Fin n → Bool) (j : Fin n) (he : d.Equations s σ j)
    (hn : d.Separation s σ j) :
    Classified (Subgroup.closure (Set.range (schreier s σ j))) := by
  cases d with
  | core =>
      left
      rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      change coreCharacter (schreier s σ j k) = 1
      simpa only [BranchData.Equations, packedSchreier_eq, decode_code] using he k
  | edge e w =>
      right; right
      refine ⟨e, ?_⟩
      have hv : PackedEquality w (schreier s σ j) (Certificates.fastGenerator e) := by
        simpa only [BranchData.Equations, packedSchreier_eq, PackedEquality] using he
      have hh := hv.sound w _ _
      rw [fastGenerator_eq] at hh
      exact hh
  | noncentric c =>
      right; left
      refine ⟨decode c, ?_, hn⟩
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      apply code_injective
      have hh := he k
      simpa only [BranchData.Equations, packedSchreier_eq, packedMul, decode_code,
        collectedMul_eq] using hh.symm

theorem classify_of_checks {n : Nat} (i : Fin 600) (s : Fin n → SylowModel)
    (hs : Subgroup.closure (Set.range s) = smallEvenDescentNode i)
    (pivot : (Fin n → Bool) → Fin n) (data : (Fin n → Bool) → BranchData n)
    (hp : ∀ (σ : Fin n → Bool), (∃ k, σ k = true) → σ (pivot σ) = true)
    (he : ∀ σ, (∃ k, σ k = true) → (data σ).Equations s σ (pivot σ))
    (hn : ∀ σ, (∃ k, σ k = true) → (data σ).Separation s σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode i) : Classified H := by
  classical
  let σ : Fin n → Bool := fun k => decide (s k ∉ H)
  have hex : ∃ k, σ k = true := by
    by_contra hh
    have hle : smallEvenDescentNode i ≤ H := by
      rw [← hs, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      by_contra hk
      change s k ∉ H at hk
      exact hh ⟨k, by simpa only [σ, decide_eq_true_eq] using hk⟩
    exact hH.lt.not_ge hle
  have hout : s (pivot σ) ∉ H := by simpa only [σ, decide_eq_true_eq] using hp σ hex
  have hL := binarySchreier_eq_relative hH.le
    (relIndex_two_of_covBy (IsPGroup.of_card (n := 12) card) hH) s hs
    (s (pivot σ)) (hs ▸ Subgroup.subset_closure ⟨pivot σ, rfl⟩) hout σ
    (fun k => by simp only [σ, decide_eq_true_eq])
  have hc := (data σ).sound s σ (pivot σ) (he σ hex) (hn σ hex)
  rwa [range_schreier, hL] at hc

end ReeTwo.SylowModel.SmallEvenMaximalBranches
