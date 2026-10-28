module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.Contracts
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed

/-!
# Soundness of the Sylow factorization certificates

A positive recovery tree constructs actual members of each literal seed.
Shared three-point checks prove equations t*s = q*u for the eight marked
Sylow generators. These equations preserve the set of products seed*t under
right multiplication. Starting at one and iterating through the mixed-radix
normal form proves the required left seed factorization.

The tables need neither the order of a seed nor distinctness of its cosets.
Source: Parrott (1972), section 5, p.683; the marking and candidate data in
`ExtensionObstructions/source/README.md`.
-/

@[expose] public section

namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
open OuterOddSubgroups.OverlapCentralizers
open ConverseLocalCoverage.DoubleCosetCertificate

def permToEnd : Equiv.Perm (Fin 1600) →* Function.End (Fin 1600) where
  toFun p := p.toFun
  map_one' := rfl
  map_mul' _ _ := rfl

def action : Atlas1600Group →* Function.End (Fin 1600) :=
  permToEnd.comp atlas1600Subgroup.subtype

def pointGenerator (j : Fin 10) : Function.End (Fin 1600) := Packed.pointMap j

theorem pointGenerator_eq (j : Fin 10) :
    pointGenerator j = permToEnd (Packed.generator j) :=
  funext (Packed.pointMap_eq j)

def normalMap (n : Fin 2048) : Function.End (Fin 1600) :=
  pointGenerator 2 ^ (n.val % 2) * pointGenerator 3 ^ (n.val / 2 % 2) *
  pointGenerator 4 ^ (n.val / 4 % 4) * pointGenerator 5 ^ (n.val / 16 % 2) *
  pointGenerator 6 ^ (n.val / 32 % 4) * pointGenerator 7 ^ (n.val / 128 % 2) *
  pointGenerator 8 ^ (n.val / 256 % 4) * pointGenerator 9 ^ (n.val / 1024 % 2)

theorem normalMap_eq (n : Fin 2048) :
    normalMap n = action (atlas1600SylowTwoNormalForm n) := by
  change normalMap n = permToEnd (atlas1600SylowTwoNormalForm n).val
  rw [atlas1600SylowTwoNormalForm_val]
  simp only [normalMap, pointGenerator_eq, map_mul, map_pow]
  rfl

def generator : Fin 8 → Atlas1600Group :=
  ![atlas1600ParrottAssignment .s1, atlas1600ParrottAssignment .s2,
    atlas1600ParrottAssignment .s3, atlas1600ParrottAssignment .s4,
    atlas1600ParrottAssignment .s5, atlas1600ParrottAssignment .s6,
    atlas1600ParrottAssignment .s7, atlas1600ParrottAssignment .s8]

def generatorMap (j : Fin 8) : Function.End (Fin 1600) :=
  pointGenerator ⟨j.val + 2, by omega⟩

theorem generatorMap_eq (j : Fin 8) : generatorMap j = action (generator j) := by
  unfold generatorMap
  rw [pointGenerator_eq]
  change permToEnd _ = permToEnd (generator j).val
  congr 1
  fin_cases j <;> simp [generator, Packed.generator, atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation]

def sameBase (a b : Function.End (Fin 1600)) : Bool :=
  (a 0 == b 0) && (a 1 == b 1) && (a 2 == b 2)

theorem eq_of_sameBase {x y : Atlas1600Group}
    (h : sameBase (action x) (action y) = true) : x = y := by
  simp only [sameBase, Bool.and_eq_true, beq_iff_eq] at h
  exact threePoint_ext h.1.1 h.1.2 h.2

theorem normal_zero : atlas1600SylowTwoNormalForm 0 = 1 := by
  simp [atlas1600SylowTwoNormalForm_eq]

/-- A recovery row stores a normal form, a generator and an earlier row. -/
def recoveryQ (d : Nat) (j : Fin 64) : Fin 2048 :=
  ⟨(d >>> (28 * j.val)) % 2048, Nat.mod_lt _ (by decide)⟩
def recoveryG (d : Nat) (j : Fin 64) : Fin 2048 :=
  ⟨(d >>> (28 * j.val + 11)) % 2048, Nat.mod_lt _ (by decide)⟩
def recoveryParent (d : Nat) (j : Fin 64) : Fin 64 :=
  ⟨(d >>> (28 * j.val + 22)) % 64, Nat.mod_lt _ (by decide)⟩
def recoveryTest (i : Fin 122) (d : Nat) (j : Fin 64) : Bool :=
  if j.val = 0 then recoveryQ d j == 0 else
    decide ((recoveryParent d j).val < j.val) &&
    decide (recoveryG d j ∈ seedIndices i) &&
    sameBase (normalMap (recoveryQ d j))
      (normalMap (recoveryG d j) * normalMap (recoveryQ d (recoveryParent d j)))

theorem recovery_mem (i : Fin 122) (d : Nat)
    (h : ∀ j, recoveryTest i d j = true) (j : Fin 64) :
    atlas1600SylowTwoNormalForm (recoveryQ d j) ∈ seed i := by
  have aux (n : Nat) : ∀ hn : n < 64,
      atlas1600SylowTwoNormalForm (recoveryQ d ⟨n, hn⟩) ∈ seed i := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have ht := h ⟨n, hn⟩
      by_cases hz : n = 0
      · subst n
        simp only [recoveryTest, ↓reduceIte, beq_iff_eq] at ht
        rw [ht, normal_zero]
        exact (seed i).one_mem
      · simp only [recoveryTest, hz, ↓reduceIte, Bool.and_eq_true,
          decide_eq_true_eq] at ht
        have he : atlas1600SylowTwoNormalForm (recoveryQ d ⟨n, hn⟩) =
            atlas1600SylowTwoNormalForm (recoveryG d ⟨n, hn⟩) *
              atlas1600SylowTwoNormalForm (recoveryQ d (recoveryParent d ⟨n, hn⟩)) := by
          apply eq_of_sameBase
          simpa only [map_mul, ← normalMap_eq] using ht.2
        rw [he]
        exact (seed i).mul_mem (Subgroup.subset_closure ⟨_, ht.1.2, rfl⟩)
          (ih _ ht.1.1 _)
  exact aux j.val j.isLt

/-- A transition equation stores t, a generator number, q, and t'. -/
def transitionT (c : Nat) : Fin 2048 := ⟨c % 2048, Nat.mod_lt _ (by decide)⟩
def transitionG (c : Nat) : Fin 8 := ⟨(c >>> 11) % 8, Nat.mod_lt _ (by decide)⟩
def transitionQ (c : Nat) : Fin 2048 := ⟨(c >>> 14) % 2048, Nat.mod_lt _ (by decide)⟩
def transitionU (c : Nat) : Fin 2048 := ⟨(c >>> 25) % 2048, Nat.mod_lt _ (by decide)⟩
def transitionTest (c : Nat) : Bool :=
  sameBase (normalMap (transitionT c) * generatorMap (transitionG c))
    (normalMap (transitionQ c) * normalMap (transitionU c))

theorem transition_eq (c : Nat) (h : transitionTest c = true) :
    atlas1600SylowTwoNormalForm (transitionT c) * generator (transitionG c) =
      atlas1600SylowTwoNormalForm (transitionQ c) *
        atlas1600SylowTwoNormalForm (transitionU c) := by
  apply eq_of_sameBase
  simpa only [transitionTest, normalMap_eq, generatorMap_eq, map_mul] using h

def Covered (i : Fin 122) (x : Atlas1600Group) : Prop :=
  ∃ (q : seed i) (a : Fin 32), x = q.val * transversal i a

theorem all_covered (i : Fin 122)
    (hzero : transversal i 0 = 1)
    (hstep : ∀ (a : Fin 32) (j : Fin 8), Covered i (transversal i a * generator j))
    (n : Fin 2048) : Covered i (atlas1600SylowTwoNormalForm n) := by
  have h1 : Covered i 1 := ⟨1, 0, by simp [hzero]⟩
  have step (x : Atlas1600Group) (hx : Covered i x) (j : Fin 8) :
      Covered i (x * generator j) := by
    obtain ⟨q, a, rfl⟩ := hx
    obtain ⟨r, b, hr⟩ := hstep a j
    refine ⟨q * r, b, ?_⟩
    change q.val * transversal i a * generator j = (q.val * r.val) * transversal i b
    rw [mul_assoc, hr, ← mul_assoc]
  have power (x : Atlas1600Group) (hx : Covered i x) (j : Fin 8) (e : Nat) :
      Covered i (x * generator j ^ e) := by
    induction e with
    | zero => simpa using hx
    | succ e ih => simpa only [pow_succ, ← mul_assoc] using step _ ih j
  rw [atlas1600SylowTwoNormalForm_eq]
  exact power _ (power _ (power _ (power _ (power _ (power _ (power _
    (by simpa [generator] using power 1 h1 0 (n.val % 2)) 1 (n.val / 2 % 2))
    2 (n.val / 4 % 4)) 3 (n.val / 16 % 2)) 4 (n.val / 32 % 4))
    5 (n.val / 128 % 2)) 6 (n.val / 256 % 4)) 7 (n.val / 1024 % 2)
/-- An entry refers to a shared equation, a recovered member, and a target coset. -/
def rowEquation (r : Nat) (a : Fin 32) (j : Fin 8) : Fin 5940 :=
  ⟨(r >>> (24 * (8 * a.val + j.val))) % 8192 % 5940, Nat.mod_lt _ (by decide)⟩
def rowMember (r : Nat) (a : Fin 32) (j : Fin 8) : Fin 64 :=
  ⟨(r >>> (24 * (8 * a.val + j.val) + 13)) % 64, Nat.mod_lt _ (by decide)⟩
def rowTarget (r : Nat) (a : Fin 32) (j : Fin 8) : Fin 32 :=
  ⟨(r >>> (24 * (8 * a.val + j.val) + 19)) % 32, Nat.mod_lt _ (by decide)⟩

def rowTest (codes : Fin 5940 → Nat) (i : Fin 122) (d r : Nat)
    (a : Fin 32) (j : Fin 8) : Bool :=
  let c := codes (rowEquation r a j)
  (transitionT c == transversalPattern (seedTransversalPattern i) a) &&
  (transitionG c == j) && (transitionQ c == recoveryQ d (rowMember r a j)) &&
  (transitionU c == transversalPattern (seedTransversalPattern i) (rowTarget r a j))

theorem row_step (codes : Fin 5940 → Nat)
    (hc : ∀ k, transitionTest (codes k) = true)
    (i : Fin 122) (d r : Nat) (hm : ∀ k, recoveryTest i d k = true)
    (ht : ∀ a j, rowTest codes i d r a j = true) (a : Fin 32) (j : Fin 8) :
    Covered i (transversal i a * generator j) := by
  have hh := ht a j
  simp only [rowTest, Bool.and_eq_true, beq_iff_eq] at hh
  have he := transition_eq _ (hc (rowEquation r a j))
  rw [hh.1.1.1, hh.1.1.2, hh.1.2, hh.2] at he
  exact ⟨⟨_, recovery_mem i d hm (rowMember r a j)⟩, rowTarget r a j, he⟩

theorem transversal_zero (i : Fin 122) : transversal i 0 = 1 := by
  have ht : ∀ i : Fin 122, transversalPattern (seedTransversalPattern i) 0 = 0 := by
    apply Atlas1600OrderCertificate.allFin
    decide +kernel
  rw [transversal, ht, normal_zero]

theorem row_covered (codes : Fin 5940 → Nat)
    (hc : ∀ k, transitionTest (codes k) = true)
    (i : Fin 122) (d r : Nat) (hm : ∀ k, recoveryTest i d k = true)
    (ht : ∀ a j, rowTest codes i d r a j = true) (n : Fin 2048) :
    Covered i (atlas1600SylowTwoNormalForm n) :=
  all_covered i (transversal_zero i) (row_step codes hc i d r hm ht) n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
