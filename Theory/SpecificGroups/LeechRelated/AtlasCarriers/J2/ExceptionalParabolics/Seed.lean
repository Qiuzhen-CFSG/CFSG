module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms

/-!
# Explicit candidate subgroups for the Hall--Janko parabolics

The central involution candidate is the sixth power of the standard
commutator word. The remaining elements are fixed words in the original
ATLAS generators and the checked normalizing involution. Thus all subgroup
carriers below are actual subgroups of the published permutation group or
its explicit extension.

The words were found by the GAP calculation in `source/discover-seed.g`;
`source/seed.json` retains the signed free words. They fix one common choice
for independent local calculations. The alphabet is `a,b,b⁻¹`, extended by
the normalizing involution in the outer case. Conversion from the original
right action to Lean's left action preserves word order, as in `J2.lean`.

Only the displayed involution identities are proved here. In particular,
`s` and `outerS` are candidates for Sylow subgroups; `q₂` is a candidate for
the second two-core. Their sizes, normality, full normalizers, quotients,
and all marking identities require separate Lean proofs. GAP output is
not used as a proof. `l₂` uses normal closure inside `p₂`, then its inclusion
in the ambient group; it is not ambient normal closure.

Source: R. A. Wilson et al., ATLAS `J2G1-p100B0` (original data retained in
`AtlasCarriers/source/`), and Aschbacher--Smith F.1.12(I)(10)--(11), p.263.
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed
open Theory.GroupTheory GeneratorPair

/-- The involution defining the first centralizer candidate. -/
def z : Carrier := (a * b * a * b⁻¹) ^ 6

theorem z_sq : z ^ 2 = 1 := by
  simpa only [z, ← pow_mul] using comm_word_pow_twelve

set_option maxRecDepth 20000 in
theorem z_ne_one : z ≠ 1 := by
  intro h
  have hh := congrArg inclusion h
  simp only [z, map_pow, map_mul, map_inv, map_one] at hh
  change (generatorA * generatorB * generatorA * generatorB⁻¹) ^ 6 = 1 at hh
  rw [generatorA_eq_table, generatorB_eq_table] at hh
  exact (by decide +kernel : (tableA * tableB * tableA * tableB⁻¹) ^ 6 ≠ 1) hh

/-- The first local group is an actual involution centralizer. -/
def l₁ : Subgroup Carrier := Subgroup.centralizer ({z} : Set Carrier)

/-- Evaluate words inside the actual generated carrier. -/
def localWord (w : List (Fin 3)) : Carrier := evalWord ![a, b, b⁻¹] w

def sWords : Fin 7 → List (Fin 3) := ![
  [2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2],
  [0],
  [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0],
  [2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0],
  [1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0],
  [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0],
  [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2]]

def q₂Words : Fin 6 → List (Fin 3) := ![
  [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0],
  [0],
  [0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1],
  [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1],
  [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1],
  [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2]]

/-- Fixed candidate Sylow generators, as elements of the carrier. -/
def sGenerator (i : Fin 7) : Carrier := localWord (sWords i)

/-- The chosen subgroup; its Sylow property remains a calculation. -/
def s : Subgroup Carrier := Subgroup.closure (Set.range sGenerator)

def q₂Generator (i : Fin 6) : Carrier := localWord (q₂Words i)

/-- The chosen second radical candidate. -/
def q₂ : Subgroup Carrier := Subgroup.closure (Set.range q₂Generator)

/-- Its full normalizer in the concrete carrier. -/
def p₂ : Subgroup Carrier := Subgroup.normalizer (q₂ : Set Carrier)

/-- Relative normal closure in the second parabolic candidate. -/
def l₂ : Subgroup Carrier :=
  (Subgroup.normalClosure ((s.subgroupOf p₂ : Subgroup p₂) : Set p₂)).map p₂.subtype

def L : Fin 2 → Subgroup Carrier := ![l₁, l₂]

def outerWord : List (Fin 4) :=
  [3, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1]

/-- A fixed candidate outer Sylow generator in the permutation extension. -/
def outerElement : Extension :=
  evalWord ![intoExtension a, intoExtension b, intoExtension b⁻¹,
    extensionInvolution] outerWord

def outerS : Subgroup Extension := s.map intoExtension ⊔ Subgroup.zpowers outerElement

/-- The same two local factors included in the extension. -/
def outerL (i : Fin 2) : Subgroup Extension := (L i).map intoExtension

/-- The numerator appearing in the first outer quotient. -/
def l₁s : Subgroup Extension := outerL 0 ⊔ outerS

end Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed
