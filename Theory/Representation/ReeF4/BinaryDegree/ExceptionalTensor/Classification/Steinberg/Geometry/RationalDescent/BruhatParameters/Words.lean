module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Embedding

/-!
# Literal words for F4 rational Bruhat parameters

The unipotent factors are ordered products of actual root elements. The torus
factor is the product of the four representation coroots `n(t) n(1)⁻¹`, and
the Weyl factor is a finite product of simple normalizer words at parameter
one. Their finite-field counterparts commute with the actual split embedding.
These equations allow a rational parameter tuple to be lifted as a word;
they do not assert that arbitrary carrier points have such parameters.

Source: Steinberg, *Lectures on Chevalley Groups*, Theorem 7 and its third
corollary (`refs/KGroup/GLS3/Chapter2St1.tex`, pp. 64–67).
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters

universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- An enumeration of precisely the 24 positive roots, with no repetitions. -/
abbrev PositiveOrdering := Fin 24 ≃ {r : F4Chevalley.Root // typeF4RootPairing_base.IsPos r}

/-- A literal ordered product; no root collection is implicit in this definition. -/
def rootProduct {n : ℕ} (p : Fin n → F4Chevalley.Root) (a : Fin n → F) :
    Variety.Point (F4Chevalley.Carrier (k := F)) :=
  (List.ofFn fun i => algebraicRootElement (p i) (a i)).prod

/-- The four actual representation coroots, in numbered simple-root order. -/
def corootProduct (t : Fin 4 → Fˣ) : Variety.Point (F4Chevalley.Carrier (k := F)) :=
  (List.ofFn fun i => algebraicCorootElement (typeF4SimpleRootIndex i) (t i)).prod

/-- An actual prime-field word, rather than an abstract Weyl-group label. -/
def weylWord (l : List (Fin 4)) : Variety.Point (F4Chevalley.Carrier (k := F)) :=
  (l.map fun i => algebraicNElement (typeF4SimpleRootIndex i) (1 : Fˣ)).prod

/-- The opposite-unipotent chart followed by a prime-field Weyl word.
Coverage of these charts is a separate mathematical assertion. -/
def cell {n n' : ℕ} (p : Fin n → F4Chevalley.Root) (q : Fin n' → F4Chevalley.Root)
    (a : Fin n → F) (t : Fin 4 → Fˣ) (b : Fin n' → F) (l : List (Fin 4)) :
    Variety.Point (F4Chevalley.Carrier (k := F)) :=
  rootProduct p a * corootProduct t * rootProduct q b * weylWord l

def finiteRootProduct (m : ℕ) {n : ℕ} (p : Fin n → F4Chevalley.Root)
    (a : Fin n → CoefficientField m) : SplitGroup m :=
  (List.ofFn fun i => rootGeneratorInGroup m (p i) (a i)).prod

/-- The finite word uses exactly the algebraic coroot convention. -/
def finiteNWord (m : ℕ) (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ) : SplitGroup m :=
  rootGeneratorInGroup m r t * rootGeneratorInGroup m (-r) (-((t : CoefficientField m)⁻¹)) *
    rootGeneratorInGroup m r t

def finiteCorootProduct (m : ℕ) (t : Fin 4 → (CoefficientField m)ˣ) : SplitGroup m :=
  (List.ofFn fun i => finiteNWord m (typeF4SimpleRootIndex i) (t i) *
    (finiteNWord m (typeF4SimpleRootIndex i) 1)⁻¹).prod

def finiteWeylWord (m : ℕ) (l : List (Fin 4)) : SplitGroup m :=
  (l.map fun i => finiteNWord m (typeF4SimpleRootIndex i) 1).prod

theorem splitEmbedding_rootProduct {m n : ℕ} (f : CoefficientField m →+* F)
    (p : Fin n → F4Chevalley.Root) (a : Fin n → CoefficientField m) :
    splitEmbedding f (finiteRootProduct m p a) = rootProduct p (f ∘ a) := by
  simp only [finiteRootProduct, rootProduct, map_list_prod, List.map_ofFn,
    Function.comp_def, splitEmbedding_rootGenerator]

theorem splitEmbedding_NWord {m : ℕ} (f : CoefficientField m →+* F)
    (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ) :
    splitEmbedding f (finiteNWord m r t) =
      algebraicNElement r (Units.map f.toMonoidHom t) := by
  simp only [finiteNWord, algebraicNElement, map_mul, splitEmbedding_rootGenerator,
    map_neg, map_inv₀, Units.coe_map]
  rfl

theorem splitEmbedding_corootProduct {m : ℕ} (f : CoefficientField m →+* F)
    (t : Fin 4 → (CoefficientField m)ˣ) :
    splitEmbedding f (finiteCorootProduct m t) =
      corootProduct (fun i => Units.map f.toMonoidHom (t i)) := by
  simp only [finiteCorootProduct, corootProduct, map_list_prod, List.map_ofFn,
    Function.comp_def, map_mul, map_inv, splitEmbedding_NWord, map_one,
    algebraicCorootElement]

theorem splitEmbedding_weylWord {m : ℕ} (f : CoefficientField m →+* F)
    (l : List (Fin 4)) :
    splitEmbedding f (finiteWeylWord m l) = weylWord (F := F) l := by
  simp only [finiteWeylWord, weylWord, map_list_prod, List.map_map, Function.comp_def,
    splitEmbedding_NWord, map_one]

/-- Explicit transport of the entire four-factor word. This gives the parent
descent proof its finite-group witness once the parameters are recovered. -/
theorem splitEmbedding_cell {m n n' : ℕ} (f : CoefficientField m →+* F)
    (p : Fin n → F4Chevalley.Root) (q : Fin n' → F4Chevalley.Root)
    (a : Fin n → CoefficientField m) (t : Fin 4 → (CoefficientField m)ˣ)
    (b : Fin n' → CoefficientField m) (l : List (Fin 4)) :
    splitEmbedding f (finiteRootProduct m p a * finiteCorootProduct m t *
      finiteRootProduct m q b * finiteWeylWord m l) =
      cell p q (f ∘ a) (fun i => Units.map f.toMonoidHom (t i)) (f ∘ b) l := by
  simp only [cell, map_mul, splitEmbedding_rootProduct, splitEmbedding_corootProduct,
    splitEmbedding_weylWord]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
