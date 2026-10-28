module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.Recognition.ComponentSpectrum

/-!
# The actual centralizer layer in the component orbit

Write `E = componentOrbit L B`. The subgroup used by GLS2 Theorem 25.14,
Steps 2--3, is the intrinsic layer of `C_E(a)`, mapped into the ambient group.
In particular `diagonalLayer` does not mean an arbitrary subgroup supplied
with generation or representation properties. `diagonalOvergroup` is its
join with `B`; the source exceptional overgroup also contains `orbitCenter`.

These definitions retain relative subgroup types: the layer is taken inside
the centralizer in `E`, and the center is taken inside `E`. The elementary
containments below do not assert the missing diagonal decomposition or
maximality theorem (GLS2 Lemmas 3.25 and 3.27). The final lemma makes precise
a sufficient additional input for quotient evenness: odd-order solvability
of this particular nontrivial perfect quotient. It does not prove that input.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup

variable {G : Type*} [Group G]

/-- The literal centralizer of `a` inside its component orbit, viewed in `G`. -/
def orbitCentralizer (L B : Subgroup G) (a : G) : Subgroup G :=
  componentOrbit L B ⊓ centralizer ({a} : Set G)

/-- The actual layer `E(C_E(a))`, mapped into `G`. -/
def diagonalLayer (L B : Subgroup G) (a : G) : Subgroup G :=
  (componentLayer (orbitCentralizer L B a)).map (orbitCentralizer L B a).subtype

/-- The subgroup called `Y = KB` in the source. -/
def diagonalOvergroup (L B : Subgroup G) (a : G) : Subgroup G :=
  diagonalLayer L B a ⊔ B

/-- The center of the actual orbit, mapped into the ambient group. -/
def orbitCenter (L B : Subgroup G) : Subgroup G :=
  (center (componentOrbit L B)).map (componentOrbit L B).subtype

/-- The mapped intrinsic layer lies in its actual local centralizer. -/
theorem diagonalLayer_le_orbitCentralizer (L B : Subgroup G) (a : G) :
    diagonalLayer L B a ≤ orbitCentralizer L B a :=
  map_subtype_le _

/-- In particular, the layer centralizes the distinguished involution. -/
theorem diagonalLayer_le_centralizer (L B : Subgroup G) (a : G) :
    diagonalLayer L B a ≤ centralizer ({a} : Set G) :=
  (diagonalLayer_le_orbitCentralizer L B a).trans inf_le_right

/-- The local layer is a subgroup of the original component orbit. -/
theorem diagonalLayer_le_componentOrbit (L B : Subgroup G) (a : G) :
    diagonalLayer L B a ≤ componentOrbit L B :=
  (diagonalLayer_le_orbitCentralizer L B a).trans inf_le_left

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

open scoped IsMulCommutative in
/-- The source four-group centralizes its distinguished involution. -/
theorem Hypotheses.fourGroup_le_centralizer (h : Hypotheses ρ L B a) :
    B ≤ Subgroup.centralizer ({a} : Set G) := by
  let := h.elementary
  intro b hb
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val ((Commute.all (⟨b, hb⟩ : B) ⟨a, h.mem⟩).eq)

/-- The actual subgroup `Y` centralizes `a`, without a diagonal certificate. -/
theorem Hypotheses.diagonalOvergroup_le_centralizer (h : Hypotheses ρ L B a) :
    diagonalOvergroup L B a ≤ Subgroup.centralizer ({a} : Set G) :=
  sup_le (diagonalLayer_le_centralizer L B a) h.fourGroup_le_centralizer

/-- The precise additional odd-order input sufficient to produce the
involution needed for even-order Burnside recognition. The component quotient
is nontrivial and perfect, so odd-order solvability excludes odd cardinality;
Cauchy's theorem then supplies an actual involution. This input is not deduced
from the spectrum condition. -/
theorem Hypotheses.quotient_involution_of_odd_solvable [Finite G] (h : Hypotheses ρ L B a)
    (hodd : Odd (Nat.card (L ⧸ center L)) → Group.IsSolvable (L ⧸ center L)) :
    ∃ t : L ⧸ center L, orderOf t = 2 := by
  let := h.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  apply exists_prime_orderOf_dvd_card' 2
  apply even_iff_two_dvd.mp
  apply Nat.not_odd_iff_even.mp
  intro ho
  exact Group.IsPerfect.not_isSolvable (L ⧸ center L) (hodd ho)

end Representation.QuadraticFourGroup

end
