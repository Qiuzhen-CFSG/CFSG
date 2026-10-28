module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Markings
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Literal ambient subgroups for the exterior branch of Section 12.5

Pulling back the standard wedge subspaces along the marking fixes V₁, V₃,
V₄, V₆ and V₇ in the original ambient group. Their local groups are actual
normalizers and solvable residuals, and Rᵢ is the two-core of LᵢT.
No normality, component recognition or normalizer containment is assumed
by these definitions. In particular, aligning the flag with T is a separate
source construction.

Source: Aschbacher--Smith, Notation preceding 12.5.2, printed p.817.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The source choice of coordinates in which T preserves the natural flag.
The actor extends the original quotient marking on L, so it cannot be
replaced by an unrelated representation of LT. Its existence is a separate
source obligation, using the full-module linear normalizer. -/
structure SylowExteriorMarking (D : ChosenModule T L V) where
  marking : ExteriorMarking D
  actor : (L ⊔ (T : Subgroup G) : Subgroup G) →*
    Representation.SL5TenDimensional.Group
  actor_component : ∀ l : L,
    actor ⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩ =
      marking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)
  normalizes : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
  equivariant : ∀ (h : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
    marking.coordinates ⟨(h : G) * v * (h : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes h.property) v).mp v.property⟩ =
        Multiplicative.ofAdd (Representation.SL5TenDimensional.exteriorAction 2 (actor h)
          (marking.coordinates v).toAdd)
  sylow_flag : ∀ t : T,
    actor ⟨t, (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) t.property⟩ ∈
    Representation.SL5ExteriorSquare.flagGroup

namespace ExteriorMarking
variable (a : ExteriorMarking D)

/-- Pull back a genuine exterior subspace into the unchanged ambient V. -/
def subspace (W : Submodule (ZMod 2) Representation.SL5ExteriorSquare.V) : Subgroup G :=
  ((W.toAddSubgroup.toSubgroup').comap a.coordinates.toMonoidHom).map V.subtype

omit [Finite G] in
theorem subspace_le (W : Submodule (ZMod 2) Representation.SL5ExteriorSquare.V) :
    a.subspace W ≤ V := map_subtype_le _

omit [Finite G] in
theorem subspace_mono : Monotone a.subspace := by
  intro W W' h
  apply map_mono
  apply comap_mono
  exact h

omit [Finite G] in
theorem mem_subspace (W : Submodule (ZMod 2) Representation.SL5ExteriorSquare.V)
    (v : V) : (v : G) ∈ a.subspace W ↔ (a.coordinates v).toAdd ∈ W := by
  constructor
  · rintro ⟨w, hw, he⟩
    have hwv : w = v := Subtype.ext he
    change (a.coordinates w).toAdd ∈ W at hw
    simpa only [hwv] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- The source index i refers to exterior dimension, not natural flag dimension. -/
def Vi (i : ℕ) : Subgroup G := a.subspace (match i with
  | 1 => Representation.SL5ExteriorSquare.V₁
  | 3 => Representation.SL5ExteriorSquare.V₃
  | 4 => Representation.SL5ExteriorSquare.V₄
  | 6 => Representation.SL5ExteriorSquare.V₆
  | 7 => Representation.SL5ExteriorSquare.V₇
  | _ => ⊥)

def VthreePrime : Subgroup G := a.subspace Representation.SL5ExteriorSquare.V₃'

/-- The decomposable involution whose cyclic subgroup is V₁. -/
def z : G := (a.coordinates.symm
  (Multiplicative.ofAdd Representation.SL5ExteriorSquare.decomposable) : V)

/-- The nondecomposable representative in 12.5.5(2). -/
def zPrime : G := (a.coordinates.symm
  (Multiplicative.ofAdd Representation.SL5ExteriorSquare.nondecomposable) : V)

def Gi (i : ℕ) : Subgroup G := normalizer (a.Vi i : Set G)
def Mi (i : ℕ) : Subgroup G := (L ⊔ (T : Subgroup G)) ⊓ a.Gi i

/-- The solvable residual of N_L(Vᵢ), included in G. -/
def Li (i : ℕ) : Subgroup G :=
  (solvableResidual (L ⊓ a.Gi i : Subgroup G)).map (L ⊓ a.Gi i).subtype

/-- O₂(LᵢT), included in G; this is not O₂(Lᵢ). -/
def Ri (i : ℕ) : Subgroup G := (a.Li i ⊔ (T : Subgroup G)).pCoreIn 2

/-- The maximal local group M from Notation 12.2.5. -/
def M (_a : ExteriorMarking D) : Subgroup G := normalizer (L : Set G)

/-- The literal point span from 12.5.8. -/
def U : Subgroup G := conjugateSpanBy V (a.Gi 1)

/-- The literal H-span used in the final argument on p.822. -/
def UH (H : Subgroup G) : Subgroup G := conjugateSpanBy (a.Vi 7) H

omit [Finite G] in
theorem UH_le_U {H : Subgroup G} (hH : H ≤ a.Gi 1) : a.UH H ≤ a.U :=
  conjugateSpanBy_mono (a.subspace_le _) hH

end ExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
