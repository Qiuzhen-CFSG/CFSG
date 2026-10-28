module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.Classes

/-!
# The sixteen marked B parameters and their Sylow orbits

B is the product of the two displayed four-planes. Its sixteen parameters
make the five class intersections explicit. Eight rotation/swap actors
suffice to certify each orbit. For the two four-point diagonal classes,
a 128-element Sylow-coordinate certificate identifies the pointwise
centralizer with B. No conjugacy search in the full wreath product occurs.

Source: Aschbacher–Smith 13.9.4–5, printed p.970.
-/

@[expose] public section
namespace SymmetricFourWreath.InvolutionClasses
open Subgroup
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq

abbrev Parameters := (plane false) × (plane false)

def parametersToP : Parameters →* P := pair.comp
  ((plane false).subtype.prodMap (plane false).subtype)

def parametersToW : Parameters →* W := sylowEmbedding.comp parametersToP

theorem parametersToP_injective : Function.Injective parametersToP := by
  intro a b h
  have he := pair_injective h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))

theorem parametersToW_injective : Function.Injective parametersToW :=
  sylowEmbedding_injective.comp parametersToP_injective

theorem parametersToW_range : parametersToW.range=B := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨parametersToP a,⟨((a.1:D8),(a.2:D8)),⟨a.1.property,a.2.property⟩,rfl⟩,rfl⟩
  · rintro ⟨_,⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩,rfl⟩
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl⟩

noncomputable def parametersEquivB : Parameters ≃* B :=
  (MonoidHom.ofInjective parametersToW_injective).trans
    (MulEquiv.subgroupCongr parametersToW_range)

def dihedralKind (a : D8) : Fin 3 := if a=1 then 0 else if a=DihedralGroup.r 2 then 2 else 1

theorem kind_square_plane : ∀a:plane false,kind (square a)=dihedralKind a := by decide +kernel

def parameterIndex (a : Parameters) : Fin 6 := pairIndex (dihedralKind a.1) (dihedralKind a.2)

theorem parametersToW_index (a : Parameters) : classIndex (parametersToW a)=parameterIndex a := by
  change pairIndex (kind (square a.1)) (kind (square a.2))=parameterIndex a
  rw [kind_square_plane,kind_square_plane]
  rfl

def orbitSize (i : Fin 6) : Nat := if i=0 then 1 else if i=1 then 2 else if i=5 then 0 else 4

theorem parameter_class_card : ∀i:Fin 6,
    Fintype.card {a:Parameters // a≠1 ∧ parameterIndex a=i}=orbitSize i := by decide +kernel

def orbitActor (s : Bool×Bool×Bool) : P :=
  pair (if s.1 then DihedralGroup.r 1 else 1,if s.2.1 then DihedralGroup.r 1 else 1) *
    (if s.2.2 then RegularWreathProduct.inl turn else 1)

theorem parameter_orbit : ∀a b:Parameters,a≠1 → b≠1 → parameterIndex a=parameterIndex b →
    ∃s:Bool×Bool×Bool,orbitActor s*parametersToP a*(orbitActor s)⁻¹=parametersToP b := by
  decide +kernel

theorem parameter_class_centralizer : ∀i:Fin 6,i=3 ∨ i=4 → ∀x:P,
    (∀a:Parameters,a≠1 → parameterIndex a=i →
      x*parametersToP a=parametersToP a*x) ↔
      x.right=1 ∧ x.left 1∈plane false ∧ x.left turn∈plane false := by
  decide +kernel

end SymmetricFourWreath.InvolutionClasses
