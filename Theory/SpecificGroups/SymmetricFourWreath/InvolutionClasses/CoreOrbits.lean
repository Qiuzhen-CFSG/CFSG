module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Placement
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.Classes

/-!
# The four Sylow orbits on the noncentral involutions of Q

The literal order-128 dihedral wreath coordinates identify the four class
intersections of sizes 4, 2, 4 and 8. Thirty-two simple coordinate actors
certify transitivity without a conjugacy search in the order-1152 group.
Three generators describe the span and centralizer of the first orbit.

Source: Aschbacher–Smith 13.9.9, printed p.972.
-/

@[expose] public section
namespace SymmetricFourWreath.InvolutionClasses
open Subgroup
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq

def coreTest (x:P) : Prop := x.left 1*(x.left turn)⁻¹=1 ∨
  x.left 1*(x.left turn)⁻¹=DihedralGroup.r 2
instance (x:P) : Decidable (coreTest x) := inferInstanceAs (Decidable (x.left 1*(x.left turn)⁻¹=1 ∨ x.left 1*(x.left turn)⁻¹=DihedralGroup.r 2))

def gamma (i:Fin 6) : Set P := {x | coreTest x ∧ x*x=1 ∧ x≠1 ∧
  x≠centralInP ∧ classIndex (sylowEmbedding x)=i}
private def gammaDecidable (i:Fin 6) (x:P) : Decidable (coreTest x ∧ x*x=1 ∧ x≠1 ∧ x≠centralInP ∧ classIndex (sylowEmbedding x)=i) := by infer_instance
private instance (i:Fin 6) : DecidablePred (·∈gamma i) := gammaDecidable i

theorem mem_gamma (i:Fin 6) (x:P) : x∈gamma i ↔
    x∈coreInP ∧ orderOf x=2 ∧ x≠centralInP ∧ classIndex (sylowEmbedding x)=i := by
  rw [mem_coreInP]
  change (coreTest x ∧ x*x=1 ∧ x≠1 ∧ _) ↔ _
  constructor
  · rintro ⟨h,hxx,hne,hz,hi⟩
    exact ⟨h,orderOf_eq_prime (by simpa only [pow_two] using hxx) hne,hz,hi⟩
  · rintro ⟨h,ho,hz,hi⟩
    exact ⟨h,by simpa only [pow_two,ho] using pow_orderOf_eq_one x,
      by intro he;simp [he] at ho,hz,hi⟩

def gammaSize (i:Fin 6) : Nat := if i=0 then 4 else if i=1 then 2 else if i=3 then 4 else if i=5 then 8 else 0

theorem gamma_card (i:Fin 6) : Nat.card (gamma i)=gammaSize i := by
  rw [Nat.card_eq_fintype_card]
  revert i
  decide +kernel

theorem gamma_indices : ∀i:Fin 6,∀x:P,x∈gamma i → i=0 ∨ i=1 ∨ i=3 ∨ i=5 := by decide +kernel

def gammaRep (i:Fin 6) : P := if i=0 then pair (DihedralGroup.sr 1,DihedralGroup.sr 1)
  else if i=1 then pair (DihedralGroup.r 2,1)
  else if i=3 then pair (DihedralGroup.sr 0,DihedralGroup.sr 0)
  else RegularWreathProduct.inl turn

def gammaActor (s:D8×Bool×Bool) : P :=
  pair (s.1,if s.2.1 then DihedralGroup.r 1 else 1) *
    (if s.2.2 then RegularWreathProduct.inl turn else 1)

theorem gamma_representative_mem : ∀i:Fin 6,i=0 ∨ i=1 ∨ i=3 ∨ i=5 → gammaRep i∈gamma i := by
  decide +kernel

theorem gamma_representative_orbit : ∀i:Fin 6,∀x:P,x∈gamma i →
    ∃s:D8×Bool×Bool,gammaActor s*gammaRep i*(gammaActor s)⁻¹=x := by decide +kernel


def gammaZeroGenerator (i:Fin 3) : P := pair
  (if i=2 then DihedralGroup.sr 3 else DihedralGroup.sr 1,
   if i=1 then DihedralGroup.sr 3 else DihedralGroup.sr 1)

theorem gammaZeroGenerator_mem : ∀i:Fin 3,gammaZeroGenerator i∈gamma 0 := by decide +kernel

def gammaZeroWord (e:Fin 3→Fin 2) : P :=
  gammaZeroGenerator 0^(e 0).val * gammaZeroGenerator 1^(e 1).val * gammaZeroGenerator 2^(e 2).val

theorem gamma_zero_span_certificate : ∀x:P,coreTest x →
    x.right=1 → x.left 1∈plane true → x.left turn∈plane true →
    ∃e:Fin 3→Fin 2,gammaZeroWord e=x := by decide +kernel

theorem gamma_zero_centralizer_certificate : ∀x:P,x.right=1 →
    ((∀i:Fin 3,x*gammaZeroGenerator i=gammaZeroGenerator i*x) ↔
      x.left 1∈plane true ∧ x.left turn∈plane true) := by decide +kernel

end SymmetricFourWreath.InvolutionClasses
