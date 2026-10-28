module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CommutatorRows
public import Theory.ElementaryAbelian.Injective
/-! # Marked symplectic Sylow commutator rows
The actual Sylow conjugacy equivalence transports the two root-wing
calculation without any assumed coordinate or placement data.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {E F:Type*} [Group E] [Finite E] [Field F] [Finite F] [CharP F 2]
theorem sylow_commutator_rows (e:E≃*Sp F) {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n) (S:Sylow 2 E) :
    _root_.commutator S≤center S ∧ ∀a:S,a^2=1→a∉center S→
      Nat.card (⁅zpowers a,⊤⁆:Subgroup S)=Nat.card F := by
  let P:=S.mapSurjective (f:=e.toMonoidHom) e.surjective
  let eS:S≃*unipotent (F:=F):=((S:Subgroup E).equivMapOfInjective e.toMonoidHom e.injective).trans
    (Sylow.equiv P (unipotentSylow hF hn))
  let f:=eS.toMonoidHom
  have hpre (i:Bool):IsElementaryAbelian 2 ((wing (F:=F) i).comap f):=by
    let :=wing_elementary (F:=F) i
    exact IsElementaryAbelian.comap_of_injective f eS.injective _
  let :=hpre false
  let :=hpre true
  refine ⟨Subgroup.TwoPlaneCover.class_two f eS.surjective (wing false) (wing true)
    wings_generate center_le_wings class_two,?_⟩
  intro a ha hz
  exact (cover_involution_commutator f eS.surjective a ha hz).2.2.1
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
