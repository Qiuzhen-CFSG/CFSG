module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
/-!
# Orienting an index-three subgroup of S₄ × S₄

An index-three subgroup containing the two Klein-four cores descends to an
index-three subgroup of S₃ × S₃. The two parabolics in that quotient are
conjugate, up to exchanging coordinates, to the stabilizer of a point in
the first factor. Lifting the conjugating element identifies the original
subgroup with the centralizer of a fixed double transposition in that factor.

This supplies the local-intersection coordinate choice in Aschbacher--Smith
F.5.7, before the independent compatibility of the marked maps is addressed.
-/
open Subgroup
namespace SymmetricFourProduct
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
local notation "S4" => Equiv.Perm (Fin 4)
local notation "S3" => Equiv.Perm (Fin 3)
private def q : S4×S4 →* S3×S3 := quotientHom.prodMap quotientHom
private theorem qsurj : Function.Surjective q := by
  rintro ⟨x,y⟩
  obtain ⟨a,rfl⟩ := quotientHom_surjective x
  obtain ⟨b,rfl⟩ := quotientHom_surjective y
  exact ⟨(a,b),rfl⟩
private theorem qker : q.ker=core.prod core := by
  ext x
  change (quotientHom x.1,quotientHom x.2)=(1,1) ↔ _
  simp only [Prod.mk.injEq, mem_prod]
  rfl
private theorem first_fixed (x:S4) : quotientHom x 0=0 ↔ x∈centralizer ({doubleSwap 0}:Set S4) := by
  rw [mem_centralizer_singleton_iff]
  exact (show ∀ x:S4,quotientHom x 0=0 ↔ x*doubleSwap 0=doubleSwap 0*x by decide +kernel) x

public theorem index_three_marking (K:Subgroup (S4×S4))
    (hK:K.index=3) (hcore:core.prod core≤K) :
    ∃ e : MulAut (S4×S4), ∀ x, x∈K ↔ (e x).1∈centralizer ({doubleSwap 0}:Set S4) := by
  let P := K.map q
  have hker : q.ker≤K := qker ▸ hcore
  have hP : P.index=3 := (K.index_map_eq qsurj hker).trans hK
  have hPc : Nat.card P=12 := by
    have hh := P.card_mul_index
    rw [hP,SymmetricThreeProduct.card_group] at hh
    omega
  let S : Sylow 2 P := default
  have hS : Nat.card S=4 := by
    rw [S.card_eq_multiplicity,hPc]
    decide +kernel
  let T := (S:Subgroup P).map P.subtype
  have hTc : Nat.card T=4 := (card_map_of_injective P.subtype_injective).trans hS
  have hTi : T.index=9 := by
    have hh := T.card_mul_index
    rw [hTc,SymmetricThreeProduct.card_group] at hh
    omega
  let TS : Sylow 2 (S3×S3) := (S.isPGroup'.map P.subtype).toSylow (by rw [hTi];decide)
  obtain ⟨g,_,hp⟩ := SymmetricThreeProduct.coatom_over_sylow TS
  have hcases := (hp P).mp ⟨isCoatom_of_index_three P hP,map_subtype_le _⟩
  obtain ⟨a,ha⟩ := qsurj g
  let e := MulAut.conj a⁻¹
  have heval (x:S4×S4) : q (e x)=(MulAut.conj g).symm (q x) := by
    change q (a⁻¹*x*(a⁻¹)⁻¹)=g⁻¹*q x*(g⁻¹)⁻¹
    simp only [map_mul,map_inv,ha]
  have hpre (x:S4×S4) : x∈K ↔ q x∈P := by
    have hh := K.comap_map_eq_self hker
    exact Iff.of_eq (congrArg (fun L:Subgroup (S4×S4)=>x∈L) hh.symm)
  rcases hcases with hp | hp
  · refine ⟨e,fun x=>?_⟩
    rw [hpre,hp]
    change q x∈SymmetricThreeProduct.leftParabolic.map (MulAut.conj g).toMonoidHom ↔ _
    have hm := (mem_map_equiv (f := MulAut.conj g)
      (K := SymmetricThreeProduct.leftParabolic) (x := q x))
    rw [hm]
    rw [←heval,SymmetricThreeProduct.mem_leftParabolic]
    exact first_fixed _
  · refine ⟨e.trans (MulEquiv.prodComm : S4×S4≃*S4×S4),fun x=>?_⟩
    rw [hpre,hp]
    change q x∈SymmetricThreeProduct.rightParabolic.map (MulAut.conj g).toMonoidHom ↔ _
    have hm := (mem_map_equiv (f := MulAut.conj g)
      (K := SymmetricThreeProduct.rightParabolic) (x := q x))
    rw [hm]
    rw [←heval,SymmetricThreeProduct.mem_rightParabolic]
    exact first_fixed _
end SymmetricFourProduct
