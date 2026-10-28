module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Orbit
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.EvenFlag
/-!
# Isotropic planes in the actual binary six-letter module

Distinct orthogonal nonzero vectors correspond to disjoint duads. Extend
that four-letter injection to a permutation; it sends the canonical
isotropic plane to the specified plane. Multiplication by a canonical
plane-fixing transposition makes the marking even, so A₆ already acts
transitively on the isotropic planes of the literal natural module.

The only finite certificate checks the 225 pairs of duads. The basis,
permutation extension and subspace transports are structural.
Source: Aschbacher--Smith 13.5.6(2), printed p.917.
-/

@[expose] public section
open Subgroup BinaryPermutation Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.IsotropicPlanes
open NaturalGeometry NaturalPairing NondegeneratePlane
private theorem disjoint_indices (d e:NaturalGeometry.Duad)(hne:d≠e)
    (h:(∑a,rawPair d.val.1 d.val.2 a*rawPair e.val.1 e.val.2 a)=0) :
    d.val.1≠e.val.1∧d.val.1≠e.val.2∧d.val.2≠e.val.1∧d.val.2≠e.val.2 := by decide +revert

theorem orthogonal_pair_mover (x y:V)(hx:x≠0)(hy:y≠0)(hxy:x≠y)(h:form x y=0) :
    ∃g:S,naturalRepresentation Ω g (pairVector 0 1)=x ∧
      naturalRepresentation Ω g (pairVector 2 3)=y := by
  obtain ⟨d,rfl⟩:=(vector_cases x).resolve_left hx
  obtain ⟨e,rfl⟩:=(vector_cases y).resolve_left hy
  have hde:d≠e:=by intro he;subst e;exact hxy rfl
  rw [duadVector,duadVector,pair_form] at h
  obtain ⟨h00,h01,h10,h11⟩:=disjoint_indices d e hde h
  let f:Fin 4→Ω:=![d.val.1,d.val.2,e.val.1,e.val.2]
  have hf:Function.Injective f:=by
    have hd:=ne_of_lt d.property
    have he:=ne_of_lt e.property
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  obtain ⟨g,hg⟩:=Perm.exists_extending_pair (fun j:Fin 4=>(j.castLE (by decide):Fin 6)) f
    (by intro a b he;exact Fin.ext (congrArg (fun x:Fin 6=>x.val) he)) hf
  refine ⟨g,?_,?_⟩
  · rw [pairVector_map]
    have h0:g 0=d.val.1:=hg 0
    have h1:g 1=d.val.2:=hg 1
    rw [h0,h1];rfl
  · rw [pairVector_map]
    have h2:g 2=e.val.1:=hg 2
    have h3:g 3=e.val.2:=hg 3
    rw [h2,h3];rfl

theorem exists_even_plane_marking (W:Submodule (ZMod 2) V)
    (hd:Module.finrank (ZMod 2) W=2)(hi:∀x∈W,∀y∈W,form x y=0) :
    ∃a:alternatingGroup Ω,W=move a.val canonicalPlane := by
  let b:=Module.finBasisOfFinrankEq (ZMod 2) W hd
  have hx:(b 0:V)≠0:=by intro h;exact b.ne_zero 0 (Subtype.ext h)
  have hy:(b 1:V)≠0:=by intro h;exact b.ne_zero 1 (Subtype.ext h)
  have hxy:(b 0:V)≠b 1:=by intro h;exact (by decide:(0:Fin 2)≠1) (b.injective (Subtype.ext h))
  obtain ⟨g,hg0,hg1⟩:=orthogonal_pair_mover (b 0) (b 1) hx hy hxy
    (hi _ (b 0).property _ (b 1).property)
  have hW:W=move g canonicalPlane := by
    apply (Submodule.eq_of_le_of_finrank_eq ?_
      ((move_finrank g canonicalPlane).trans (canonicalPlane_finrank.trans hd.symm))).symm
    rw [move,canonicalPlane,Submodule.map_span,Set.image_insert_eq,Set.image_singleton,hg0,hg1]
    exact Submodule.span_le.mpr (by rintro x (rfl|rfl);exact (b 0).property;exact (b 1).property)
  obtain ⟨a,_,ha⟩:=exists_even_same_flag g
  exact ⟨a,hW.trans ha⟩
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.IsotropicPlanes
