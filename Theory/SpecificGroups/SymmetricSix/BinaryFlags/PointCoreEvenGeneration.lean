module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreGeneration
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
/-!
# Generating S₆ with a conjugate point core and a prescribed involution

The even involution (04)(12) conjugates the point transposition (45) to
(05). These crossing transpositions and the full point core generate S₆.
Involution fusion in A₆ transports that calculation to every even involution.
A transposition has the same generation property. Both transports preserve
any specified conjugate marking of the point core and choose the new
conjugator in A₆.

Source application: Meierfrankenfeld--Stellmacher (1993), (5.5)(a),
printed p.915, for the actual symplectic critical-image actors.
-/

public section
open Subgroup BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing Representation.BinaryOffender

namespace PointCoreEvenGeneration

private def actor : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 4 * Equiv.swap 1 2, by decide⟩
private theorem actor_order : orderOf actor = 2 :=
  orderOf_eq_prime (by decide) (by decide)
private theorem actor_generates : pointCore ⊔ zpowers (actor : S) = ⊤ := by
  let N := pointCore ⊔ zpowers (actor : S)
  have ht : swap45 ∈ pointCore := by
    rw [pointCore_eq_closure]
    exact subset_closure (by simp)
  have hcore : (subspaceStabilizer (naturalRepresentation Ω) canonicalLine).pCoreIn 2 = pointCore := by
    have hh : subspaceStabilizer (naturalRepresentation Ω) canonicalLine = H1 := by
      ext x
      exact (mem_stabilizer_iff_map _ _).trans (canonicalLine_stabilizer x)
    rw [hh,H1_core_eq_pointCore]
  have hall := PointCoreGeneration.point_core_generate canonicalLine canonicalLine_finrank
    swap45 (Equiv.swap 0 5) (by exact ⟨4,5,by decide,rfl⟩)
    (by exact ⟨0,5,by decide,rfl⟩) (hcore ▸ ht) (by change swap45 * Equiv.swap 0 5 ≠ Equiv.swap 0 5 * swap45; decide +kernel)
  rw [hcore] at hall
  have hh : actor.val * swap45 * actor.val⁻¹ = Equiv.swap 0 5 := by decide +kernel
  have hs : Equiv.swap (0:Fin 6) 5 ∈ N := hh ▸ N.mul_mem
    (N.mul_mem (mem_sup_right (mem_zpowers actor.val)) (mem_sup_left ht))
    (N.inv_mem (mem_sup_right (mem_zpowers actor.val)))
  apply top_unique
  rw [←hall]
  exact sup_le le_sup_left (zpowers_le.mpr hs)


theorem exists_conjugate_pointCore_generates (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) :
    ∃ g : alternatingGroup (Fin 6),
      pointCore.map (MulAut.conj g.val).toMonoidHom ⊔ zpowers a.val = ⊤ := by
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj actor a actor_order ha)
  refine ⟨g,?_⟩
  have he : (MulAut.conj g.val).toMonoidHom actor.val = a.val := congrArg Subtype.val hg
  have hh := congrArg (Subgroup.map (MulAut.conj g.val).toMonoidHom) actor_generates
  simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,he,
    map_top_of_surjective (MulAut.conj g.val).toMonoidHom (MulAut.conj g.val).surjective] using hh

theorem exists_even_conjugate_pointCore_generates (u : S) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) :
    ∃ g : alternatingGroup (Fin 6),
      (pointCore.map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj g.val).toMonoidHom ⊔ zpowers a.val = ⊤ := by
  let c : MulAut (alternatingGroup (Fin 6)) := MulAut.conjNormal u⁻¹
  let b : alternatingGroup (Fin 6) := c a
  have hb : orderOf b = 2 := (c.orderOf_eq a).trans ha
  obtain ⟨k,hk⟩ := exists_conjugate_pointCore_generates b hb
  let g : alternatingGroup (Fin 6) := MulAut.conjNormal u k
  refine ⟨g,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) hk
  have hback : (MulAut.conj u).toMonoidHom b.val = a.val := by change u*(u⁻¹*a.val*u)*u⁻¹=a.val; group
  have hcomp : ((MulAut.conj g.val).toMonoidHom.comp (MulAut.conj u).toMonoidHom) =
      ((MulAut.conj u).toMonoidHom.comp (MulAut.conj k.val).toMonoidHom) := by
    apply MonoidHom.ext
    intro x
    change (u*k.val*u⁻¹)*(u*x*u⁻¹)*(u*k.val*u⁻¹)⁻¹ = u*(k.val*x*k.val⁻¹)*u⁻¹
    group
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,hback,
    map_top_of_surjective (MulAut.conj u).toMonoidHom (MulAut.conj u).surjective,map_map] at hh
  rw [map_map,hcomp]
  exact hh


private theorem swap_generates : pointCore ⊔ zpowers (Equiv.swap (0:Fin 6) 5) = ⊤ := by
  have ht : swap45 ∈ pointCore := by
    rw [pointCore_eq_closure]
    exact subset_closure (by simp)
  have hcore : (subspaceStabilizer (naturalRepresentation Ω) canonicalLine).pCoreIn 2 = pointCore := by
    have hh : subspaceStabilizer (naturalRepresentation Ω) canonicalLine = H1 := by
      ext x
      exact (mem_stabilizer_iff_map _ _).trans (canonicalLine_stabilizer x)
    rw [hh,H1_core_eq_pointCore]
  have hall := PointCoreGeneration.point_core_generate canonicalLine canonicalLine_finrank
    swap45 (Equiv.swap 0 5) (by exact ⟨4,5,by decide,rfl⟩)
    (by exact ⟨0,5,by decide,rfl⟩) (hcore ▸ ht)
    (by change swap45 * Equiv.swap 0 5 ≠ Equiv.swap 0 5 * swap45; decide +kernel)
  rwa [hcore] at hall

private theorem exists_even_swap_conjugator (a : S) (ha : a.IsSwap) :
    ∃ g : alternatingGroup (Fin 6), g.val * Equiv.swap 0 5 * g.val⁻¹ = a := by
  have hc : IsConj (Equiv.swap (0:Fin 6) 5) a :=
    Equiv.Perm.isConj_of_cycleType_eq ((by decide +kernel :
      (Equiv.swap (0:Fin 6) 5).cycleType = {2}).trans
        (Equiv.Perm.isSwap_iff_cycleType.mp ha).symm)
  obtain ⟨c,hc⟩ := isConj_iff.mp hc
  rcases Int.units_eq_one_or (Equiv.Perm.sign c) with he | he
  · exact ⟨⟨c,he⟩,hc⟩
  · have hk : c * Equiv.swap (0:Fin 6) 5 ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup,map_mul,he]
      decide +kernel
    refine ⟨⟨c * Equiv.swap 0 5,hk⟩,?_⟩
    change (c * Equiv.swap 0 5) * Equiv.swap 0 5 * (c * Equiv.swap 0 5)⁻¹ = a
    rw [←hc]
    group

theorem exists_conjugate_pointCore_generates_swap (a : S) (ha : a.IsSwap) :
    ∃ g : alternatingGroup (Fin 6),
      pointCore.map (MulAut.conj g.val).toMonoidHom ⊔ zpowers a = ⊤ := by
  obtain ⟨g,hg⟩ := exists_even_swap_conjugator a ha
  refine ⟨g,?_⟩
  have he : (MulAut.conj g.val).toMonoidHom (Equiv.swap 0 5) = a := hg
  have hh := congrArg (Subgroup.map (MulAut.conj g.val).toMonoidHom) swap_generates
  simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,he,
    map_top_of_surjective (MulAut.conj g.val).toMonoidHom (MulAut.conj g.val).surjective] using hh

theorem exists_even_conjugate_pointCore_generates_swap (u a : S) (ha : a.IsSwap) :
    ∃ g : alternatingGroup (Fin 6),
      (pointCore.map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj g.val).toMonoidHom ⊔ zpowers a = ⊤ := by
  let b := u⁻¹*a*u
  have hb : b.IsSwap := by
    obtain ⟨i,j,hij,rfl⟩ := ha
    change (u⁻¹*Equiv.swap i j*(u⁻¹)⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨_,_,u.symm.injective.ne hij,rfl⟩
  obtain ⟨k,hk⟩ := exists_conjugate_pointCore_generates_swap b hb
  let g : alternatingGroup (Fin 6) := MulAut.conjNormal u k
  refine ⟨g,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) hk
  have hback : (MulAut.conj u).toMonoidHom b = a := by change u*(u⁻¹*a*u)*u⁻¹=a; group
  have hcomp : ((MulAut.conj g.val).toMonoidHom.comp (MulAut.conj u).toMonoidHom) =
      ((MulAut.conj u).toMonoidHom.comp (MulAut.conj k.val).toMonoidHom) := by
    apply MonoidHom.ext
    intro x
    change (u*k.val*u⁻¹)*(u*x*u⁻¹)*(u*k.val*u⁻¹)⁻¹ = u*(k.val*x*k.val⁻¹)*u⁻¹
    group
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,hback,
    map_top_of_surjective (MulAut.conj u).toMonoidHom (MulAut.conj u).surjective,map_map] at hh
  rw [map_map,hcomp]
  exact hh

end PointCoreEvenGeneration
