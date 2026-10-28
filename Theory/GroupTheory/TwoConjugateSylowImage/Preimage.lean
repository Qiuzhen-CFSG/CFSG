module
public import Theory.GroupTheory.TwoConjugateSylowImage
/-!
# Internal conjugators in a prescribed quotient preimage

Restrict the original homomorphism to the preimage of the desired subgroup,
then apply minimal-pair rechoice there. Mapping back retains the prescribed
quotient image and makes the conjugator internal in the original carrier.
Source: the lifting step in Aschbacher–Smith E.2.9.
-/
public section
open scoped Pointwise
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]

omit [Finite G] in
private theorem map_pair (f : G →* D) (V : Subgroup G) (g : G) :
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f =
      V.map f ⊔ (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup,map_map,map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

theorem exists_internal_conjugator_in_preimage {p : ℕ} [Fact p.Prime]
    (f : G →* D) (V : Subgroup G) (hV : IsPGroup p V)
    (I : Subgroup D) (P : Sylow p I)
    (hP : (P : Subgroup I).map I.subtype = V.map f)
    (hex : ∃g:G, f g ∈ I ∧ (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f = I) :
    ∃g:G,g ∈ V ⊔ V.map (MulAut.conj g).toMonoidHom ∧
      (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f = I := by
  let L := I.comap f
  let U := V.subgroupOf L
  let r : L →* I := (f.comp L.subtype).codRestrict I (fun x => x.property)
  have hVL : V ≤ L := by
    apply map_le_iff_le_comap.mp
    rw [← hP]
    exact map_subtype_le _
  have hUr : U.map r = (P : Subgroup I) := by
    apply map_injective I.subtype_injective
    rw [map_map,hP]
    change U.map (f.comp L.subtype) = V.map f
    rw [← map_map,map_subgroupOf_eq_of_le hVL]
  obtain ⟨g,hg,hgim⟩ := hex
  let g0 : L := ⟨g,hg⟩
  have hex' : ∃g:L,(U ⊔ U.map (MulAut.conj g).toMonoidHom).map r = ⊤ := by
    refine ⟨g0,?_⟩
    apply map_injective I.subtype_injective
    rw [← MonoidHom.range_eq_map,range_subtype]
    rw [map_pair,map_sup]
    have hU : (U.map r).map I.subtype = V.map f := by rw [hUr,hP]
    rw [hU]
    have hc : ((U.map r).map (MulAut.conj (r g0)).toMonoidHom).map I.subtype =
        (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
      rw [← hU]
      simp only [map_map]
      congr 1
    rw [hc,← map_pair]
    exact hgim
  obtain ⟨x,hx,him⟩ := exists_internal_conjugator_of_sylow_image r U hV.comap_subtype P hUr hex'
  have he : (U ⊔ U.map (MulAut.conj x).toMonoidHom).map L.subtype =
      V ⊔ V.map (MulAut.conj (x:G)).toMonoidHom := by
    rw [map_pair,map_subgroupOf_eq_of_le hVL]
    rfl
  refine ⟨x,?_,?_⟩
  · rw [← he]
    exact mem_map_of_mem L.subtype hx
  · rw [← he,map_map]
    have hh := congrArg (fun A:Subgroup I => A.map I.subtype) him
    rw [map_map,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
end Subgroup
