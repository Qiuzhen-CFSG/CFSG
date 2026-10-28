module
public import Theory.SpecificGroups.AlternatingSix.CubicNormalizerQuotient
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A cubic normalizer above an elementary sixteen

A surjection onto A6 with kernel of order sixteen lifts the normalizer of a
three-group. Its kernel is the fixed subgroup of the sixteen, because the
map is injective on the three-group. A fixed four therefore gives order 72.
This is the local lifting step in Aschbacher (1994), 45.7(3).
-/

public section
open Subgroup
namespace ElementarySixteenCubic
variable {G:Type*} [Group G] [Finite G]
variable (f:G→*alternatingGroup (Fin 6)) (hf:Function.Surjective f)
variable (hR:Nat.card f.ker=16) (U:Subgroup G) (hU:Nat.card U=3)

include hR hU in
theorem kernel_inf_normalizer : f.ker ⊓ normalizer (U:Set G) =
    f.ker ⊓ centralizer (U:Set G) := by
  have hp:IsPGroup 3 U:=IsPGroup.of_card (n:=1) (by simpa using hU)
  have hi:=injective_comp_subtype_of_coprime_ker f
    (show Nat.Coprime 3 (Nat.card f.ker) by rw [hR]; decide) U hp
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le_normalizer _))
  rintro x ⟨hxR,hxN⟩
  refine ⟨hxR,mem_centralizer_iff.mpr ?_⟩
  intro u hu
  have hxu: x*u*x⁻¹∈U := (mem_normalizer_iff.mp hxN u).mp hu
  have he:(⟨x*u*x⁻¹,hxu⟩:U)=⟨u,hu⟩:=hi (by
    change f (x*u*x⁻¹)=f u
    simp only [map_mul,map_inv,MonoidHom.mem_ker.mp hxR,one_mul,mul_one,inv_one])
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm

include hf hR hU in
/-- The actual normalizer maps onto the A6 cubic normalizer, with its fixed-four kernel. -/
theorem normalizer_lift
    (hS:Nat.card (f.ker ⊓ centralizer (U:Set G):Subgroup G)=4) :
    Nat.card (normalizer (U:Set G))=72 ∧
    ∃π:normalizer (U:Set G)→*normalizer (U.map f:Set (alternatingGroup (Fin 6))),
      Function.Surjective π ∧
      (∀x, (π x:alternatingGroup (Fin 6))=f x) ∧
      π.ker=(f.ker ⊓ centralizer (U:Set G)).subgroupOf (normalizer (U:Set G)) := by
  let N:=normalizer (U:Set G)
  let D:=U.map f
  have hp:IsPGroup 3 U:=IsPGroup.of_card (n:=1) (by simpa using hU)
  let : Fact (IsPGroup 3 U):=⟨hp⟩
  have hcop:Nat.Coprime 3 (Nat.card f.ker):=by rw [hR]; decide
  have hi:=injective_comp_subtype_of_coprime_ker f hcop U hp
  have hD:Nat.card D=3:=by
    rw [show D=(f.comp U.subtype).range by rw [MonoidHom.range_comp,range_subtype],
      ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,hU]
  have hmap:normalizer (D:Set (alternatingGroup (Fin 6)))=N.map f:=
    normalizer_map_eq_of_coprime_kernel 3 U f hf hcop
  let π:N→*normalizer (D:Set (alternatingGroup (Fin 6))):=
    (f.comp N.subtype).codRestrict _ (fun x=>hmap ▸ mem_map_of_mem f x.property)
  have hπ:Function.Surjective π:=by
    intro y
    have hy : (y:alternatingGroup (Fin 6))∈N.map f:=hmap ▸ y.property
    obtain ⟨x,hx,he⟩:=hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hker:π.ker=(f.ker ⊓ centralizer (U:Set G)).subgroupOf N:=by
    ext x
    change π x=1 ↔ (x:G)∈f.ker ∧ (x:G)∈centralizer (U:Set G)
    rw [Subtype.ext_iff]
    change f (x:G)=1 ↔ _
    constructor
    · intro hx
      exact (kernel_inf_normalizer f hR U hU).le ⟨hx,x.property⟩
    · exact fun h=>h.1
  have hkerC:Nat.card π.ker=4:=by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe
      (inf_le_right.trans (centralizer_le_normalizer (U:Set G)))).toEquiv]
    exact hS
  have hN:Nat.card N=72:=by
    have hh:=π.ker.card_mul_index
    rw [hkerC,index_ker,π.range_eq_top_of_surjective hπ,card_top,
      (AlternatingSix.CubicNormalizer.normalizer_data D hD).1] at hh
    exact hh.symm
  exact ⟨hN,π,hπ,fun _=>rfl,hker⟩
end ElementarySixteenCubic
