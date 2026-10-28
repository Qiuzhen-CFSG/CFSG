module
public import Theory.GroupTheory.PGroup.ExtraspecialCentralizer
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# A faithful seed for a class-two action

An extraspecial subgroup P whose ambient commutators lie in Z(P) has its
centralizer as a supplement. The ambient-subgroup form retains its inclusion
in U and is convenient for source actions: actors centralizing the complement
modulo Z(P) have the same kernel on P/Z(P) and on U/Z(P).
Source: Aschbacher–Smith F.9.5(5–6), printed p.319.
-/
public section
namespace Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- The extraspecial centralizer supplement in the original ambient group. -/
theorem extraspecial_sup_centralizer_eq (P U Z : Subgroup G)
    [Finite P] [IsExtraspecial 2 P] (hPU : P ≤ U)
    (hz : (center P).map P.subtype = Z) (hcomm : ⁅U,P⁆ ≤ Z) :
    P ⊔ (U ⊓ centralizer (P : Set G)) = U := by
  let E := P.subgroupOf U
  let e : E ≃* P := subgroupOfEquivOfLe hPU
  let : Finite E := Finite.of_equiv P e.toEquiv.symm
  let : IsExtraspecial 2 E := IsExtraspecial.of_mulEquiv e.symm inferInstance
  have hcenter : (center E).map E.subtype = Z.subgroupOf U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      apply hz.le
      refine ⟨e y,?_,rfl⟩
      apply mem_center_iff.mpr
      intro p
      have hh := congrArg e (mem_center_iff.mp hy (e.symm p))
      simpa only [map_mul,e.apply_symm_apply] using hh
    · intro hx
      obtain ⟨p,hp,he⟩ := hz.ge hx
      change (p:G) = (x:G) at he
      have hxp : (x:G) ∈ P := he ▸ p.property
      refine ⟨⟨x,hxp⟩,?_,rfl⟩
      apply mem_center_iff.mpr
      intro q
      apply Subtype.ext
      apply Subtype.ext
      have hh := congrArg Subtype.val (mem_center_iff.mp hp (e q))
      change (q:G)*(p:G)=(p:G)*(q:G) at hh
      rwa [he] at hh
  have hs := sup_centralizer_eq_top_of_extraspecial_two E (by
    rw [hcenter]
    apply commutator_le.mpr
    intro x _ p hp
    exact hcomm (commutator_mem_commutator x.property hp))
  have hc : (centralizer (E : Set U)).map U.subtype = U ⊓ centralizer (P : Set G) := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.property,fun p hp => ?_⟩
      exact congrArg Subtype.val (hx ⟨p,hPU hp⟩ hp)
    · intro hx
      refine ⟨⟨x,hx.1⟩,?_,rfl⟩
      intro p hp
      exact Subtype.ext (hx.2 p hp)
  have hm := congrArg (fun A : Subgroup U => A.map U.subtype) hs
  rw [map_sup,map_subgroupOf_eq_of_le hPU,hc,←MonoidHom.range_eq_map,range_subtype] at hm
  exact hm

/-- Killing the centralizer supplement reduces the kernel to the original seed. -/
theorem commutatorPreimage_eq_of_centralizer_supplement
    (I P U Z : Subgroup G) (hIU : I ≤ normalizer (Z : Set G))
    (hUZ : U ≤ normalizer (Z : Set G))
    (hPU : P ≤ U) (hs : P ⊔ (U ⊓ centralizer (P : Set G)) = U)
    (hc : ⁅I,U ⊓ centralizer (P : Set G)⁆ ≤ Z) :
    commutatorPreimage I P Z = commutatorPreimage I U Z := by
  apply le_antisymm
  · intro x hx
    apply (mem_commutatorPreimage_iff I U Z hIU x).mpr
    obtain ⟨hxI,_⟩ := (mem_commutatorPreimage_iff I P Z hIU x).mp hx
    refine ⟨hxI,fun u hu => ?_⟩
    let K := commutatorPreimage U (zpowers x) Z
    have hPK : P ≤ K := le_commutatorPreimage hPU (by
      rw [commutator_comm]
      exact (commutator_mono (zpowers_le.mpr hx) le_rfl).trans
        (commutator_commutatorPreimage_le I P Z hIU))
    have hCK : U ⊓ centralizer (P : Set G) ≤ K := le_commutatorPreimage inf_le_left (by
      rw [commutator_comm]
      exact (commutator_mono (zpowers_le.mpr hxI) le_rfl).trans hc)
    have huK : u ∈ K := (hs ▸ sup_le hPK hCK) hu
    have hh := commutator_commutatorPreimage_le U (zpowers x) Z hUZ
      (commutator_mem_commutator huK (mem_zpowers x))
    rw [←commutatorElement_inv]
    exact Z.inv_mem hh
  · exact le_commutatorPreimage (commutatorPreimage_le I U Z)
      ((commutator_mono le_rfl hPU).trans (commutator_commutatorPreimage_le I U Z hIU))
end Subgroup
