module
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Intersections
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.LocalStructure
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Excluding normal alternating-five subgroups in Goldschmidt triples

A proper subgroup of A₅ containing a prescribed Sylow four-group normalizes
that four-group. Intersecting either solvable Goldschmidt vertex with a
normal A₅ subgroup therefore identifies the four-group with the intersection's
two-core. Both vertices normalize it, contradicting simplicity of A₅.

This direct argument is used on the original O₃′ quotient in the final
13.2.7 argument. It needs neither an order-based recognition nor a table
exhaustion. Source: Aschbacher--Smith F.6.1 and 13.2.7, pp.304 and 883.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

private theorem five_sylow_normalized_by_solvable
    (K : Subgroup G) [K.Normal] (e : K ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 K) (X : Subgroup G) [Group.IsSolvable X]
    (hSX : (S : Subgroup K).map K.subtype ≤ X) :
    X ≤ normalizer ((S : Subgroup K).map K.subtype : Set G) := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let U := X.subgroupOf K
  have hSU : (S : Subgroup K) ≤ U := map_le_iff_le_comap.mp hSX
  have hU : U.map e.toMonoidHom ≠ ⊤ := by
    intro he
    let f : U →* X := { toFun := fun x => ⟨x.val.val,x.property⟩
                        map_one' := rfl
                        map_mul' := fun _ _ => rfl }
    let : Group.IsSolvable U := Group.isSolvable_of_isSolvable_injective
      (f := f) (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : X => (x : G)) hab)
    have hs : Group.IsSolvable (U.map e.toMonoidHom) :=
      Group.isSolvable_of_surjective (f := (e.subgroupMap U).toMonoidHom) (e.subgroupMap U).surjective
    have hs' : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_surjective
        (f := ((MulEquiv.subgroupCongr he).trans topEquiv).toMonoidHom)
        ((MulEquiv.subgroupCongr he).trans topEquiv).surjective
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) hs'
  have hUN : U ≤ normalizer (S : Set K) := by
    have hn := Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
      (S.mapSurjective e.surjective) (U.map e.toMonoidHom) (map_mono hSU) hU
    intro x hx
    apply mem_normalizer_iff.mpr
    intro s
    have hh := mem_normalizer_iff.mp (hn (mem_map_of_mem e.toMonoidHom hx)) (e s)
    change e.toMonoidHom s ∈ (S : Subgroup K).map e.toMonoidHom ↔
      e.toMonoidHom x * e.toMonoidHom s * (e.toMonoidHom x)⁻¹ ∈
        (S : Subgroup K).map e.toMonoidHom at hh
    simpa only [← map_inv, ← map_mul, mem_map_iff_mem (f := e.toMonoidHom) e.injective] using hh
  have hcore : U.pCoreIn 2 = (S : Subgroup K) := by
    apply le_antisymm
    · have hh := pCoreIn_le_sylow U (S.subtype hSU)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSU] using hh
    · exact le_pCoreIn_of_normalizes S.isPGroup' hSU hUN
  have he : (X ⊓ K).pCoreIn 2 = (S : Subgroup K).map K.subtype := by
    rw [← subgroupOf_map_subtype X K, ← map_pCoreIn_of_injective 2 U K.subtype
      K.subtype_injective,hcore]
  rw [←he]
  exact ((le_inf X.le_normalizer le_normalizer_of_normal).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (X ⊓ K) (pCore 2 (X ⊓ K : Subgroup G)))

/-- A Goldschmidt triple has no normal subgroup isomorphic to A₅. -/
theorem goldschmidt_no_normal_five (h : IsGoldschmidtTriple A B)
    (K : Subgroup G) [K.Normal] (e : K ≃* alternatingGroup (Fin 5)) : False := by
  obtain ⟨S,hS⟩ := h.subnormal_intersection_sylow K (inferInstance : K.Normal).isSubnormal
  have hSI : (S : Subgroup K).map K.subtype ≤ A ⊓ B := by
    rw [hS,subgroupOf_map_subtype]
    exact inf_le_left
  let : Group.IsSolvable A := h.local_solvable
  let : Group.IsSolvable B := h.symm.local_solvable
  have hn : normalizer ((S : Subgroup K).map K.subtype : Set G) = ⊤ := by
    apply top_unique
    rw [←h.generated]
    exact sup_le (five_sylow_normalized_by_solvable K e S A (hSI.trans inf_le_left))
      (five_sylow_normalized_by_solvable K e S B (hSI.trans inf_le_right))
  have hSN : (S : Subgroup K).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro k _
    apply mem_normalizer_iff.mpr
    intro s
    have hk : (k : G) ∈ normalizer ((S : Subgroup K).map K.subtype : Set G) := hn ▸ mem_top _
    have hh := mem_normalizer_iff.mp hk (s : G)
    change K.subtype s ∈ (S : Subgroup K).map K.subtype ↔
      K.subtype (k * s * k⁻¹) ∈ (S : Subgroup K).map K.subtype at hh
    simpa only [mem_map_iff_mem K.subtype_injective] using hh
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup K := e.isSimpleGroup
  rcases hSN.eq_bot_or_eq_top with hb | ht
  · have hi := S.not_dvd_index
    rw [hb,index_bot,Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hi
    norm_num [Nat.factorial] at hi
  · have hp : IsPGroup 2 K := (S.isPGroup'.of_equiv
      ((MulEquiv.subgroupCongr ht).trans topEquiv))
    let : Group.IsNilpotent K := hp.isNilpotent
    let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.not_isSolvable K inferInstance
end CFSG.Quasithin.ChapterF.SourceAssembly
