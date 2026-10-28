module
public import Theory.Representation.PSL3Two.DoubledPoint
public import Theory.Representation.PSL3Two.NaturalSylowFixed

/-!
# Sylow-fixed points in a doubled natural module

A fixed pair lies in a natural summand or its diagonal, because a Sylow
subgroup fixes only one nonzero natural vector. Its stabilizer is therefore
S₄. Transport through the actual component quotient gives the literal point
centralizer map and its two-core kernel, without assuming a cubic already
lies in that centralizer. This removes the circular containment premise in
the ordinary-A₆ application of 13.4.10(2).

Source: Aschbacher–Smith, 13.4.10(2–4), printed pp.908–909.
-/

public noncomputable section
open Subgroup
namespace BinaryLinearThree

/-- A nonzero doubled vector fixed by a Sylow subgroup has S₄ stabilizer. -/
theorem doubled_sylow_fixed_stabilizer (P : Sylow 2 Group)
    (v : Vector × Vector) (hv : v ≠ 0)
    (hfix : ∀ a : P, (W.prod W) a.val v = v) :
    Nonempty ((OrbitStabilizers.natural v.1 ⊓ OrbitStabilizers.natural v.2 :
      Subgroup Group) ≃* Equiv.Perm (Fin 4)) := by
  let F := Representation.BinaryOffender.fixedSpace W (P : Subgroup Group)
  have h1 : v.1 ∈ F := fun p => congrArg Prod.fst (hfix p)
  have h2 : v.2 ∈ F := fun p => congrArg Prod.snd (hfix p)
  have hz : OrbitStabilizers.natural (0 : Vector) = ⊤ := by
    ext g
    simp only [OrbitStabilizers.mem_natural, map_zero, mem_top]
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := fun hh => hv (Prod.ext hv1 hh)
    rw [hv1,hz,top_inf_eq]
    exact ⟨OrbitStabilizers.naturalEquivSymmetric v.2 hv2⟩
  by_cases hv2 : v.2 = 0
  · rw [hv2,hz,inf_top_eq]
    exact ⟨OrbitStabilizers.naturalEquivSymmetric v.1 hv1⟩
  let : Nontrivial F := ⟨⟨⟨v.1,h1⟩,0,fun hh => hv1 (congrArg Subtype.val hh)⟩⟩
  have hc : Nat.card F = 2 := le_antisymm (card_sylow_natural_fixed_le_two P)
    (Nat.succ_le_of_lt (Finite.one_lt_card (α := F)))
  have he := ((Nat.card_eq_two_iff' (0 : F)).mp hc).unique
    (show (⟨v.1,h1⟩ : F) ≠ 0 from fun hh => hv1 (congrArg Subtype.val hh))
    (show (⟨v.2,h2⟩ : F) ≠ 0 from fun hh => hv2 (congrArg Subtype.val hh))
  have he' : v.1 = v.2 := congrArg Subtype.val he
  rw [he',inf_idem]
  exact ⟨OrbitStabilizers.naturalEquivSymmetric v.2 hv2⟩

/-- The point-centralizer quotient retains the original action and exact kernel. -/
theorem doubled_point_centralizer_of_sylow
    {G : Type*} [_root_.Group G] [Finite G]
    (K U : Subgroup G) (hKU : K ≤ normalizer (U : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : U ≃* Multiplicative (Vector × Vector))
    (he : letI := conjMulDistribMulActionOfLeNormalizer K U hKU
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod W W) (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)
    (w : U) (hw : w ≠ 1) (S : Sylow 2 K)
    (hSw : (S : Subgroup K).map K.subtype ≤ centralizer ({w.val} : Set G)) :
    ∃ f : (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = (K.pCoreIn 2).subgroupOf
        (K ⊓ centralizer ({w.val} : Set G)) := by
  let qK := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective qK :=
    eK.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K))
  let P₂ := S.mapSurjective hq
  let v := (e w).toAdd
  let P := OrbitStabilizers.natural v.1 ⊓ OrbitStabilizers.natural v.2
  let := conjMulDistribMulActionOfLeNormalizer K U hKU
  have hmem (k : K) : qK k ∈ P ↔ k.val ∈ centralizer ({w.val} : Set G) := by
    change (qK k ∈ OrbitStabilizers.natural v.1 ∧ qK k ∈ OrbitStabilizers.natural v.2) ↔ _
    rw [OrbitStabilizers.mem_natural,OrbitStabilizers.mem_natural]
    have hp : (Representation.prod W W) (qK k) v = v ↔
        W (qK k) v.1 = v.1 ∧ W (qK k) v.2 = v.2 := Prod.ext_iff
    rw [←hp]
    change (Representation.prod W W) (eK (QuotientGroup.mk' (pCore 2 K) k))
      (e w).toAdd = (e w).toAdd ↔ _
    rw [←he k w,Multiplicative.toAdd.injective.eq_iff,e.injective.eq_iff,Subtype.ext_iff]
    change k.val * w.val * k.val⁻¹ = w.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  have hv : v ≠ 0 := by
    intro hh
    apply hw
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hh
  have hfix (a : P₂) : (Representation.prod W W) a.val v = v := by
    obtain ⟨s,hs,heq⟩ := (show a.val ∈ (S : Subgroup K).map qK from a.property)
    have hh := (hmem s).mpr (hSw (mem_map_of_mem K.subtype hs))
    rw [←heq]
    exact Prod.ext (OrbitStabilizers.mem_natural _ _ |>.mp hh.1)
      (OrbitStabilizers.mem_natural _ _ |>.mp hh.2)
  obtain ⟨eP⟩ := doubled_sylow_fixed_stabilizer P₂ v hv hfix
  let C := K ⊓ centralizer ({w.val} : Set G)
  let p : C →* P := (qK.comp (inclusion inf_le_left)).codRestrict _
    (fun c => (hmem (inclusion inf_le_left c)).mpr c.property.2)
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨k,hk⟩ := (eK.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K))) x.val
    have hk' : qK k = x.val := hk
    have hkc : k.val ∈ centralizer ({w.val} : Set G) :=
      (hmem k).mp (hk'.symm ▸ x.property)
    exact ⟨⟨k.val,k.property,hkc⟩,Subtype.ext hk⟩
  refine ⟨eP.toMonoidHom.comp p,eP.surjective.comp hp,?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ eP.injective]
  ext c
  change p c = 1 ↔ c.val ∈ K.pCoreIn 2
  rw [Subtype.ext_iff]
  change eK (QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left c)) = 1 ↔ _
  rw [eK.map_eq_one_iff]
  exact (QuotientGroup.eq_one_iff (inclusion inf_le_left c)).trans
    (mem_map_iff_mem K.subtype_injective).symm

end BinaryLinearThree
