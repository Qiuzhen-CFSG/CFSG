module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Odd residuals below products of symmetric groups of degree three

Every two-residual in a subgroup of a product of S₃ groups has exponent
three: each coordinate lies in A₃. For a normal subgroup with odd
2-residual, adjoining a two-subgroup gives an odd normal subgroup with
2-group quotient. The same property passes to every subgroup by residual
monotonicity. These statements retain the actual embeddings and residuals.

Source application: the J(N)T action in Aschbacher–Smith, original 14.1.4.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem pResidual_threeGroup_of_injective_permThree_product
    {ι : Type*} (f : G →* (ι → Equiv.Perm (Fin 3))) (hf : Function.Injective f) :
    IsPGroup 3 (pResidual 2 G) := by
  have hres : pResidual 2 (Equiv.Perm (Fin 3)) ≤ alternatingGroup (Fin 3) := by
    apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    simp
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    rfl
  intro x
  refine ⟨1,Subtype.ext (hf ?_)⟩
  change f ((x : G) ^ 3) = f 1
  simp only [map_pow,map_one]
  funext i
  let fi := (Pi.evalMonoidHom (fun _ : ι => Equiv.Perm (Fin 3)) i).comp f
  have hx : fi x ∈ alternatingGroup (Fin 3) :=
    hres (map_pResidual_le 2 fi (mem_map_of_mem fi x.property))
  have he := pow_card_eq_one' (x := (⟨fi x,hx⟩ : alternatingGroup (Fin 3)))
  rw [hcard] at he
  exact congrArg Subtype.val he

theorem exists_odd_normal_two_quotient_of_normal_sup
    (I S : Subgroup G) [I.Normal] (hodd : Odd (Nat.card (pResidual 2 I)))
    (hS : IsPGroup 2 S) (hgen : I ⊔ S = ⊤) :
    ∃ L : Subgroup G, ∃ hL : L.Normal, Odd (Nat.card L) ∧
      @IsPGroup 2 (G ⧸ L) (@QuotientGroup.Quotient.group G _ L hL) := by
  let L := (pResidual 2 I).map I.subtype
  let q := QuotientGroup.mk' L
  have hI : IsPGroup 2 (I.map q) := by
    intro x
    obtain ⟨a,ha,he⟩ := x.property
    obtain ⟨n,hn⟩ := isPGroup_quotient_pResidual (G := I) 2
      (QuotientGroup.mk' (pResidual 2 I) ⟨a,ha⟩)
    have hn' : (⟨a,ha⟩ : I) ^ 2 ^ n ∈ pResidual 2 I :=
      (QuotientGroup.eq_one_iff _).mp hn
    refine ⟨n,Subtype.ext ?_⟩
    change (x:G ⧸ L) ^ 2 ^ n = 1
    rw [← he,← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem I.subtype hn')
  let : (I.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective L)
  have hp := hI.to_sup_of_normal_left (hS.map q)
  have htop : I.map q ⊔ S.map q = ⊤ := by
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective L)]
  refine ⟨L,inferInstance,hodd.of_dvd_nat (card_map_dvd _ _),?_⟩
  exact (htop ▸ hp).of_equiv topEquiv

omit [Finite G] in
theorem odd_pResidual_subgroup_of_odd_normal_two_quotient
    (L : Subgroup G) [L.Normal] (hodd : Odd (Nat.card L))
    (hquot : IsPGroup 2 (G ⧸ L)) (K : Subgroup G) :
    Odd (Nat.card (pResidual 2 K)) := by
  have hle : (pResidual 2 K).map K.subtype ≤ L :=
    (map_pResidual_le 2 K.subtype).trans (sInf_le ⟨inferInstance,hquot⟩)
  apply hodd.of_dvd_nat
  rw [← card_map_of_injective (K := pResidual 2 K) K.subtype_injective]
  exact card_dvd_of_le hle

end Theory.GroupTheory
