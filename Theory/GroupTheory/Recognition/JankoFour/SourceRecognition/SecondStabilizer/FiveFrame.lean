module
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.Perm.Closure

/-!
# Recognizing the order-1920 stabilizer from five involutions

Conjugation on five distinct elements gives a map from their normalizer to S₅.
A 5-cycle and a transposition make it surjective. Sixteen distinct commuting
square-one elements fill the kernel by the order formula, so the normalizer
is the whole group and its two-core is elementary of order sixteen.

This criterion is used for the literal second vector stabilizer in
Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent. Math. 105
(1991), (4.2), p.597, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FiveFrame
variable {G : Type*} [Group G] (v : Fin 5 → G) (hv : Function.Injective v)

noncomputable def numbering : Fin 5 ≃ Set.range v := Equiv.ofInjective v hv

private instance frameAction : MulAction (normalizer (Set.range v)) (Set.range v) where
  smul g x := ⟨g.val * x.val * g.val⁻¹, (mem_set_normalizer_iff.mp g.property x.val).mp x.property⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : G) * x.val * (1 : G)⁻¹ = x.val
    simp
  mul_smul g h x := by
    apply Subtype.ext
    change (g.val * h.val) * x.val * (g.val * h.val)⁻¹ =
      g.val * (h.val * x.val * h.val⁻¹) * g.val⁻¹
    group

noncomputable def action : normalizer (Set.range v) →* Equiv.Perm (Fin 5) :=
  (numbering v hv).symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom _ (Set.range v))

theorem action_spec (g : normalizer (Set.range v)) (i : Fin 5) :
    v (action v hv g i) = g.val * v i * g.val⁻¹ := by
  exact congrArg Subtype.val ((numbering v hv).apply_symm_apply (g • numbering v hv i))

variable [Finite G]

private theorem perm5_core : pCore 2 (Equiv.Perm (Fin 5)) = ⊥ := by
  by_contra hn
  have ht : Nontrivial (pCore 2 (Equiv.Perm (Fin 5))) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 5)) ht
  have hp : IsPGroup 2 (alternatingGroup (Fin 5)) :=
    pCore_isPGroup.of_injective (inclusion hle) (inclusion_injective hle)
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hd : 3 ∣ 2 ^ n := by
    rw [← hn,nat_card_alternatingGroup,Nat.card_fin]
    decide
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

include hv in
/-- A faithful five-frame, two conjugating permutations and sixteen distinct
centralizing involutions determine the complete group of order 1920. -/
theorem structure_of_frame (hcard : Nat.card G = 1920)
    (k : Fin 16 → G) (hki : Function.Injective k) (hk2 : ∀ i, k i ^ 2 = 1)
    (hkc : ∀ i j, k i * v j = v j * k i)
    (a b : G)
    (ha : ∀ i, a * v i * a⁻¹ = v (List.formPerm [0,1,2,3,4] i))
    (hb : ∀ i, b * v i * b⁻¹ = v (Equiv.swap 0 1 i)) :
    IsElementaryAbelian 2 (pCore 2 G) ∧ Nat.card (pCore 2 G) = 16 ∧
      Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 5)) := by
  classical
  let N := normalizer (Set.range v)
  have memN (g : G) (p : Equiv.Perm (Fin 5))
      (hg : ∀ i, g * v i * g⁻¹ = v (p i)) : g ∈ N := by
    apply mem_normalizer_fintype
    rintro x ⟨i,rfl⟩
    exact ⟨p i,(hg i).symm⟩
  let f := action v hv
  let aa : N := ⟨a,memN a _ ha⟩
  let bb : N := ⟨b,memN b _ hb⟩
  have hfa : f aa = List.formPerm [0,1,2,3,4] := by
    apply Equiv.ext
    intro i
    apply hv
    rw [action_spec v hv]
    exact ha i
  have hfb : f bb = Equiv.swap 0 1 := by
    apply Equiv.ext
    intro i
    apply hv
    rw [action_spec v hv]
    exact hb i
  have hsur : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← Equiv.Perm.closure_prime_cycle_swap
      (by decide : (Fintype.card (Fin 5)).Prime)
      (List.isCycle_formPerm (by decide : ([0,1,2,3,4] : List (Fin 5)).Nodup) (by decide))
      (by decide : (List.formPerm [0,1,2,3,4] : Equiv.Perm (Fin 5)).support = Finset.univ)
      (show (Equiv.swap (0 : Fin 5) 1).IsSwap from ⟨0,1,by decide,rfl⟩)]
    apply (closure_le _).mpr
    rintro p (rfl|rfl)
    · exact ⟨aa,hfa⟩
    · exact ⟨bb,hfb⟩
  have hkm (i) : k i ∈ N := memN (k i) 1 (fun j => by
    change k i * v j * (k i)⁻¹ = v j
    rw [hkc,mul_assoc,mul_inv_cancel,mul_one])
  let kk : Fin 16 → f.ker := fun i => ⟨⟨k i,hkm i⟩, by
    apply Equiv.ext
    intro j
    apply hv
    rw [action_spec v hv]
    change k i * v j * (k i)⁻¹ = v j
    rw [hkc,mul_assoc,mul_inv_cancel,mul_one]⟩
  have hkk : Function.Injective kk := by
    intro i j he
    exact hki (congrArg (fun x : f.ker => x.val.val) he)
  have hi : f.ker.index = 120 := by
    rw [index_ker,f.range_eq_top_of_surjective hsur,card_top,Nat.card_perm,Nat.card_fin]
    decide
  have hc := f.ker.card_mul_index
  rw [hi] at hc
  change Nat.card f.ker * 120 = Nat.card N at hc
  have hlo : 16 ≤ Nat.card f.ker := by
    simpa using Nat.card_le_card_of_injective kk hkk
  have hup : Nat.card N ≤ 1920 := hcard ▸ card_le_card_group N
  have hkcard : Nat.card f.ker = 16 := by omega
  have hNcard : Nat.card N = Nat.card G := by omega
  have htop : N = ⊤ := eq_top_of_card_eq N hNcard
  have hkbij : Function.Bijective kk := (Nat.bijective_iff_injective_and_card kk).mpr
    ⟨hkk,by rw [Nat.card_fin]; exact hkcard.symm⟩
  have hs (x : f.ker) : x ^ 2 = 1 := by
    obtain ⟨i,rfl⟩ := hkbij.surjective x
    apply Subtype.ext
    apply Subtype.ext
    exact hk2 i
  let he : IsElementaryAbelian 2 f.ker :=
    { toIsMulCommutative := ⟨⟨fun x y => by
        have inv_self (x : f.ker) : x⁻¹ = x :=
          inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
        have hh := inv_self (x*y)
        rw [mul_inv_rev,inv_self x,inv_self y] at hh
        exact hh.symm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs }
  have hkcore : f.ker = pCore 2 N := by
    have ht := f.comap_pCore_of_ker_isPGroup hsur (IsElementaryAbelian.isPGroup 2 f.ker)
    rwa [perm5_core,MonoidHom.comap_bot] at ht
  let e : G ≃* N := topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
  let ec := (e.subgroupMap (pCore 2 G)).trans
    (MulEquiv.subgroupCongr ((pCore_map_iso 2 e).trans hkcore.symm))
  refine ⟨IsElementaryAbelian.of_injective ec.toMonoidHom ec.injective,?_,?_⟩
  · exact (Nat.card_congr ec.toEquiv).trans hkcard
  · exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      ((QuotientGroup.quotientMulEquivOfEq hkcore.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hsur))⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FiveFrame
