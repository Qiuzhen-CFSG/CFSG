module

public import Theory.GroupTheory.Commutator.ThompsonAB
public import Theory.GroupTheory.PrimeOrderCentralizerSylow
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.PerfectSylowPreservingAction
public import Theory.GroupTheory.PerfectNormalizerInner
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.CComponent.SolvableQuotient

/-!
# Recognizing a full residual from an involution-centralizing seed

A perfect seed S supplements O₂(Q) in a normal perfect subgroup Q.
If the two-core of C(t) is central and t centralizes S, Thompson's A×B
lemma makes O₂(Q) centralize S, forcing Q=S. Solvable outer action then
places the full residual in S C(S). If the t-centralizer in C(S) has no
factor of four, transfer and odd-order solvability make C(S) solvable;
thus the full residual is S.

Application: the cubic centralizer in Aschbacher--Smith 4.2.13, p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative


namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- One involution centralizer with two-part two forces solvability. -/
theorem solvable_of_involution_centralizer_no_four (t : G) (ht : orderOf t = 2)
    (hc : ¬ 4 ∣ Nat.card (centralizer ({t} : Set G))) : Group.IsSolvable G := by
  let P : Sylow 2 G := default
  have hP : Nat.card P = 2 := sylow_card_eq_prime_of_centralizer t ht hc P
  have hcyc : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨hn, ho, hq⟩ := P.twoResidual_normal_complement_of_isCyclic hcyc
  let := hn
  let : Group.IsSolvable (pResidual 2 G) := odd_order_theorem _ ho
  let : Group.IsNilpotent (G ⧸ pResidual 2 G) := hq.isNilpotent
  exact Group.isSolvable_of_ker_le_range (pResidual 2 G).subtype
    (QuotientGroup.mk' (pResidual 2 G)) (by simp)

/-- Thompson centralization identifies the perfect overgroup with its seed. -/
theorem perfect_eq_of_centralizer_core (t : G) (ht : orderOf t = 2)
    (S Q : Subgroup G) [Group.IsPerfect S] [Group.IsPerfect Q] [Q.Normal]
    (hS : S ≤ centralizer ({t} : Set G))
    (hgen : S ⊔ Q.pCoreIn 2 = Q)
    (hcore : pCore 2 (centralizer ({t} : Set G)) ≤
      center (centralizer ({t} : Set G))) : Q = S := by
  let D := centralizer ({t} : Set G)
  let P := Q.pCoreIn 2
  let : P.Normal := inferInstanceAs (((pCore 2 Q).map Q.subtype).Normal)
  let B := zpowers t
  have hB : IsPGroup 2 B := IsPGroup.of_card (n := 1)
    (by simpa only [B,Nat.card_zpowers,pow_one] using ht)
  have hBA : ⁅B,S⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [le_centralizer_iff]
    simpa only [B,zpowers_eq_closure,centralizer_closure] using hS
  have hres : pResidual 2 S = ⊤ := by
    apply (pResidual_eq_top_iff 2 S).mpr
    intro N hN hq
    let := hN
    let : Group.IsNilpotent (S ⧸ N) := hq.isNilpotent
    exact top_unique (by simpa only [solvableResidual_eq_top] using
      solvableResidual_le_of_solvable_quotient N)
  have hfix : P ⊓ centralizer (B : Set G) ≤ centralizer (S : Set G) := by
    intro y hy
    have hyD : y ∈ D := by
      exact mem_centralizer_singleton_iff.mpr (hy.2 t (mem_zpowers t)).symm
    have hp : P.subgroupOf D ≤ pCore 2 D :=
      le_sSup ⟨inferInstance,(isPGroup_pCoreIn 2 Q).comap_subtype⟩
    have hz := hcore (hp (show (⟨y,hyD⟩ : D) ∈ P.subgroupOf D from hy.1))
    intro s hs
    exact congrArg D.subtype (mem_center_iff.mp hz ⟨s,hS hs⟩)
  have hc := thompson_a_times_b_centralizer S B P hB (isPGroup_pCoreIn 2 Q)
    hres le_normalizer_of_normal le_normalizer_of_normal hBA hfix
  have hnS : (S.subgroupOf Q).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [←hgen]
    exact sup_le S.le_normalizer
      ((commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_le_normalizer _))
  have hSQ : S ≤ Q := hgen ▸ le_sup_left
  have hSn : S.IsSubnormal := .step S Q hSQ (inferInstance : Q.Normal).isSubnormal hnS
  let : Group.IsNilpotent P := (isPGroup_pCoreIn 2 Q).isNilpotent
  have he := hSn.solvableResidual_sup_eq P
    (show S ≤ normalizer (P : Set G) from le_normalizer_of_normal)
  have hm := le_map_solvableResidual_of_isPerfect Q (S ⊔ P) hgen.ge
  exact le_antisymm (hm.trans he.le) hSQ

/-- The same seed is the full residual when its centralizer has the stated small fixed subgroup. -/
theorem solvableResidual_eq_of_involution_seed (t : G) (ht : orderOf t = 2)
    (S Q : Subgroup G) [Group.IsPerfect S] [Group.IsPerfect Q] [Q.Normal]
    [Group.IsSolvable (MulAut.Outer S)]
    (hS : S ≤ centralizer ({t} : Set G))
    (hgen : S ⊔ Q.pCoreIn 2 = Q)
    (hcore : pCore 2 (centralizer ({t} : Set G)) ≤
      center (centralizer ({t} : Set G)))
    (hsmall : ¬ 4 ∣ Nat.card ((centralizer (S : Set G)).subgroupOf
      (centralizer ({t} : Set G)))) : solvableResidual G = S := by
  have he := perfect_eq_of_centralizer_core t ht S Q hS hgen hcore
  let : S.Normal := he ▸ inferInstanceAs Q.Normal
  let Z := centralizer (S : Set G)
  have htZ : t ∈ Z := by
    intro s hs
    exact mem_centralizer_singleton_iff.mp (hS hs)
  let z : Z := ⟨t,htZ⟩
  have hz : orderOf z = 2 := (orderOf_coe z).symm.trans ht
  have hno : ¬ 4 ∣ Nat.card (centralizer ({z} : Set Z)) := by
    let f : centralizer ({z} : Set Z) →* Z.subgroupOf (centralizer ({t} : Set G)) := {
      toFun y := ⟨⟨y.val.val,mem_centralizer_singleton_iff.mpr
        (congrArg Z.subtype (mem_centralizer_singleton_iff.mp y.property))⟩,y.val.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact fun hd => hsmall (hd.trans (card_dvd_of_injective f
      (fun a b hh => Subtype.ext (Subtype.ext (congrArg
        (fun y : Z.subgroupOf (centralizer ({t} : Set G)) => (y.val : G)) hh)))))
  let : Group.IsSolvable Z := solvable_of_involution_centralizer_no_four z hz hno
  have hle := perfect_le_sup_centralizer_of_solvable_outer S (solvableResidual G)
    (show solvableResidual G ≤ normalizer (S : Set G) from le_normalizer_of_normal)
  have hm := le_map_solvableResidual_of_isPerfect (solvableResidual G) (S ⊔ Z) hle
  have hh := (inferInstance : S.Normal).isSubnormal.solvableResidual_sup_eq Z
    (show S ≤ normalizer (Z : Set G) from le_normalizer_of_normal)
  exact le_antisymm (hm.trans hh.le) (le_solvableResidual_of_isPerfect S)

end Subgroup
