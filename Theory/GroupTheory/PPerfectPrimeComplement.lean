module
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Faithfulness on an odd prime complement of a two-perfect group

Suppose a two-perfect group has prime order p modulo its two-core.
Every subgroup of order p complements that core. If a homomorphism
kills this subgroup, its entire image is a two-group, so the image is
trivial. Simplicity of the prime subgroup therefore makes every
nontrivial homomorphism faithful on it.

Source application: the faithful quintic action in Aschbacher--Smith
6.1.4, printed p.665.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H]
  {p : ℕ} [Fact p.Prime]

private theorem prime_complement_sup_twoCore
    (hp : p ≠ 2) (hq : Nat.card (G ⧸ pCore 2 G) = p)
    (D : Subgroup G) (hD : Nat.card D = p) : D ⊔ pCore 2 G = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hcop : Nat.Coprime p (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨a,ha⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [ha]
    exact ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp).pow_right a
  have hd : IsPGroup p D := isPGroup_iff_card_dvd_pow.mpr ⟨1,by simp [hD]⟩
  have hi := injective_comp_subtype_of_coprime_ker q hcop D hd
  have hc : Nat.card (D.map q) = Nat.card D := by
    exact Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap D)
      ⟨fun x y he => hi (congrArg Subtype.val he),q.subgroupMap_surjective D⟩).toEquiv |>.symm
  have ht : D.map q = ⊤ := (D.map q).eq_top_of_card_eq (hc.trans (hD.trans hq.symm))
  have hh := congrArg (Subgroup.comap q) ht
  simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh

/-- Nontrivial homomorphisms of a two-perfect prime-by-two group are
faithful on each subgroup of the specified odd prime order. -/
theorem prime_complement_restriction_injective
    (hG : IsPPerfect 2 G) (hp : p ≠ 2)
    (hq : Nat.card (G ⧸ pCore 2 G) = p)
    (D : Subgroup G) (hD : Nat.card D = p)
    (f : G →* H) (hf : f ≠ 1) : Function.Injective (f.comp D.subtype) := by
  let : IsSimpleGroup D := isSimpleGroup_of_prime_card hD
  let r := f.comp D.subtype
  apply (MonoidHom.ker_eq_bot_iff r).mp
  rcases r.normal_ker.eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    have hDf : D.map f = ⊥ := (Subgroup.map_eq_bot_iff D).mpr (by
      intro d hd
      have hdker : (⟨d,hd⟩ : D) ∈ r.ker := ht.symm ▸ mem_top (⟨d,hd⟩ : D)
      exact hdker)
    have hfr : f.range ≤ (pCore 2 G).map f := by
      rw [MonoidHom.range_eq_map,←prime_complement_sup_twoCore hp hq D hD,
        Subgroup.map_sup,hDf,bot_sup_eq]
    have htriv := hG.hom_eq_one_of_isPGroup
      (((pCore_isPGroup (p := 2) (G := G)).map f).to_le hfr) f.rangeRestrict
    apply hf
    ext g
    exact congrArg (fun a : G →* f.range => (a g : H)) htriv

end Theory.GroupTheory
