module

public import Theory.SpecificGroups.SymmetricEight.FourBlockQuotient
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The cubic quotient obstruction inside the four-block stabilizer

A subgroup of the four-block stabilizer containing the binary-tree Sylow
cannot have two-core quotient of order six. After factoring out the ambient
two-core, the obstruction is the dihedral Sylow in the binary-plane wreath
actor: a nontrivial normal Sylow subgroup contains an element inverting the
whole cubic residual. A cubic element would then belong to the two-core.

This records an obstruction to lifting a cubic local action into the literal
point stabilizer; it does not supply the missing lift. Source context:
Aschbacher–Smith 14.7.2 and 14.7.51, printed pp.1043 and 1065.
-/

public section

open Subgroup
open Theory.GroupTheory.WreathTwoResidual
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource

private theorem actor_sylow_card (P : Sylow 2 Actor) : Nat.card P = 8 := by
  obtain ⟨e⟩ := wreath_two_sylow_mulEquiv_dihedral_four P
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

/-- A Sylow-containing subgroup of the binary-plane wreath actor cannot have
two-core quotient of order six. -/
theorem actor_core_quotient_card_ne_six (P : Sylow 2 Actor) (J : Subgroup Actor) (hPJ : (P : Subgroup Actor) ≤ J)
    : Nat.card (J ⧸ pCore 2 J) ≠ 6 := by
  intro hq
  let R := (pCore 2 J).map J.subtype
  have hnJ : J ≤ normalizer (R : Set Actor) := by
    have h := (pCore 2 J).le_normalizer_map J.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  have hRP : R ≤ (P : Subgroup Actor) := by
    rintro x ⟨y,hy,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (P.subtype hPJ) hy
  have hRne : R ≠ ⊥ := by
    intro hb
    have hc : pCore 2 J = ⊥ :=
      (map_eq_bot_iff_of_injective _ J.subtype_injective).mp hb
    have hJ : Nat.card J = 6 := by
      rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 J), hq, hc]
      simp
    have hd := card_dvd_of_le hPJ
    rw [actor_sylow_card P, hJ] at hd
    norm_num at hd
  obtain ⟨r,hr,_,hi⟩ := exists_normal_sylow_inverter P R hRP (hPJ.trans hnJ) hRne
  have hd : 3 ∣ Nat.card J := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 J), hq]
    omega
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hcA : orderOf (c : Actor) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hc
  have hcR : (c : Actor) ∈ pResidual 2 Actor := by
    apply mem_pResidual_of_orderOf_coprime
    rw [hcA]
    decide
  have hc3 : (c : Actor)^3 = 1 := by rw [← hcA]; exact pow_orderOf_eq_one _
  have hpow : (c : Actor)*(c : Actor)*(c : Actor)=1 := by
    simpa only [pow_succ,pow_zero,one_mul] using hc3
  have hinv : (c : Actor)⁻¹*(c : Actor)⁻¹=(c : Actor) := by
    rw [← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right hpow
  have hconj := (hnJ c.property r⁻¹).mp (R.inv_mem hr)
  have hcIn : (c : Actor) ∈ R := by
    have h := R.mul_mem hr hconj
    simpa only [← mul_assoc,hi (c : Actor) hcR,hinv] using h
  have hcne : (⟨(c : Actor),hcIn⟩ : R) ≠ 1 := by
    intro he
    have hh : (c : Actor) = 1 := congrArg Subtype.val he
    rw [hh, orderOf_one] at hcA
    contradiction
  have hdiv := (pCore_isPGroup (p := 2) (G := J)).map J.subtype |>.dvd_orderOf hcne
  norm_num only [Subgroup.orderOf_mk, hcA, Nat.reduceDvd] at hdiv


private theorem cover_core_quotient_card_ne_six {H : Type*} [Group H] [Finite H]
    (f : H →* Actor) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (P : Sylow 2 H) (J : Subgroup H) (hPJ : (P : Subgroup H) ≤ J) :
    Nat.card (J ⧸ pCore 2 J) ≠ 6 := by
  let g := f.comp J.subtype
  let K := g.range
  let Q := P.mapSurjective hf
  have hQK : (Q : Subgroup Actor) ≤ K := by
    rintro x ⟨y,hy,rfl⟩
    exact ⟨⟨y,hPJ hy⟩,rfl⟩
  have hgk : IsPGroup 2 g.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hk.comap_of_injective J.subtype J.subtype_injective
  let e := g.rangeRestrict.pCoreQuotientEquiv g.rangeRestrict_surjective hgk
  intro hc
  apply actor_core_quotient_card_ne_six Q K hQK
  exact (Nat.card_congr e.toEquiv).symm.trans hc

/-- No overgroup of the binary-tree Sylow inside the unordered four-block
stabilizer has two-core quotient of order six. -/
theorem four_block_core_quotient_card_ne_six (J : Subgroup S8)
    (hT : treeGroup ≤ J) (hJ : J ≤ fourStabilizer) :
    Nat.card (J ⧸ pCore 2 J) ≠ 6 := by
  let H := fourStabilizer
  let e := Theory.SpecificGroups.SymmetricEight.FourBlockQuotient.fourStabilizerQuotientEquivActor
  let f : H →* Actor := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ x ∈ pCore 2 H
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff _
  have hk : IsPGroup 2 f.ker := hker ▸ pCore_isPGroup
  have hTH : (treeSylow : Subgroup S8) ≤ H :=
    treeGroup_le_flagStabilizer.trans inf_le_right
  let P := treeSylow.subtype hTH
  let K := J.subgroupOf H
  have hPK : (P : Subgroup H) ≤ K := by
    intro x hx
    exact hT hx
  let eJ := subgroupOfEquivOfLe hJ
  let eqJ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  intro hc
  apply cover_core_quotient_card_ne_six f hf hk P K hPK
  exact (Nat.card_congr eqJ.toEquiv).trans hc

/-- In particular, the literal four-block overgroup cannot realize a local
S₃ quotient above the binary-tree Sylow. -/
theorem four_block_cubic_quotient_impossible (J : Subgroup S8)
    (hT : treeGroup ≤ J) (hJ : J ≤ fourStabilizer)
    (e : (J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) : False := by
  apply four_block_core_quotient_card_ne_six J hT hJ
  rw [Nat.card_congr e.toEquiv]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
