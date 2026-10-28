module
public import Theory.GroupTheory.SylowTwistedGeneratingPair
public import Theory.SpecificGroups.SL2.UniqueMaximalKernel
public import Theory.GroupTheory.AbelianGeneratorCore
public import Theory.ElementaryAbelian.Injective
/-!
# The original rank-one pair and its two-core intersection

A generating pair of full Sylow two-subgroups has abelian images of order
four in the prescribed PSL2(4) quotient. Their image intersection is central
in A₅ and hence trivial. The original unique-maximal kernel theorem therefore
identifies the actual intersection with O₂(H), without identifying the
arbitrary original kernel K with O₂(H). The actual Sylow quotient by that
two-core is elementary abelian of order four.

Combining this with the specified Sylow automorphism constructs the literal
twisted generating pair used in Niles 2.3 and 4.2(a)–(d). The central omega
module condition in 4.2(e) is the separate natural-recognition theorem 2.9.

Source: Niles, *Pushing-up in finite groups* (1979), printed pp.29–30,44.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SL2
private theorem five_sylow_card (P : Sylow 2 (alternatingGroup (Fin 5))) : Nat.card P = 4 := by
  rw [P.card_eq_multiplicity,nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  decide +kernel
private theorem five_sylow_elementary (P : Sylow 2 (alternatingGroup (Fin 5))) :
    IsElementaryAbelian 2 P := by
  have hc : Nat.card P = 2 ^ 2 := five_sylow_card P
  let := IsPGroup.isMulCommutative_of_card_eq_prime_sq hc
  refine ⟨?_⟩
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  have hd := pow_card_eq_one' (x := x)
  rw [five_sylow_card] at hd
  have hall : ∀ x : alternatingGroup (Fin 5), x ^ 4 = 1 → x ^ 2 = 1 := by decide +kernel
  exact Subtype.ext (hall x (congrArg Subtype.val hd))

/-- The original Sylow quotient by the literal two-core is elementary of order four. -/
theorem sylow_twoCore_quotient_elementary_four
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    IsElementaryAbelian 2 (S ⧸ (pCore 2 H).subgroupOf S) ∧
    Nat.card (S ⧸ (pCore 2 H).subgroupOf S) = 4 := by
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let f := (e.trans a).toMonoidHom.comp (QuotientGroup.mk' K)
  have hf : Function.Surjective f := (e.trans a).surjective.comp (QuotientGroup.mk'_surjective K)
  let P := S.mapSurjective hf
  let r := f.subgroupMap (S : Subgroup H)
  have hr : Function.Surjective r := f.subgroupMap_surjective (S : Subgroup H)
  have hk : r.ker = (pCore 2 H).subgroupOf S := by
    have hSK := (original_kernel_reduction_of_psl2_four hF S hu K e).1
    ext x
    change r x = 1 ↔ x.val ∈ pCore 2 H
    rw [← Subtype.coe_inj]
    change f x = 1 ↔ x.val ∈ pCore 2 H
    change (e.trans a) (QuotientGroup.mk' K x.val) = 1 ↔ x.val ∈ pCore 2 H
    rw [(e.trans a).map_eq_one_iff]
    change QuotientGroup.mk x.val = (1 : H ⧸ K) ↔ _
    rw [QuotientGroup.eq_one_iff,←hSK]
    exact (and_iff_right x.property).symm
  let d : (S ⧸ (pCore 2 H).subgroupOf S) ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr)
  let := five_sylow_elementary P
  exact ⟨IsElementaryAbelian.of_injective d.toMonoidHom d.injective,
    (Nat.card_congr d.toEquiv).trans (five_sylow_card P)⟩

/-- The actual conjugate Sylow intersection in the PSL2(4) Main Hypothesis. -/
theorem generating_sylow_intersection_eq_twoCore
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (hF : Nat.card F = 4) (S T : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hgen : (S : Subgroup H) ⊔ (T : Subgroup H) = ⊤) :
    (S : Subgroup H) ⊓ (T : Subgroup H) = pCore 2 H := by
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let f := (e.trans a).toMonoidHom.comp (QuotientGroup.mk' K)
  have hf : Function.Surjective f := (e.trans a).surjective.comp (QuotientGroup.mk'_surjective K)
  let P := S.mapSurjective hf
  let R := T.mapSurjective hf
  let := five_sylow_elementary P
  let := five_sylow_elementary R
  have hPR : (P : Subgroup (alternatingGroup (Fin 5))) ⊔ R = ⊤ := by
    change (S : Subgroup H).map f ⊔ (T : Subgroup H).map f = ⊤
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective f hf]
  have hI : (P : Subgroup (alternatingGroup (Fin 5))) ⊓ R = ⊥ := by
    apply le_bot_iff.mp
    exact (inf_le_center_of_abelian_generators _ _ hPR).trans
      (alternatingGroup.center_eq_bot (by simp)).le
  have hk : f.ker = K := by
    ext x
    change (e.trans a) (QuotientGroup.mk' K x) = 1 ↔ x ∈ K
    rw [(e.trans a).map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hIK : (S : Subgroup H) ⊓ (T : Subgroup H) ≤ K := by
    rw [←hk,←Subgroup.map_eq_bot_iff]
    exact le_bot_iff.mp ((map_inf_le _ _ _).trans hI.le)
  have hSK := (original_kernel_reduction_of_psl2_four hF S hu K e).1
  exact le_antisymm (hSK ▸ le_inf inf_le_left hIK)
    (le_inf (pCore_isPGroup.le_sylow_of_normal S) (pCore_isPGroup.le_sylow_of_normal T))

/-- The exact initial Main Hypothesis pair, retaining the arbitrary original kernel. -/
theorem original_twisted_pair_of_psl2_four
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    ∃ g : H,
      (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H ∧
      ∀ A : Subgroup S, A.Normal →
        (A.map (twistedConjugacy (S : Subgroup H) α g).toMonoidHom).map
          ((S : Subgroup H).map (MulAut.conj g).toMonoidHom).subtype =
          A.map (S : Subgroup H).subtype → A = ⊥ := by
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hc : Nat.card (H ⧸ K) = 60 := by
    rw [Nat.card_congr (e.trans a).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have htwo : 2 ∣ Nat.card H := (show 2 ∣ Nat.card (H ⧸ K) by rw [hc]; decide).trans
    K.card_quotient_dvd_card
  obtain ⟨g,hg,hfix⟩ := exists_twisted_generating_pair S α hu hno (S.ne_bot_of_dvd_card htwo)
  refine ⟨g,hg,?_,hfix⟩
  exact generating_sylow_intersection_eq_twoCore hF S
    (S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective)
    hu K e hg
end Theory.SpecificGroups.SL2
