module

public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.PPrimeCore

/-!
# The faithful action of the star quotient on the selected A₆ component

In a strongly quasithin finite group, an A₆ component is normal: distinct
conjugate components would commute and violate the local three-rank bound.
Its centralizer has order prime to three, because the component supplies an
E₉ and any commuting element of order three would give an embedded E₂₇.
The component dichotomy gives the reverse containment, identifying the
centralizer with O_{3′}(I), the kernel of the actual conjugation action.

These arguments use only hypotheses already present in the mixed setup;
no later factor containment, residual equality or local identification is used.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed pp.1162–1163; compare the normality reduction in F.6.10, p.306.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient
variable {I : Type*} [Group I] [Finite I]

omit [Finite I] in
private theorem component_disjoint_centralizer (L : Subgroup I)
    (e : L ≃* alternatingGroup (Fin 6)) : Disjoint L (centralizer (L : Set I)) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hz : (⟨x, hx.1⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (hx.2 l l.property)
  have hez := (Subgroup.centerCongr e ⟨⟨x, hx.1⟩, hz⟩).property
  change e ⟨x, hx.1⟩ ∈ center (alternatingGroup (Fin 6)) at hez
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hez
  exact congrArg Subtype.val (e.injective (hez.trans e.map_one.symm))

/-- The rank-two E9 in the component leaves no commuting element of order three. -/
theorem centralizer_coprime_three (hI : IsStronglyQuasithin I)
    (L : Subgroup I) (e : L ≃* alternatingGroup (Fin 6)) :
    Nat.Coprime 3 (Nat.card (centralizer (L : Set I))) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
  intro hd
  let C := centralizer (L : Set I)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hd
  let D := zpowers z
  let : CommGroup D := IsCyclic.commGroup
  have hD : Nat.card D = 3 := (Nat.card_zpowers z).trans hz
  obtain ⟨P, hP, hPc⟩ := alternatingGroup.exists_elementaryAbelian_nine_of_equiv e
  let := hP
  let : CommGroup P := { (inferInstance : Group P) with mul_comm := mul_comm' }
  let m : L × C →* I := L.subtype.noncommCoprod C.subtype
    (fun l c => c.property l l.property)
  have hm : Function.Injective m :=
    Subgroup.mul_injective_of_disjoint (component_disjoint_centralizer L e)
  let j : P × D →* L × C := P.subtype.prodMap D.subtype
  have hj : Function.Injective j := by
    intro a b h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))
  have hr : 3 ≤ primeRank 3 I := by
    apply primeRank_ge_of_elementary_embedding (A := P × D)
      (f := m.comp j) (hf := hm.comp hj)
    · intro a
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 3 P) a.1
      · change a.2 ^ 3 = 1
        simpa only [hD] using pow_card_eq_one' (x := a.2)
    · rw [Nat.card_prod, hPc, hD]
      norm_num
  have := hI 3 (by decide) (by decide)
  omega

/-- In the source SQTK group the selected A6 component is normal. -/
theorem component_normal (hI : IsStronglyQuasithin I)
    (L : Subgroup I) (hL : Theory.GroupTheory.IsComponent I L)
    (e : L ≃* alternatingGroup (Fin 6)) : L.Normal :=
  alternatingGroup.normal_of_component_a6_of_quasithin hI.quasithin L e hL

/-- The three-prime core is exactly the kernel of conjugation on the component. -/
theorem core_eq_centralizer (hI : IsStronglyQuasithin I)
    (L : Subgroup I) (hL : Theory.GroupTheory.IsComponent I L)
    (e : L ≃* alternatingGroup (Fin 6)) :
    pPrimeCore 3 I = centralizer (L : Set I) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : L.Normal := component_normal hI L hL e
  apply le_antisymm
  · rcases hL.normal_dichotomy (pPrimeCore 3 I) with hle | hc
    · have hc : Nat.card L = 360 := (Nat.card_congr e.toEquiv).trans
        AlternatingSix.ShadowLocal.card_A6
      have hd : 3 ∣ Nat.card (pPrimeCore 3 I) :=
        (show 3 ∣ Nat.card L by rw [hc]; decide).trans (Subgroup.card_dvd_of_le hle)
      exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mp
        pPrimeCore_coprime_card hd).elim
    · rw [commutator_comm] at hc
      exact commutator_eq_bot_iff_le_centralizer.mp hc
  · exact le_sSup ⟨inferInstance, centralizer_coprime_three hI L e⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient
