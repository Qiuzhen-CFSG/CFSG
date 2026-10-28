module

public import Theory.GroupTheory.ThompsonSylowCentralizer
public import Theory.GroupTheory.CentralSylowCenterQuotient
public import Theory.GroupTheory.SylowCentricNormalQuotient
public import Theory.GroupTheory.RankTwoCharacteristicThreeQuotient
public import BenderSuzuki.External.Huppert.IV.CentralQuotientComplement

/-!
# Normal three-complements from noncyclic abelian cubic quotients

Let a finite group A be covered by a group of three-rank at most two.
If A has a noncyclic abelian three-group quotient, then A has a normal
three-complement.

Induct on the target order. Every subgroup containing a Sylow three-group
still covers the same abelian quotient, and the original cover restricts
to its literal preimage. Thompson's normal-complement theorem reduces to
the centralizer of the Sylow center and the normalizers of the two Thompson
subgroups. Proper local subgroups are handled by induction.

If a Thompson subgroup is normal, its Sylow centralizer lies inside it;
quotienting the three-prime core gives characteristic three, so the earlier
characteristic-three theorem applies. If the Sylow center is central, either
Burnside transfer gives a complement or a nontrivial central subgroup in the
abelian quotient kernel permits induction on a central quotient. Central
quotient lifting finishes that case. Rank always stays on the original cover.
-/

public noncomputable section
open Subgroup BenderSuzuki.External
open scoped IsMulCommutative
namespace Theory.GroupTheory
universe u v w

private theorem complement_of_normal_sylow_centric
    {B : Type u} [Group B] [Finite B] {A : Type v} [Group A] [Finite A]
    {D : Type w} [Group D] [IsMulCommutative D]
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (q : A →* D) (hq : Function.Surjective q) (hD : IsPGroup 3 D)
    (hnoncyclic : ¬IsCyclic D) (S : Sylow 3 A)
    (U : Subgroup A) [U.Normal] (hUS : U ≤ (S : Subgroup A))
    (hc : (S : Subgroup A) ⊓ centralizer (U : Set A) ≤ U) : HasNormalPComplement 3 A := by
  let O := pPrimeCore 3 A
  let π := QuotientGroup.mk' O
  have hkill : O ≤ q.ker := by
    have hc : Nat.Coprime 3 (Nat.card (O.map q)) :=
      (pPrimeCore_coprime_card (p := 3) (G := A)).of_dvd_right (O.card_map_dvd q)
    have hcard : Nat.card (O.map q) = 1 :=
      (hD.to_subgroup (O.map q)).card_eq_or_dvd.resolve_right
        (Nat.prime_three.coprime_iff_not_dvd.mp hc)
    exact (Subgroup.map_eq_bot_iff _).mp (Subgroup.card_eq_one.mp hcard)
  let f : A ⧸ O →* D := QuotientGroup.lift O q hkill
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective O q hq hkill
  have hchar := S.centralizer_pCore_quotient_pPrimeCore_le_of_normal_centric U hUS hc
  have hp : IsPGroup 3 (A ⧸ O) :=
    isThreeGroup_of_characteristic_three_of_noncyclic_abelian_quotient
      (π.comp cover) ((QuotientGroup.mk'_surjective O).comp hcover) hrank
      hchar f hf hD hnoncyclic
  exact ⟨O,inferInstance,pPrimeCore_coprime_card,hp⟩

private theorem surjective_restriction_of_sylow_le
    {A : Type v} [Group A] [Finite A] {D : Type w} [Group D]
    (q : A →* D) (hq : Function.Surjective q) (hD : IsPGroup 3 D)
    (S : Sylow 3 A) (H : Subgroup A) (hSH : (S : Subgroup A) ≤ H) :
    Function.Surjective (q.comp H.subtype) := by
  let : Finite D := Finite.of_surjective q hq
  have hStop : (S : Subgroup A).map q = ⊤ :=
    ((S.mapSurjective hq).is_maximal' (hD.to_subgroup ⊤) le_top).symm
  have hHtop : H.map q = ⊤ := top_unique (hStop ▸ map_mono hSH)
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp,range_subtype,hHtop]

/-- A finite image of a group of three-rank at most two has a normal
three-complement whenever it has a noncyclic abelian three-group quotient. -/
theorem hasNormalThreeComplement_of_noncyclic_abelian_three_quotient
    {B : Type u} [Group B] [Finite B] {A : Type v} [Group A] [Finite A]
    {D : Type w} [Group D] [IsMulCommutative D]
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (q : A →* D) (hq : Function.Surjective q) (hD : IsPGroup 3 D)
    (hnoncyclic : ¬IsCyclic D) : HasNormalPComplement 3 A := by
  classical
  let rec aux {C : Type u} [Group C] [Finite C] {X : Type v} [Group X] [Finite X]
      (f : C →* X) (hf : Function.Surjective f) (hr : primeRank 3 C ≤ 2)
      (r : X →* D) (hrsurj : Function.Surjective r) : HasNormalPComplement 3 X := by
    let S : Sylow 3 X := Classical.choice inferInstance
    have local_complement (H : Subgroup X) (hSH : (S : Subgroup X) ≤ H) (hne : H ≠ ⊤) :
        HasNormalPComplement 3 H := by
      let fH := f.subgroupComap H
      have hfH : Function.Surjective fH := f.subgroupComap_surjective_of_surjective H hf
      have hrH : primeRank 3 (H.comap f) ≤ 2 := (primeRank_subgroup_le 3 _).trans hr
      have hqH := surjective_restriction_of_sylow_le r hrsurj hD S H hSH
      have hlt : Nat.card H < Nat.card X :=
        lt_of_le_of_ne H.card_le_card_group (fun he => hne (H.card_eq_iff_eq_top.mp he))
      exact aux fH hfH hrH (r.comp H.subtype) hqH
    have center_complement : HasNormalPComplement 3
        (centralizer (centerIn (S : Subgroup X) : Set X)) := by
      let Z := centerIn (S : Subgroup X)
      let H := centralizer (Z : Set X)
      by_cases hH : H = ⊤
      · have hZ : (center S).map (S : Subgroup X).subtype ≤ center X := by
          have hz : Z ≤ centralizer (Set.univ : Set X) := by
            simpa only [coe_top] using (le_centralizer_iff.mp
              (show (⊤ : Subgroup X) ≤ centralizer (Z : Set X) from hH.ge))
          simpa only [Z,centerIn_eq_map_center,centralizer_univ] using hz
        have hcomp : HasNormalPComplement 3 X := by
          rcases S.hasNormalPComplement_or_central_kernel r hZ with hc | ⟨N,hN,hne,hNc,hNk⟩
          · exact hc
          · let : N.Normal := hN
            let π := QuotientGroup.mk' N
            let rb : X ⧸ N →* D := QuotientGroup.lift N r hNk
            have hrb : Function.Surjective rb :=
              QuotientGroup.lift_surjective_of_surjective N r hrsurj hNk
            have hlt : Nat.card (X ⧸ N) < Nat.card X := by
              have hn : 1 < Nat.card N := by
                let : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hne
                exact Finite.one_lt_card
              rw [card_eq_card_quotient_mul_card_subgroup N]
              simpa using Nat.mul_lt_mul_of_pos_left hn (Nat.card_pos (α := X ⧸ N))
            have hc := aux (π.comp f) ((QuotientGroup.mk'_surjective N).comp hf) hr rb hrb
            exact hasNormalPComplement_of_central_quotient N hNc hc
        have htop : HasNormalPComplement 3 (⊤ : Subgroup X) :=
          hasNormalPComplement_of_equiv 3 topEquiv.symm hcomp
        change HasNormalPComplement 3 H
        rwa [hH]
      · apply local_complement H _ hH
        exact le_centralizer_iff.mpr inf_le_right
    have order_complement : HasNormalPComplement 3
        (normalizer (thompsonSubgroup (S : Subgroup X) : Set X)) := by
      let J := thompsonSubgroup (S : Subgroup X)
      let H := normalizer (J : Set X)
      by_cases hH : H = ⊤
      · let : J.Normal := normalizer_eq_top_iff.mp hH
        have hc := complement_of_normal_sylow_centric f hf hr r hrsurj hD hnoncyclic S J
          (thompsonSubgroup_le _) (inf_centralizer_thompsonSubgroup_le _)
        have htop : HasNormalPComplement 3 (⊤ : Subgroup X) :=
          hasNormalPComplement_of_equiv 3 topEquiv.symm hc
        change HasNormalPComplement 3 H
        rwa [hH]
      · exact local_complement H (le_normalizer_thompsonSubgroup _) hH
    have rank_complement : HasNormalPComplement 3
        (normalizer (huppertRankThompsonSubgroup (S : Subgroup X) : Set X)) := by
      let J := huppertRankThompsonSubgroup (S : Subgroup X)
      let H := normalizer (J : Set X)
      by_cases hH : H = ⊤
      · let : J.Normal := normalizer_eq_top_iff.mp hH
        have hc := complement_of_normal_sylow_centric f hf hr r hrsurj hD hnoncyclic S J
          (huppertRankThompsonSubgroup_le _) (inf_centralizer_rankThompsonSubgroup_le _ S.isPGroup')
        have htop : HasNormalPComplement 3 (⊤ : Subgroup X) :=
          hasNormalPComplement_of_equiv 3 topEquiv.symm hc
        change HasNormalPComplement 3 H
        rwa [hH]
      · exact local_complement H (le_normalizer_rankThompsonSubgroup _) hH
    exact huppert_IV_6_2_thompson_normal_p_complement (by decide) S
      center_complement order_complement rank_complement
  termination_by Nat.card X
  decreasing_by all_goals assumption
  exact aux cover hcover hrank q hq

end Theory.GroupTheory
