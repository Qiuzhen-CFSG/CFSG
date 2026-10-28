module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.SameActor

/-!
# The prime-seven original actor

In PSL₂(7), a prescribed Sylow subgroup has order eight. The normalizers
of its two four-groups are distinct S₄ subgroups of index seven, so the
Sylow subgroup cannot have a unique maximal overgroup.

In PGL₂(7), the Sylow subgroup has order sixteen. The proved prime-field
maximal-overgroup calculation forces any maximal Sylow overgroup to have
order sixteen. For an actor inside the normal PSL₂ layer, the paired
four-group normalizer has order twenty-four and therefore escapes that
original maximal subgroup. Mapping its local witness back preserves the
original actor and literal Sylow intersection.

Source: Aschbacher–Smith E.1.14(6) and E.2.2, printed pp.214–216.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.Structure.PrimeSevenActor
open ValuesOdd.PSLTwoGeneration ValuesOdd.PSLTwoGeneration.PrimeGeometry Inner.SymmetricNormalizers

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

local instance {F : Type*} [Field F] [Finite F] : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem coatom_of_index_seven {G : Type*} [Group G] (A : Subgroup G) (hi : A.index=7) : IsCoatom A := by
  refine ⟨fun ht => by simp [ht] at hi, fun B hAB => ?_⟩
  have hm := relIndex_mul_index hAB.le
  rw [hi] at hm
  have hp : (A.relIndex B * B.index).Prime := hm ▸ (by decide : Nat.Prime 7)
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hB⟩ | ⟨_, hrel⟩
  · exact index_eq_one.mp hB
  · exact (hAB.not_ge (relIndex_eq_one.mp hrel)).elim

private theorem psl_seven_card {G F : Type*} [Group G] [Field F] [Finite F]
    (hF : Nat.card F=7) (e : G≃*PSL2 F) : Nat.card G=168 := by
  rw [Nat.card_congr e.toEquiv,psl2_card_formula F ⟨7,1,by decide,by decide,by decide,by simpa using hF⟩,hF]
  norm_num

private theorem perm_four_card {G : Type*} [Group G] (e : G≃*Equiv.Perm (Fin 4)) : Nat.card G=24 := by
  rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
  norm_num

theorem not_minimal_of_seven
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (hF : Nat.card F=7) (e : G≃*PSL2 F)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A≤T) : False := by
  have hG := psl_seven_card hF e
  have hT : Nat.card T=8 := by
    rw [T.card_eq_multiplicity,hG]
    rw [show 168 = 2^3*21 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.prime_two.factorization_pow]
    norm_num [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣21)]
  obtain ⟨B,hBT,hB,_,_,_,_,hN,_⟩ := exists_paired_four_and_local_witness_of_prime_field
    (p:=7) (by decide) hF e T hT.ge A hA hAT
  have hmax : ∀ V : Subgroup G, IsKleinFour V → V≤T →
      normalizer (V : Set G)=ChapterB.minimalParabolicMax T hP := by
    intro V hV hVT
    let : IsKleinFour V := hV
    obtain ⟨eV⟩ := normalizer_equiv_symmetric_four_of_prime_field (p:=7) (by decide) hF e T hT.ge V hV hVT
    have hi : (normalizer (V : Set G)).index=7 := by
      have hc := (normalizer (V : Set G)).card_mul_index
      rw [hG,perm_four_card eV] at hc
      omega
    exact ChapterB.minimalParabolicMax_unique T hP (coatom_of_index_seven _ hi)
      (normalizes_four_of_card_eight V (T : Subgroup G) hVT hT)
  exact hN ((hmax A hA hAT).trans (hmax B hB hBT).symm)

theorem pgl_seven_maximal_card
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (hF : Nat.card F=7) (e : G≃*PGL2 F)
    (T : Sylow 2 G) (M : Subgroup G) (hM : IsCoatom M) (hTM : (T : Subgroup G)≤M) :
    Nat.card M=16 := by
  let S := T.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hG : Nat.card G=336 := by rw [Nat.card_congr e.toEquiv,pgl2_card_formula,hF]; norm_num
  have hT : Nat.card T=16 := by
    rw [T.card_eq_multiplicity,hG]
    rw [show 336 = 2^4*21 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.prime_two.factorization_pow]
    norm_num [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣21)]
  have hd : 16∣Nat.card M := hT ▸ card_dvd_of_le hTM
  have hTM' : (S : Subgroup (PGL2 F))≤M.map e.toMonoidHom := map_mono hTM
  have hmodel := Diagonal.sylowOvergroupModel_of_prime_card (p:=7) (by decide) (by decide) hF S
    (M.map e.toMonoidHom) ((e.mapSubgroup.isCoatom_iff _).mpr hM) hTM'
  have hc : Nat.card (M.map e.toMonoidHom)=Nat.card M := card_map_of_injective e.injective
  rcases hmodel with he | ⟨n,hn,⟨em⟩⟩
  · obtain ⟨em⟩ := he
    have hcM : Nat.card M=24 := hc.symm.trans (perm_four_card em)
    norm_num [hcM] at hd
  · have hcM : Nat.card M=2*n := hc.symm.trans ((Nat.card_congr em.toEquiv).trans DihedralGroup.nat_card)
    rw [hF] at hn
    rcases hn with rfl | rfl
    · norm_num [hcM] at hd
    · norm_num at hcM
      exact hcM


theorem inner_actor_odd_escape_of_seven
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (hF : Nat.card F=7) (eG : G≃*PGL2 F)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) [K.Normal] (eK : K≃*PSL2 F)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A≤T) (hAK : A≤K) :
    ∃ P : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A P ∧ ECaseOdd A P ∧
      ¬P≤ChapterB.minimalParabolicMax T hP := by
  let M := ChapterB.minimalParabolicMax T hP
  have hM : Nat.card M=16 := pgl_seven_maximal_card hF eG T M
    (ChapterB.minimalParabolicMax_spec T hP).1 (ChapterB.minimalParabolicMax_spec T hP).2
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have hKcard := psl_seven_card hF eK
  have hScard : Nat.card S=8 := by
    rw [S.card_eq_multiplicity,hKcard]
    rw [show 168 = 2^3*21 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.prime_two.factorization_pow]
    norm_num [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣21)]
  let eA := subgroupOfEquivOfLe hAK
  have hA' : IsKleinFour (A.subgroupOf K) :=
    ⟨(Nat.card_congr eA.toEquiv).trans hA.card_four,
      (Monoid.exponent_eq_of_mulEquiv eA).trans hA.exponent_two⟩
  have hAS : A.subgroupOf K≤S := by rw [hS]; exact subgroupOf_mono K hAT
  obtain ⟨B,hBS,hB,_,_,_,_,_,hw⟩ := exists_paired_four_and_local_witness_of_prime_field
    (p:=7) (by decide) hF eK S hScard.ge (A.subgroupOf K) hA' hAS
  obtain ⟨eB⟩ := normalizer_equiv_symmetric_four_of_prime_field
    (p:=7) (by decide) hF eK S hScard.ge B hB hBS
  have hNM : ¬normalizer (B : Set K)≤M.subgroupOf K := by
    intro h
    have hle : (normalizer (B : Set K)).map K.subtype≤M := map_le_iff_le_comap.mpr h
    have hd := card_dvd_of_le hle
    rw [card_map_of_injective K.subtype_injective,perm_four_card eB,hM] at hd
    norm_num at hd
  obtain ⟨P,hAP,hSyl,hlocal,hPM⟩ := hw (M.subgroupOf K) hNM
  have hAP' : A≤P.map K.subtype := by
    rw [←map_subgroupOf_eq_of_le hAK]
    exact map_mono hAP
  have hSyl' := Diagonal.localSylow_map_of_comap K.subtype K.subtype_injective
    (S : Subgroup K) P (T : Subgroup G) hS.symm hSyl
  have hlocal' : LocalModel A (P.map K.subtype) := by
    have hh := Diagonal.localModel_map_injective hlocal K.subtype K.subtype_injective
    simpa only [map_subgroupOf_eq_of_le hAK] using hh
  have ho' := eCaseOdd_of_localModel A (P.map K.subtype) hA hAP' hlocal'
  have hodd : IsOddPrimePower (Nat.card F) := ⟨7,1,by decide,by decide,by decide,by simpa using hF⟩
  have hmodel : Nonempty (G≃*PSL2 F) ∨ Nonempty (G≃*PGL2 F) := Or.inr ⟨eG⟩
  let : IsKleinFour A := hA
  let : IsElementaryAbelian 2 A := { toIsMulCommutative := IsKleinFour.isMulCommutative, exponent_dvd_p := by rw [hA.exponent_two] }
  have htau := tau_eq_self_of_selfCentralizing T A hAT
    (SquareGeometry.LinearWitnesses.twoCore_eq_bot hodd (by omega) hmodel)
    (SquareGeometry.LinearWitnesses.kleinFour_centralizer_eq_self hodd hmodel A hA)
  have hrank : Group.rank ((A.subgroupOf (P.map K.subtype)).map
      (QuotientGroup.mk' (pCore 2 (P.map K.subtype))))=1 := by
    obtain ⟨r,_,_,_,_,_,hr⟩ := ho'
    exact hr
  refine ⟨P.map K.subtype,?_,ho',fun h => hPM (map_le_iff_le_comap.mp h)⟩
  exact ⟨⟨inferInstance,hAT,hAP',(by rw [htau]; exact le_inf hAT hAP'),hSyl',Or.inl ho'⟩,
    Or.inl ⟨ho',hrank.le⟩⟩

end CFSG.Quasithin.ChapterE.Structure.PrimeSevenActor

