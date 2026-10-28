module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SameActor
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.SameActor
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.NormalTransfer
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeGeometry

/-!
# Original-actor witnesses in the prime-field source row

The original minimal-parabolic hypotheses supply the involution centralizer
and Sylow size for the normal PSL₂(p) layer when p > 9. Its prescribed inner
actor gives a witness inside that layer; embedding back into the ambient
group preserves the literal Sylow intersection. Faithfulness of the normal
layer supplies the linear model needed for the ambient tau calculation.
For an outer actor in PGL₂(p), the actual maximal overgroup suffices for all
p > 5. Neither theorem replaces the actor by another family member.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.Structure
open ValuesOdd.PSLTwoGeneration ValuesOdd.PSLTwoGeneration.PrimeGeometry Inner.SameActor

local instance {F : Type*} [Field F] [Finite F] : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem prime_inner_actor_odd_escape
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H)=⊤)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F=p) (hp : 9<p)
    (e : K ≃* PSL2 F) (hC : centralizer (K : Set H)=⊥)
    (A : Subgroup H) (hA : IsKleinFour A) (hAT : A ≤ T) (hAK : A≤K) :
    ∃ P : Subgroup H, IsEMemberAt 1 (T : Subgroup H) A P ∧
      ECaseOdd A P ∧ ¬ P ≤ ChapterB.minimalParabolicMax T hP := by
  obtain ⟨S,hS,t,ht,hZ,hM,h8⟩ :=
    Structure.prime_linear_source_sylow_center T hP K hgen hpodd hFcard hp e
  have htne : t≠1 := by intro he; rw [he,orderOf_one] at ht; omega
  have hbound : 8 ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos h8
  let eA := subgroupOfEquivOfLe hAK
  have hA' : IsKleinFour (A.subgroupOf K) :=
    ⟨(Nat.card_congr eA.toEquiv).trans hA.card_four,
      (Monoid.exponent_eq_of_mulEquiv eA).trans hA.exponent_two⟩
  obtain ⟨P,hAP,hSyl,hlocal,ho,hPM⟩ := exists_local_escape_centralizer hpodd hFcard e
    S hbound (A.subgroupOf K) hA' (by rw [hS]; exact subgroupOf_mono K hAT) t htne _ hM.le
  have hAP' : A≤P.map K.subtype := by
    rw [←map_subgroupOf_eq_of_le hAK]
    exact map_mono hAP
  have hSyl' := Diagonal.localSylow_map_of_comap K.subtype K.subtype_injective
    (S : Subgroup K) P (T : Subgroup H) hS.symm hSyl
  have hlocal' : LocalModel A (P.map K.subtype) := by
    have hh := Diagonal.localModel_map_injective hlocal K.subtype K.subtype_injective
    simpa only [map_subgroupOf_eq_of_le hAK] using hh
  have ho' := eCaseOdd_of_localModel A (P.map K.subtype) hA hAP' hlocal'
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p,1,Fact.out,hpodd,by decide,by simpa using hFcard⟩
  have hmodel := linear_models_of_normal_prime_psl K (Fact.out : p.Prime) hpodd hFcard (by omega) e hC
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

theorem prime_outer_actor_odd_escape
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hpgt : 5 < p) (hFcard : Nat.card F=p)
    (T : Sylow 2 (PGL2 F)) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (A : Subgroup (PGL2 F)) (hA : IsKleinFour A)
    (hAT : A ≤ T) (hAJ : ¬ A ≤ commutator (PGL2 F)) :
    ∃ P : Subgroup (PGL2 F), IsEMemberAt 1 (T : Subgroup _) A P ∧ ECaseOdd A P ∧
      ¬ P ≤ ChapterB.minimalParabolicMax T hP :=
  Diagonal.SameActor.outer_odd_eMember_escape hpodd hpgt hFcard T A _ hA hAT hAJ
    (ChapterB.minimalParabolicMax_spec T hP).2 (ChapterB.minimalParabolicMax_spec T hP).1

end CFSG.Quasithin.ChapterE.Structure
