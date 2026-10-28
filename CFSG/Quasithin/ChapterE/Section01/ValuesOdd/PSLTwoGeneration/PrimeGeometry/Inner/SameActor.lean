module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections

/-!
# Escape for a prescribed inner four-group

Pair the given four-group with a second one whose normalizer is S₄.
Self-centrality of the second four-group makes that normalizer have trivial
ambient centralizer. It therefore escapes every nonidentity element
centralizer. The witness retains the given actor and the prescribed Sylow
intersection, and the intrinsic odd-section calculation supplies degree one.

Source: Aschbacher–Smith E.1.14(6) and E.2.2, printed pp.214–216.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
namespace SameActor

private theorem center_perm_four : center (Equiv.Perm (Fin 4))=⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have h : ∀ x : Equiv.Perm (Fin 4), (∀ y, y*x=x*y) → x=1 := by decide
  exact h x (mem_center_iff.mp hx)

private theorem centralizer_normalizer_eq_bot
    {G : Type*} [Group G] (B : Subgroup G)
    (hc : centralizer (B : Set G)=B)
    (e : normalizer (B : Set G) ≃* Equiv.Perm (Fin 4)) :
    centralizer (normalizer (B : Set G) : Set G)=⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hxB : x∈B := hc ▸ ((centralizer_le (show (B : Set G) ⊆ normalizer (B : Set G) from B.le_normalizer)) hx)
  have hxN : x∈normalizer (B : Set G) := B.le_normalizer hxB
  have hxZ : (⟨x,hxN⟩ : normalizer (B : Set G)) ∈ center (normalizer (B : Set G)) := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hx y y.property)
  have he := (centerCongr e ⟨⟨x,hxN⟩,hxZ⟩).property
  change e ⟨x,hxN⟩ ∈ center (Equiv.Perm (Fin 4)) at he
  rw [center_perm_four,mem_bot] at he
  have hx1 : (⟨x,hxN⟩ : normalizer (B : Set G))=1 := e.injective (by simpa only [map_one] using he)
  exact mem_bot.mpr (congrArg Subtype.val hx1)

theorem exists_local_escape_centralizer
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F=p)
    (e : G ≃* PSL2 F) (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A ≤ T)
    (t : G) (ht : t≠1) (M : Subgroup G) (hM : M ≤ centralizer ({t} : Set G)) :
    ∃ P : Subgroup G, A ≤ P ∧
      (∃ S : Sylow 2 P, (S : Subgroup P)=(T : Subgroup G).subgroupOf P) ∧
      LocalModel A P ∧ ECaseOdd A P ∧ ¬P≤M := by
  obtain ⟨B,hBT,hB,hBA,h8,hAB,hAn,hN,hw⟩ :=
    SymmetricNormalizers.exists_paired_four_and_local_witness_of_prime_field hpodd hFcard e T hT A hA hAT
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p,1,Fact.out,hpodd,by decide,by simpa using hFcard⟩
  have hc : centralizer (B : Set G)=B := kleinFour_selfCentralizing_of_embedding hodd
    (Matrix.ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom)
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective) B hB
  obtain ⟨eB⟩ := SymmetricNormalizers.normalizer_equiv_symmetric_four_of_prime_field hpodd hFcard e T hT B hB hBT
  have hNM : ¬ normalizer (B : Set G) ≤ M := by
    intro hle
    have htC : t∈centralizer (normalizer (B : Set G) : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hM (hle hx))
    rw [centralizer_normalizer_eq_bot B hc eB,mem_bot] at htC
    exact ht htC
  obtain ⟨P,hAP,hS,hlocal,hPM⟩ := hw M hNM
  exact ⟨P,hAP,hS,hlocal,eCaseOdd_of_localModel A P hA hAP hlocal,hPM⟩


theorem exists_odd_eMember_escape_centralizer
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hpgt : 3 < p) (hFcard : Nat.card F=p)
    (e : G ≃* PSL2 F) (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A ≤ T)
    (t : G) (ht : t≠1) (M : Subgroup G) (hM : M ≤ centralizer ({t} : Set G)) :
    ∃ P : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A P ∧ ECaseOdd A P ∧ ¬ P ≤ M := by
  obtain ⟨P,hAP,hS,hlocal,ho,hPM⟩ :=
    exists_local_escape_centralizer hpodd hFcard e T hT A hA hAT t ht M hM
  let : IsKleinFour A := hA
  let : IsElementaryAbelian 2 A := { toIsMulCommutative := IsKleinFour.isMulCommutative, exponent_dvd_p := by rw [hA.exponent_two] }
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p,1,Fact.out,hpodd,by decide,by simpa using hFcard⟩
  have hmodel : Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F) := Or.inl ⟨e⟩
  have htau := tau_eq_self_of_selfCentralizing T A hAT
    (SquareGeometry.LinearWitnesses.twoCore_eq_bot hodd (by omega) hmodel)
    (SquareGeometry.LinearWitnesses.kleinFour_centralizer_eq_self hodd hmodel A hA)
  have hrank : Group.rank ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))) = 1 := by
    obtain ⟨r, _, _, _, _, _, hr⟩ := ho
    exact hr
  refine ⟨P, ?_, ho, hPM⟩
  exact ⟨⟨inferInstance,hAT,hAP,(by rw [htau]; exact le_inf hAT hAP),hS,Or.inl ho⟩,
    Or.inl ⟨ho,hrank.le⟩⟩

end SameActor
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
