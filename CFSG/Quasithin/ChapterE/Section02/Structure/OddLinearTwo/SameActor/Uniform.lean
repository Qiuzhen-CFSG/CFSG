module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.SameActor.PrimeSeven
public import GorensteinWalter.PGL2PerfectSubnormal

/-!
# A degree-one odd witness for the original prime-field actor

A self-centralizing normal PSL₂(p) layer identifies the ambient group with
PSL₂(p) or PGL₂(p). For an inner actor, the original minimal-parabolic
centralizer argument applies when p > 9; the separate order-seven proof
handles p = 7. For an outer actor, perfectness identifies the image of the
marked normal layer with the actual PGL₂ commutator. The outer witness
therefore applies to the image of this same actor and transports back.

The conclusion retains the original Sylow subgroup, actor, and unique
maximal overgroup. No inner-actor restriction, overgroup model, local witness,
or parameter bound is assumed. This is the native model input to the marked
component-action argument for the paired odd row of E.2.2 and E.6.27.

Source: Aschbacher–Smith E.2.2 and E.1.14(6), printed pp.214–216.
-/

public section

namespace CFSG.Quasithin.ChapterE.Structure
open Subgroup GorensteinWalter ValuesOdd.PSLTwoGeneration ValuesOdd.PSLTwoGeneration.PrimeGeometry

local instance {F : Type*} [Field F] [Finite F] : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem prime_actor_odd_escape
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) [K.Normal] (hgen : K ⊔ (T : Subgroup G)=⊤)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hF : Nat.card F=p) (hp : 7≤p)
    (eK : K≃*PSL2 F) (hC : centralizer (K : Set G)=⊥)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A≤T) :
    ∃ P : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A P ∧ ECaseOdd A P ∧
      ¬P≤ChapterB.minimalParabolicMax T hP := by
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p,1,Fact.out,hpodd,by decide,by simpa using hF⟩
  have hmodel := linear_models_of_normal_prime_psl K (Fact.out : p.Prime) hpodd hF (by omega) eK hC
  by_cases hAK : A≤K
  · have hpCases : p=7 ∨ 9<p := by
      by_cases h : 9<p
      · exact Or.inr h
      · have hprime : p.Prime := Fact.out
        have hle : p≤9 := by omega
        interval_cases p <;> norm_num at *
    rcases hpCases with rfl | hlarge
    · rcases hmodel with he | he
      · obtain ⟨eG⟩ := he
        exact (PrimeSevenActor.not_minimal_of_seven hF eG T hP A hA hAT).elim
      · obtain ⟨eG⟩ := he
        exact PrimeSevenActor.inner_actor_odd_escape_of_seven hF eG T hP K eK A hA hAT hAK
    · exact prime_inner_actor_odd_escape T hP K hgen hpodd hF hlarge eK hC A hA hAT hAK
  · rcases hmodel with he | he
    · obtain ⟨eG⟩ := he
      have hKtop : K=⊤ := eq_of_le_of_card_ge le_top (by
        rw [card_top]
        exact (Nat.card_congr (eG.trans eK.symm).toEquiv).le)
      exact (hAK (hKtop ▸ le_top)).elim
    · obtain ⟨eG⟩ := he
      let : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
      let : IsSimpleGroup K := eK.isSimpleGroup
      let : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F (by omega)
      let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f:=eK.symm.toMonoidHom) eK.symm.surjective
      have hKne : K≠⊥ := (nontrivial_iff_ne_bot K).mp inferInstance
      have hKm : K.map eG.toMonoidHom = commutator (PGL2 F) :=
        (pgl2_perfect_subnormal_eq_commutator F hodd (K.map eG.toMonoidHom)
          ((map_eq_bot_iff_of_injective K eG.injective).not.mpr hKne)
          (Group.IsPerfect.map eG.toMonoidHom)
          ((inferInstance : K.Normal).isSubnormal.map eG.surjective)).2
      have hAJ : ¬A.map eG.toMonoidHom≤commutator (PGL2 F) := by
        intro h
        apply hAK
        intro a ha
        exact (mem_map_iff_mem eG.injective).mp (hKm.symm ▸ h (mem_map_of_mem eG.toMonoidHom ha))
      let S := T.mapSurjective (f:=eG.toMonoidHom) eG.surjective
      let M := ChapterB.minimalParabolicMax T hP
      obtain ⟨P,hmem,ho,hPM⟩ := Diagonal.SameActor.outer_odd_eMember_escape hpodd (by omega) hF S
        (A.map eG.toMonoidHom) (M.map eG.toMonoidHom)
        (isKleinFour_map_of_injective A hA eG.toMonoidHom eG.injective)
        (map_mono hAT) hAJ (map_mono (ChapterB.minimalParabolicMax_spec T hP).2)
        ((eG.mapSubgroup.isCoatom_iff _).mpr (ChapterB.minimalParabolicMax_spec T hP).1)
      have hm := hmem.map_equiv eG.symm
      have ho' := ho.map_injective eG.symm.toMonoidHom eG.symm.injective
      have hAM : (A.map eG.toMonoidHom).map eG.symm.toMonoidHom=A := by simp [map_map]
      have hTM : ((T : Subgroup G).map eG.toMonoidHom).map eG.symm.toMonoidHom=(T : Subgroup G) := by simp [map_map]
      change IsEMemberAt 1 (((T : Subgroup G).map eG.toMonoidHom).map eG.symm.toMonoidHom)
        ((A.map eG.toMonoidHom).map eG.symm.toMonoidHom) (P.map eG.symm.toMonoidHom) at hm
      rw [hAM,hTM] at hm
      rw [hAM] at ho'
      refine ⟨P.map eG.symm.toMonoidHom,hm,ho',fun h => hPM ?_⟩
      have hh := map_mono (f:=eG.toMonoidHom) h
      simpa [map_map] using hh

end CFSG.Quasithin.ChapterE.Structure
