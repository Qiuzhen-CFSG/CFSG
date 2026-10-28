module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.Bounds
public import Theory.GroupTheory.RankOneSylowExtension
public import Mathlib.GroupTheory.Nilpotent

/-!
# A rank-one normal subgroup obstructs E-generation

Take the elementary abelian subgroups of L having the order of a full Sylow
2-subgroup P. This is an ambient conjugation-invariant family. In a Sylow
subgroup T containing P, its weak closure is precisely P: every family member
contained in T lies in T ∩ L = P and has the same order.

An E-member containing P either normalizes P or contains L. In the second
case its image of P modulo O₂(K), respectively O_∞(K), retains its full rank,
since L is nonsolvable simple and both kernels are solvable. Thus generation
below that rank is trapped in the proper normalizer N_G(P). No restrictions
on the ambient outer automorphisms are needed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--6 and the PSL₂ case of E.1.14(1), printed pp.209--211, 214.
The concrete PSL₂ module discharges all local hypotheses of this reduction.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical
open Subgroup Subgroup.RankOneSylowExtension
variable {G : Type*} [Group G] [Finite G]

/-- A normal nonsolvable simple group with an elementary Sylow and a unique
proper Sylow overgroup prevents E-generation below that Sylow's rank. -/
theorem not_isEGenerated_of_normal_rankOne (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (hL : ¬ Group.IsSolvable L) (P : Sylow 2 L)
    [IsElementaryAbelian 2 P]
    (hproper : ∀ H : Subgroup L, (P : Subgroup L) ≤ H → H ≠ ⊤ →
      H ≤ normalizer (P : Set L))
    (hn : normalizer (P : Set L) ≠ ⊤)
    (i : ℕ) (hi : i < Group.rank P) : ¬ IsEGenerated i G := by
  let A : Subgroup G := (P : Subgroup L).map L.subtype
  have hAL : A ≤ L := map_subtype_le _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map L.subtype
  obtain ⟨T, hAT⟩ := (P.isPGroup'.map L.subtype).exists_le_sylow
  have hAeq : A = (T : Subgroup G) ⊓ L := by
    have hPT : (P : Subgroup L) ≤ (T : Subgroup G).subgroupOf L :=
      map_le_iff_le_comap.mp hAT
    have he := P.is_maximal' T.isPGroup'.comap_subtype hPT
    change (T : Subgroup G).subgroupOf L = (P : Subgroup L) at he
    rw [← subgroupOf_map_subtype, he]
  let Ω : Set (Subgroup G) := {B | B ≤ L ∧ IsElementaryAbelian 2 B ∧ Nat.card B = Nat.card A}
  have hAΩ : A ∈ Ω := ⟨hAL, inferInstance, rfl⟩
  have hΩ : IsElementaryFamily Ω := by
    refine ⟨fun B hB => hB.2.1, ?_⟩
    intro g B hB
    let : IsElementaryAbelian 2 B := hB.2.1
    refine ⟨?_, IsElementaryAbelian.map _, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact (inferInstance : L.Normal).conj_mem b (hB.1 hb) g
    · exact (Nat.card_congr (B.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm.trans hB.2.2
  have huniq : ∀ B ∈ Ω, B ≤ (T : Subgroup G) → B = A := by
    intro B hB hBT
    apply eq_of_le_of_card_ge
    · rw [hAeq]
      exact le_inf hBT hB.1
    · exact hB.2.2.ge
  have hw : weakClosure (T : Subgroup G) Ω = A := by
    apply le_antisymm
    · apply sSup_le
      intro B hB
      exact (huniq B hB.1 hB.2).le
    · exact le_sSup ⟨hAΩ, hAT⟩
  have hnA : normalizer (A : Set G) ≠ ⊤ := by
    intro he
    apply hn
    have hpre := congrArg (fun H : Subgroup G => H.comap L.subtype) he
    have hc : A.comap L.subtype = (P : Subgroup L) :=
      comap_map_eq_self_of_injective L.subtype_injective _
    rw [comap_normalizer_eq_of_le_range (by simpa using hAL), hc, comap_top] at hpre
    exact hpre
  apply not_isEGenerated_of_members_le T Ω hΩ
    (normalizer (A : Set G)) hnA
  · rw [hw]
  · intro B hB hBT K hK
    have he := huniq B hB hBT
    subst B
    rcases le_or_le_normalizer L P hproper K hK.1.2.2.1 with hLK | hKN
    · exfalso
      have hri : i < Group.rank A := by
        rwa [← Group.rank_congr ((P : Subgroup L).equivMapOfInjective L.subtype
          L.subtype_injective)]
      rcases hK.2 with hodd | hcomp
      · let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
        have hr := rank_image_solvable_quotient_eq L A K hL hAL hLK (pCore 2 K)
        exact (Nat.not_le_of_gt hri) (hr ▸ hodd.2)
      · have hr := rank_image_solvable_quotient_eq L A K hL hAL hLK (solvableRadical K)
        exact (Nat.not_le_of_gt hri) (hr ▸ hcomp.2)
    · exact hKN

end CFSG.Quasithin.ChapterE.ValuesEvenClassical
