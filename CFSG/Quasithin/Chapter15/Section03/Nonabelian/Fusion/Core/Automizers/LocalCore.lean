module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.LocalCore.Actor
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Identifying the two-core of YT in 15.3.59

The actual Sylow subgroup of I = YU has order 1024. Its ambient image is
T ∩ O²(C_G(Z)), of index two in T, so T has order 2048. The surjective
natural action of M has actor SL₂(2) wr C₂, of order 72 and trivial two-core.
Its image of T is Sylow of order eight. Thus C_T(V) has order 256.

Write Q = O₂(Y). Relative normality of Y in M makes Q normal in M and
puts Q inside T. The genuine earlier equality C_Y(V) = Q puts Q inside
C_T(V), so their equal orders identify them. The image of Y has order
nine, by the supplied order of Y/Q. Hence the images of Y and T fill the
actor. The two-core of YT maps trivially to that actor and lies inside T,
so it lies inside C_T(V) = Q. Relative normality gives the reverse inclusion.
This avoids any assumption that M = YT or O²(M) = Y.

The final theorem is an independent conditional helper. It retains the
first three clauses of 15.3.59, the actual natural action and the earlier
centralizer equality. The orders of Q, Y/Q and the two-part of I are
explicit inputs from the separate s = 1 model calculation. The first
clause U = Q_H is retained in the source-facing wrapper; the order
argument itself only needs the Sylow and index clauses. Final source
assembly and discharge of the numerical inputs belong to Automizers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 15.3.59,
printed pp.1149–1150; the preceding centralizer equality is 15.3.49 and
the s = 1 module orders are supplied by 15.3.53–54 and 15.3.58.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.LocalCore
open Subgroup

variable {G : Type*} [Group G]

private theorem restricted_ker {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M) :
    (d.actor.comp (inclusion hXM)).ker = (centralizer (V : Set G)).subgroupOf X := by
  rw [← MonoidHom.comap_ker, d.ker_actor]
  rfl

variable [Finite G]

/-- The genuine Sylow clause and index-two clause give the ambient Sylow order. -/
theorem sylow_card_of_residual_index (T : Sylow 2 G) (Y Z ZS : Subgroup G)
    (hpart : 2 ^ (Nat.card (Y ⊔ Nonabelian.closureU Z ZS : Subgroup G)).factorization 2 = 1024)
    (S : Sylow 2 (Y ⊔ Nonabelian.closureU Z ZS : Subgroup G))
    (hS : (S : Subgroup (Y ⊔ Nonabelian.closureU Z ZS : Subgroup G)).map
      (Y ⊔ Nonabelian.closureU Z ZS).subtype = Nonabelian.residualSylow (T : Subgroup G) Z)
    (hindex : ((Nonabelian.residualSylow (T : Subgroup G) Z).subgroupOf
      (T : Subgroup G)).index = 2) : Nat.card T = 2048 := by
  have hsmall : Nat.card (Nonabelian.residualSylow (T : Subgroup G) Z) = 1024 := by
    rw [← hS, card_map_of_injective (Y ⊔ Nonabelian.closureU Z ZS).subtype_injective,
      S.card_eq_multiplicity, hpart]
  have he := ((Nonabelian.residualSylow (T : Subgroup G) Z).subgroupOf
    (T : Subgroup G)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show Nonabelian.residualSylow
      (T : Subgroup G) Z ≤ (T : Subgroup G) from inf_le_left)).toEquiv,
    hsmall, hindex] at he
  exact he.symm

/-- The natural actor and the exact orders identify the core of the Sylow supplement. -/
theorem local_core_of_sylow_card (T : Sylow 2 G) (M Y V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hMY : M ≤ normalizer (Y : Set G)) (d : NaturalOrthogonalAction M V)
    (hcentral : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
    (hQcard : Nat.card (Stellmacher.twoCoreAmbient Y) = 256)
    (hYquot : Nat.card (Y ⧸ pCore 2 Y) = 9) (hTcard : Nat.card T = 2048) :
    Stellmacher.twoCoreAmbient (Y ⊔ (T : Subgroup G)) = Stellmacher.twoCoreAmbient Y := by
  let Q := Stellmacher.twoCoreAmbient Y
  let X := Y ⊔ (T : Subgroup G)
  have hXM : X ≤ M := sup_le hYM hTM
  have hQY : Q ≤ Y := map_subtype_le _
  have hQM : Q ≤ M := hQY.trans hYM
  have hQn : M ≤ normalizer (Q : Set G) :=
    hMY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hQp : IsPGroup 2 Q := pCore_isPGroup.map Y.subtype
  let : (Q.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hQn
  have hQT : Q ≤ (T : Subgroup G) := by
    have hp : IsPGroup 2 (Q.subgroupOf M) :=
      hQp.of_equiv (subgroupOfEquivOfLe hQM).symm
    have h := hp.le_sylow_of_normal (T.subtype hTM)
    intro q hq
    exact h (show (⟨q, hQM hq⟩ : M) ∈ Q.subgroupOf M from hq)
  have hQC : Q ≤ centralizer (V : Set G) := hcentral.symm.le.trans inf_le_right
  let fY := d.actor.comp (inclusion hYM)
  have hYker : fY.ker = pCore 2 Y := by
    rw [restricted_ker]
    apply Subgroup.map_injective Y.subtype_injective
    rw [subgroupOf_map_subtype, inf_comm, hcentral]
    rfl
  have hYimage : Nat.card fY.range = 9 := by
    rw [← index_ker, hYker, index_eq_card, hYquot]
  let fT := d.actor.comp (inclusion hTM)
  have hTimage : Nat.card fT.range = 8 := by
    have hr : fT.range = ((T.subtype hTM).mapSurjective d.onto : Subgroup OrthogonalActor) := by
      rw [Sylow.coe_mapSurjective, Sylow.coe_subtype, MonoidHom.range_comp,
        inclusion_range]
    rw [hr, Sylow.card_eq_multiplicity, orthogonalActor_card]
    decide +kernel
  have hTkerCard : Nat.card fT.ker = 256 := by
    have hc := fT.ker.card_mul_index
    rw [index_ker, hTimage, hTcard] at hc
    omega
  have hTker : fT.ker.map (T : Subgroup G).subtype =
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
    rw [restricted_ker, subgroupOf_map_subtype, inf_comm]
  have hCT : (T : Subgroup G) ⊓ centralizer (V : Set G) = Q := by
    apply (eq_of_le_of_card_ge (le_inf hQT hQC) ?_).symm
    rw [← hTker, card_map_of_injective (T : Subgroup G).subtype_injective,
      hTkerCard, hQcard]
  let f := d.actor.comp (inclusion hXM)
  have hYrange : fY.range ≤ f.range := by
    rintro a ⟨y, rfl⟩
    exact ⟨⟨y, (le_sup_left : Y ≤ X) y.property⟩, rfl⟩
  have hTrange : fT.range ≤ f.range := by
    rintro a ⟨t, rfl⟩
    exact ⟨⟨t, (le_sup_right : (T : Subgroup G) ≤ X) t.property⟩, rfl⟩
  have honto : Function.Surjective f := by
    have h9 : 9 ∣ Nat.card f.range := hYimage ▸ card_dvd_of_le hYrange
    have h8 : 8 ∣ Nat.card f.range := hTimage ▸ card_dvd_of_le hTrange
    have h72 : 72 ∣ Nat.card f.range := (by decide : Nat.Coprime 9 8).mul_dvd_of_dvd_of_dvd h9 h8
    apply MonoidHom.range_eq_top.mp
    apply eq_top_of_card_eq
    rw [orthogonalActor_card]
    exact Nat.dvd_antisymm (orthogonalActor_card ▸ f.range.card_subgroup_dvd_card) h72
  apply le_antisymm
  · have hRT : Stellmacher.twoCoreAmbient X ≤ (T : Subgroup G) := by
      have hTX : (T : Subgroup G) ≤ X := le_sup_right
      have h := pCoreIn_le_sylow X (T.subtype hTX)
      rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTX] at h
      exact h
    have hnormal : ((pCore 2 X).map f).Normal :=
      (inferInstance : (pCore 2 X).Normal).map f honto
    have hmap : (pCore 2 X).map f ≤ pCore 2 OrthogonalActor :=
      le_sSup ⟨hnormal, pCore_isPGroup.map f⟩
    have hker : pCore 2 X ≤ f.ker :=
      (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp (orthogonalActor_twoCore ▸ hmap))
    have hRC : Stellmacher.twoCoreAmbient X ≤ centralizer (V : Set G) := by
      rintro x ⟨r, hr, rfl⟩
      have hk := hker hr
      rw [restricted_ker] at hk
      exact hk
    exact (le_inf hRT hRC).trans hCT.le
  · exact le_pCoreIn_of_normalizes hQp (hQY.trans le_sup_left) (hXM.trans hQn)

/-- The conditional local-core step of 15.3.59, retaining its actual first
three clauses and the numerical outputs of the separate s = 1 model calculation. -/
theorem core_eq_of_first_three (T : Sylow 2 G) (M Y V Z ZS : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hMY : M ≤ normalizer (Y : Set G)) (d : NaturalOrthogonalAction M V)
    (hcentral : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
    (hQcard : Nat.card (Stellmacher.twoCoreAmbient Y) = 256)
    (hYquot : Nat.card (Y ⧸ pCore 2 Y) = 9)
    (hpart : 2 ^ (Nat.card (Y ⊔ Nonabelian.closureU Z ZS : Subgroup G)).factorization 2 = 1024)
    (hfirst : Nonabelian.closureU Z ZS = Nonabelian.coreQ Z ∧
      (∃ S : Sylow 2 (Y ⊔ Nonabelian.closureU Z ZS : Subgroup G),
        (S : Subgroup (Y ⊔ Nonabelian.closureU Z ZS : Subgroup G)).map
          (Y ⊔ Nonabelian.closureU Z ZS).subtype =
            Nonabelian.residualSylow (T : Subgroup G) Z) ∧
      ((Nonabelian.residualSylow (T : Subgroup G) Z).subgroupOf (T : Subgroup G)).index = 2) :
    Stellmacher.twoCoreAmbient (Y ⊔ (T : Subgroup G)) = Stellmacher.twoCoreAmbient Y := by
  obtain ⟨_, ⟨S, hS⟩, hindex⟩ := hfirst
  exact local_core_of_sylow_card T M Y V hTM hYM hMY d hcentral hQcard hYquot
    (sylow_card_of_residual_index T Y Z ZS hpart S hS hindex)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.LocalCore
