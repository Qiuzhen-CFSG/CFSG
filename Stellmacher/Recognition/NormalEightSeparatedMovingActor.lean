module

public import Stellmacher.Recognition.NormalEightSeparatedActorTransport
public import Stellmacher.Recognition.NormalEightSeparatedConjugateRigidity
public import Theory.GroupTheory.PGroup.MovingElementaryAction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The moving four in the separated case

The normalizer condition produces a conjugate of the returning four which
normalizes the elementary sixteen but does not centralize it. The local
omega identity is an explicit input. Rigidity of separated conjugate fours
and the elementary commutator argument upgrade this moving conjugate to a
fixed-point-free one-sided actor. No bound on elementary subgroups of an
arbitrary subgroup is used.

Source: Janko–Thompson, Math. Z. 113 (1970), first half of printed p.395,
referring to Lemma 5.1 on printed p.394.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedMovingActor

open Subgroup NormalFourCentralOmegaTwo NormalEightSeparatedFusion
open NormalEightSeparatedTransport NormalEightSeparatedActors
open NormalEightSeparatedConjugateRigidity

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conj_subtype (S : Subgroup G) (B : Subgroup S) (s : S) :
    (B.map (MulAut.conj s).toMonoidHom).map S.subtype =
      (B.map S.subtype).map (MulAut.conj (s : G)).toMonoidHom := by
  rw [map_map, map_map]
  rfl

omit [Finite G] in
private theorem conj_map_comp (W : Subgroup G) (g k : G) :
    (W.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      W.map (MulAut.conj (k * g)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Local omega control supplies a fixed-point-free actor for a disjoint
commuting returning four. The other recognition hypotheses of the final
consumer are not needed once these local inputs have been established. -/
public theorem exists_oneSidedActor
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) [(fourImage S W).Normal]
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z) (hfactor : CentralizerFactorization S W)
    (hcontrol : LocalCentralizerControl S W) (g : G)
    (hreturn : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hdisjoint : Disjoint (W.map (S : Subgroup G).subtype)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom))
    (hcommute : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (W.map (S : Subgroup G).subtype : Set G))
    (hOmega :
      let B :=
        ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom).subgroupOf
          (S : Subgroup G)
      let Y := centralizer ((W ⊔ B : Subgroup S) : Set S)
      (omega₁ Y (p := 2)).map Y.subtype = W ⊔ B) :
    Nonempty (OneSidedActor (W.map (S : Subgroup G).subtype)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom)) := by
  let W₀ := W.map (S : Subgroup G).subtype
  let W₁ := W₀.map (MulAut.conj g).toMonoidHom
  let B := W₁.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 W₁ := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hreturn
  have hBmap : B.map (S : Subgroup G).subtype = W₁ := map_subgroupOf_eq_of_le hreturn
  have hB4 : Nat.card B = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hreturn).toEquiv,
      card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (S : Subgroup G).subtype_injective, hW]
  have hBW : B ≤ centralizer (W : Set S) := by
    intro b hb w hw
    apply Subtype.ext
    exact hcommute hb w (mem_map_of_mem _ hw)
  have hdWB : Disjoint W B := by
    apply disjoint_def.mpr
    intro x hxW hxB
    exact Subtype.ext (disjoint_def.mp hdisjoint (mem_map_of_mem _ hxW) hxB)
  have hlarge : 8 ≤ Nat.card (W ⊔ B : Subgroup S) := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint W B
      (hBW.trans (Subgroup.centralizer_le_normalizer _)) hdWB, hW, hB4]
    decide
  obtain ⟨s, hsN, hsC, hsnot⟩ :=
    exists_conjugate_normalizing_sup_not_centralizing S.isPGroup' hno W B hBW hlarge hOmega
  let V := B.map (MulAut.conj s).toMonoidHom
  let V₀ := V.map (S : Subgroup G).subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hVmap : V₀ = W₀.map (MulAut.conj ((s : G) * g)).toMonoidHom := by
    change (B.map (MulAut.conj s).toMonoidHom).map (S : Subgroup G).subtype = _
    rw [map_conj_subtype, hBmap, conj_map_comp]
  have hWs : W.map (MulAut.conj s).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (W.normalizer_eq_top ▸ mem_top s)
  have hdWV : Disjoint W V := by
    have he := congrArg (Subgroup.map (MulAut.conj s).toMonoidHom) (disjoint_iff.mp hdWB)
    rw [map_inf _ _ _ (MulAut.conj s).injective, hWs, Subgroup.map_bot] at he
    exact disjoint_iff.mpr he
  have hpairP : IsPGroup 2 (W₁ ⊔ V₀ : Subgroup G) := by
    have hle : W₁ ⊔ V₀ ≤ (S : Subgroup G) := sup_le hreturn (map_subtype_le V)
    exact S.isPGroup'.of_injective (inclusion hle) (inclusion_injective hle)
  have hlocal : ∀ v ∈ V, ∀ b ∈ B, b ≠ 1 → Commute v b →
      v ∈ normalizer (B : Set S) := by
    intro v _ b hb hb1 hcomm
    let R := W₁ ⊔ zpowers (v : G)
    have hRS : R ≤ (S : Subgroup G) := sup_le hreturn (zpowers_le.mpr v.property)
    have hp : IsPGroup 2 R :=
      S.isPGroup'.of_injective (inclusion hRS) (inclusion_injective hRS)
    have hRC : R ≤ centralizer ({(b : G)} : Set G) := by
      apply sup_le
      · intro w hw
        exact mem_centralizer_singleton_iff.mpr (W₁.le_centralizer hw b hb).symm
      · exact zpowers_le.mpr
          (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm.eq))
    have hn := conjugate_normalized_by_centralizing_two_overgroup S hno hZ W hW hunique
      hcontrol g R hp le_sup_left (b : G) hb
      (fun he => hb1 (Subtype.ext he)) hRC
    have hvN := hn ((le_sup_right : zpowers (v : G) ≤ R) (mem_zpowers (v : G)))
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp hvN (a : G)
  have hnormcomm : V ≤ normalizer (B : Set S) → V ≤ centralizer (B : Set S) := by
    intro hn
    have hnG : V₀ ≤ normalizer (W₁ : Set G) := by
      have hh := (map_mono hn).trans (le_normalizer_map (S : Subgroup G).subtype)
      rwa [hBmap] at hh
    have hc : V₀ ≤ centralizer (W₁ : Set G) := by
      rw [hVmap] at hpairP hnG ⊢
      exact conjugate_le_centralizer_of_le_normalizer S hno hZ W hW hunique
        z hzW hzC hz hsep hcontrol g ((s : G) * g) hpairP hnG
    intro v hv b hb
    exact Subtype.ext (hc (mem_map_of_mem _ hv) b hb)
  have hrigid : ∀ u ∈ V, B.map (MulAut.conj u).toMonoidHom ≠ B →
      Disjoint B (B.map (MulAut.conj u).toMonoidHom) := by
    intro u _ hne
    have hmap : (B.map (MulAut.conj u).toMonoidHom).map (S : Subgroup G).subtype =
        W₀.map (MulAut.conj ((u : G) * g)).toMonoidHom := by
      rw [map_conj_subtype, hBmap, conj_map_comp]
    have hret : W₀.map (MulAut.conj ((u : G) * g)).toMonoidHom ≤ (S : Subgroup G) :=
      hmap ▸ map_subtype_le _
    have hp : IsPGroup 2
        (W₁ ⊔ W₀.map (MulAut.conj ((u : G) * g)).toMonoidHom : Subgroup G) := by
      have hle := sup_le hreturn hret
      exact S.isPGroup'.of_injective (inclusion hle) (inclusion_injective hle)
    have hneG : W₀.map (MulAut.conj ((u : G) * g)).toMonoidHom ≠ W₁ := by
      intro he
      apply hne
      exact map_injective (S : Subgroup G).subtype_injective (hmap.trans (he.trans hBmap.symm))
    have hdG := disjoint_conjugates_of_isPGroup_sup S hno hZ W hW hunique
      z hzW hzC hz hsep hfactor hcontrol g ((u : G) * g) hp hneG
    apply disjoint_def.mpr
    intro x hxB hxC
    exact Subtype.ext (disjoint_def.mp hdG hxB (hmap ▸ mem_map_of_mem _ hxC))
  have hcross := cross_action_of_moving_elementary W B V hBW hsN hsC hdWV hsnot
    hOmega hlocal hnormcomm hrigid
  refine ⟨{
    V := V₀
    elementary := IsElementaryAbelian.map _
    card := (card_map_of_injective (S : Subgroup G).subtype_injective).trans
      ((card_map_of_injective (MulAut.conj s).injective).trans hB4)
    normalizes := ?_
    centralizes := ?_
    cross := ?_ }⟩
  · have hn := (map_mono hsN).trans (le_normalizer_map (S : Subgroup G).subtype)
    rwa [Subgroup.map_sup, hBmap] at hn
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (hsC hv w hw)
  · rintro _ ⟨v, hv, rfl⟩ hv1 b hb hb1 hc
    apply hcross v hv (fun he => hv1 (congrArg Subtype.val he))
      (⟨b, hreturn hb⟩ : S) hb (fun he => hb1 (congrArg Subtype.val he))
    exact Subtype.ext hc.eq

end Stellmacher.Recognition.NormalEightSeparatedMovingActor
