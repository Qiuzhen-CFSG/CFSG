module

public import Stellmacher.Recognition.NormalEightSeparatedTransport

/-!
# Transport and assembly of separated normalizer actors

A one-sided actor centralizes one four and acts without nonidentity fixed
points on the other. Conjugate the elementary sixteen into the original
Sylow, carrying the second four's central involution to the original central
involution. Normality of the actual odd-core quotient image identifies the
transported second four with the first. Thus a one-sided construction for
returning pairs supplies both actors of the cross-action configuration.

The one-sided normalizer growth remains an explicit premise of the assembly
theorem. No fusion assertion or bound on arbitrary elementary subgroups is
assumed by the transport argument.

Source: Janko–Thompson, Math. Z. 113 (1970), first half of printed p.395,
referring to Lemma 5.1 on printed p.394.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedActors

open Subgroup NormalFourCentralOmegaTwo NormalEightSeparatedFusion
open NormalEightSeparatedTransport

variable {G : Type*} [Group G]

/-- One side of the cross-action configuration. -/
public structure OneSidedActor (W B : Subgroup G) where
  V : Subgroup G
  elementary : IsElementaryAbelian 2 V
  card : Nat.card V = 4
  normalizes : V ≤ normalizer ((W ⊔ B : Subgroup G) : Set G)
  centralizes : V ≤ centralizer (W : Set G)
  cross : ∀ v ∈ V, v ≠ 1 → ∀ b ∈ B, b ≠ 1 → ¬ Commute v b

/-- Actors transport under group isomorphisms. -/
public def OneSidedActor.map {H : Type*} [Group H] {W B : Subgroup G}
    (a : OneSidedActor W B) (f : G ≃* H) :
    OneSidedActor (W.map f.toMonoidHom) (B.map f.toMonoidHom) where
  V := a.V.map f.toMonoidHom
  elementary := by
    let := a.elementary
    exact IsElementaryAbelian.map _
  card := (card_map_of_injective f.injective).trans a.card
  normalizes := by
    have hn := (map_mono a.normalizes).trans (le_normalizer_map f.toMonoidHom)
    rwa [Subgroup.map_sup] at hn
  centralizes := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg f (a.centralizes hv w hw)
  cross := by
    rintro _ ⟨v, hv, rfl⟩ hv1 _ ⟨b, hb, rfl⟩ hb1 hc
    exact a.cross v hv (fun h => hv1 (h ▸ f.map_one)) b hb
      (fun h => hb1 (h ▸ f.map_one))
      (show Commute v b from f.injective (by
        simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hc.eq))

variable [Finite G]

/-- Switch the two fours by transporting their elementary join. The second
four becomes the original normal four, and the first becomes a returning
conjugate. Only central-omega transport is needed. -/
public theorem exists_switching_conjugator
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (g : G)
    (hcommute : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (W.map (S : Subgroup G).subtype : Set G)) :
    ∃ k : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj k).toMonoidHom ≤
        (S : Subgroup G) ∧
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj k).toMonoidHom = W.map (S : Subgroup G).subtype := by
  let W₀ := W.map (S : Subgroup G).subtype
  let B := W₀.map (MulAut.conj g).toMonoidHom
  let E := W₀ ⊔ B
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer hcommute
  let x : G := (MulAut.conj g) (z : G)
  have hxB : x ∈ B := mem_map_of_mem _ (mem_map_of_mem _ hzW)
  have hxE : x ∈ E := (le_sup_right : B ≤ E) hxB
  have hEC : E ≤ centralizer ({x} : Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr (E.le_centralizer he x hxE).symm
  obtain ⟨k, hkS, hkx⟩ := S.transport_centralizing_two_subgroup z hzC x
    (isConj_iff.mpr ⟨g, rfl⟩).symm E (IsElementaryAbelian.isPGroup 2 E) hEC
  have hBkS : B.map (MulAut.conj k).toMonoidHom ≤ (S : Subgroup G) :=
    (map_mono (show B ≤ E from le_sup_right)).trans hkS
  have hcomp : B.map (MulAut.conj k).toMonoidHom =
      W₀.map (MulAut.conj (k * g)).toMonoidHom := by
    dsimp [B]
    rw [map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨k, (map_mono (show W₀ ≤ E from le_sup_left)).trans hkS, ?_⟩
  rw [hcomp]
  apply conjugate_four_eq_of_mem_central_involution S hno hZ W hW hunique
    (k * g) (hcomp ▸ hBkS) z hzC hz
  rw [← hcomp, ← hkx]
  exact mem_map_of_mem _ hxB

/-- A one-sided actor construction for every returning pair suffices for the
full cross-action configuration. Final normalizer growth must discharge
`hactor`; the symmetric construction is proved here. -/
public theorem crossAction_of_one_sided_actors
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hactor : ∀ k : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj k).toMonoidHom ≤
        (S : Subgroup G) →
      Disjoint (W.map (S : Subgroup G).subtype)
        ((W.map (S : Subgroup G).subtype).map (MulAut.conj k).toMonoidHom) →
      (W.map (S : Subgroup G).subtype).map (MulAut.conj k).toMonoidHom ≤
        centralizer (W.map (S : Subgroup G).subtype : Set G) →
      Nonempty (OneSidedActor (W.map (S : Subgroup G).subtype)
        ((W.map (S : Subgroup G).subtype).map (MulAut.conj k).toMonoidHom)))
    (g : G)
    (hreturn : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hdisjoint : Disjoint (W.map (S : Subgroup G).subtype)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom))
    (hcommute : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (W.map (S : Subgroup G).subtype : Set G)) :
    Nonempty (CrossAction (W.map (S : Subgroup G).subtype)) := by
  let W₀ := W.map (S : Subgroup G).subtype
  let B := W₀.map (MulAut.conj g).toMonoidHom
  obtain ⟨a⟩ := hactor g hreturn hdisjoint hcommute
  obtain ⟨k, hkS, hkB⟩ :=
    exists_switching_conjugator S hno hZ W hW hunique z hzW hzC hz g hcommute
  let f := MulAut.conj k
  change B.map f.toMonoidHom = W₀ at hkB
  have hd : Disjoint W₀ (W₀.map f.toMonoidHom) := by
    apply disjoint_iff.mpr
    have he := congrArg (Subgroup.map f.toMonoidHom) (disjoint_iff.mp hdisjoint)
    change (W₀ ⊓ B).map f.toMonoidHom = (⊥ : Subgroup G).map f.toMonoidHom at he
    rw [map_inf _ _ _ f.injective, Subgroup.map_bot, hkB] at he
    simpa only [inf_comm] using he
  have hc : W₀.map f.toMonoidHom ≤ centralizer (W₀ : Set G) := by
    conv_rhs => rw [← hkB]
    rintro _ ⟨w, hw, rfl⟩ _ ⟨b, hb, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg f (hcommute hb w hw).symm
  obtain ⟨b⟩ := hactor k hkS hd hc
  have hbackW : W₀.map f.symm.toMonoidHom = B := by
    apply map_injective (f := f.toMonoidHom) f.injective
    rw [map_map]
    have he : f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id G := by
      ext x
      exact f.apply_symm_apply x
    rw [he, map_id, hkB]
  have hbackB : (W₀.map f.toMonoidHom).map f.symm.toMonoidHom = W₀ := by
    rw [map_map]
    have he : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id G := by
      ext x
      exact f.symm_apply_apply x
    rw [he, map_id]
  have hb : Nonempty (OneSidedActor B W₀) := by
    have hb := b.map f.symm
    change OneSidedActor (W₀.map f.symm.toMonoidHom)
      ((W₀.map f.toMonoidHom).map f.symm.toMonoidHom) at hb
    rw [hbackW, hbackB] at hb
    exact ⟨hb⟩
  obtain ⟨b⟩ := hb
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map_subtype
  refine ⟨{
    V := a.V
    V₁ := b.V
    W₁ := B
    elementaryV := a.elementary
    elementaryV₁ := b.elementary
    elementaryW₁ := IsElementaryAbelian.map _
    cardV := a.card
    cardV₁ := b.card
    cardW₁ := (card_map_of_injective (MulAut.conj g).injective).trans
      ((card_map_of_injective (S : Subgroup G).subtype_injective).trans hW)
    normalizes := sup_le a.normalizes ?_
    centralizes := a.centralizes
    centralizes₁ := b.centralizes
    commute := le_centralizer_iff.mp hcommute
    disjoint := disjoint_iff.mp hdisjoint
    cross := a.cross
    cross₁ := b.cross }⟩
  simpa only [sup_comm] using b.normalizes

end Stellmacher.Recognition.NormalEightSeparatedActors
