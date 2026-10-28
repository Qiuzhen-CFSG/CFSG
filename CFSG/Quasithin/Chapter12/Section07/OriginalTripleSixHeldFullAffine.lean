module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldEvenExclusion

/-!
# The full marked affine normalizer at an original escaping point

The excluded even branch decides the original actor alternative. The
result retains the original module coordinates, the prescribed component
action, and the actual scalar complement, and determines the original
ambient Sylow order.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_full_affine_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    let M := normalizer (K : Set G)
    Nat.card T=1024 ∧ ∃ Y : Subgroup M, Nat.card Y=3 ∧
      Y.map M.subtype≤tripleSixScalarResidual K ∧
      ∃ E : M≃*Multiplicative hexacode ⋊[hexAffineAction] HexAutomorphisms,
        (∀ u : U, E (inclusion (D.le_component.trans K.le_normalizer) u)=
          SemidirectProduct.inl (tripleSixPointCoordinates D a u)) ∧
        (∀ k : K, (E (inclusion K.le_normalizer k)).right=
          (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
        (normalizer (Y : Set M)).map E.toMonoidHom=
          (SemidirectProduct.inr : HexAutomorphisms→*
            Multiplicative hexacode ⋊[hexAffineAction] HexAutomorphisms).range := by
  let M := normalizer (K : Set G)
  obtain ⟨R,hR,Y,hY,hYX,E,hU,hK,hN⟩ :=
    original_tripleSix_escaping_affine_model h structural D a t ht heven hout
  have hcore := original_tripleSix_escaping_core h structural D a t ht heven hout
  have hTM : (T : Subgroup G)≤M := by
    rw [show M=normalizer (K : Set G) from rfl,hcore.2.2.2.2.2]
    exact le_sup_right
  have hRc : R=⊤ := by
    rcases hR with hR | hR
    · subst R
      have hMc : Nat.card M=69120 := by
        rw [Nat.card_congr E.toEquiv,SemidirectProduct.card,
          Nat.card_congr (Multiplicative.toAdd : Multiplicative hexacode≃hexacode),
          hexacode_card,hexEven_card]
      have hUc : Nat.card U=64 :=
        (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card
      have hOc : Nat.card (pCore 2 K)=64 := by
        have hh := congrArg (fun A : Subgroup G => Nat.card A) hcore.1
        rw [pCoreIn,card_map_of_injective K.subtype_injective,hUc] at hh
        exact hh
      have hQc : Nat.card (K ⧸ pCore 2 K)=1080 :=
        (Nat.card_congr a.groupEquiv.toEquiv).trans hexEven_card
      have hKc : Nat.card K=69120 := by
        rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K),hQc,hOc]
      have hKM : K=M := eq_of_le_of_card_ge K.le_normalizer (by rw [hMc,hKc])
      exact (original_tripleSix_escaping_sylow_not_le_component h structural D a t ht heven hout
        (hTM.trans_eq hKM.symm)).elim
    · exact hR
  subst R
  let eA := SemidirectProduct.congr (MulEquiv.refl (Multiplicative hexacode))
    (Subgroup.topEquiv : (⊤ : Subgroup HexAutomorphisms)≃*HexAutomorphisms)
    (fun _ => rfl) (φ₁ := hexAffineAction.comp (⊤ : Subgroup HexAutomorphisms).subtype)
      (φ₂ := hexAffineAction)
  let E' := E.trans eA
  have hMc : Nat.card M=138240 := by
    rw [Nat.card_congr E'.toEquiv,SemidirectProduct.card,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative hexacode≃hexacode),
      hexacode_card,hexAutomorphisms_card]
  have hTc : Nat.card T=1024 := by
    have hh := (T.subtype hTM).card_eq_multiplicity
    change Nat.card ((T : Subgroup G).subgroupOf M)=2^(Nat.card M).factorization 2 at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv,hMc] at hh
    exact hh.trans (by decide +kernel)
  refine ⟨hTc,Y,hY,hYX,E',?_,?_,?_⟩
  · intro u
    change eA (E (inclusion (D.le_component.trans K.le_normalizer) u))=_
    rw [hU]
    rfl
  · exact hK
  · change (normalizer (Y : Set M)).map (eA.toMonoidHom.comp E.toMonoidHom)=_
    rw [←Subgroup.map_map,hN]
    apply le_antisymm
    · rintro x ⟨y,⟨r,rfl⟩,rfl⟩
      exact ⟨r.val,rfl⟩
    · rintro x ⟨r,rfl⟩
      exact ⟨SemidirectProduct.inr (⟨r,mem_top _⟩ : (⊤ : Subgroup HexAutomorphisms)),
        ⟨⟨r,mem_top _⟩,rfl⟩,rfl⟩

end CFSG.Quasithin.Chapter12.Section07
