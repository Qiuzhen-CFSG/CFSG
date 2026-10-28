module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsCenter
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsReturn
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalJankoFour

/-!
# Returning the original paired HS involution to the moved module

The entire covering center lies in the original common prime-to-three
residual. Its invariance under the actual exchanging element returns the
second central involution to the original component. The full-preimage
and native rank argument then returns it to the original moved module.
No center of a model residual is substituted for the original residual.

Source: the quasisimple inspection in 12.6.12, pp.825–826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- An escaping original nonsingular centralizer supplies the paired involution
inside the unchanged moved module and the center of the same local Sylow.
The actual HS double-cover equivalence and its projection remain marked. -/
theorem SourceHypothesis.exists_original_hs_returned_pair
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ u : V, D.Nonsingular u ∧ IsQuasisimple (Kv (u : G)) ∧
      ∃ hp : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier,
        letI := hp
        ∃ (e : ((Kv (u : G)) ⧸ center (Kv (u : G))) ≃*
            Sporadic.LeechRelated.HS.Carrier)
          (f : Kv (u : G) ≃* Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover),
          (∀ x, Theory.SpecificGroups.J2HSMultipliers.HS.projection (f x) =
            e (QuotientGroup.mk' (center (Kv (u : G))) x)) ∧
          ∃ S : Sylow 2 (Gv (u : G)),
            let S₀ := (S : Subgroup (Gv (u : G))).map (Gv (u : G)).subtype
            ∃ w : G, w ≠ (u : G) ∧ w ^ 2 = 1 ∧
              w ∈ Vv L V (u : G) ∧ w ∈ (center S₀).map S₀.subtype ∧
              w ∉ centralizer (Kv (u : G) : Set G) := by
  obtain ⟨_,_,u,hu,_,_,hi,_,hnot,_,_,_,hK,hmodels,
    S,hTS,_,_,_,hmodel⟩ :=
    H.exists_preferred_nonsingular_hs_common_residual D hTV hTI v hv he
  change (∃ hp : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier,
    letI := hp
    ∃ (e : ((Kv (u : G)) ⧸ center (Kv (u : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
      (f : Kv (u : G) ≃* Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover),
      ∀ x, Theory.SpecificGroups.J2HSMultipliers.HS.projection (f x) =
        e (QuotientGroup.mk' (center (Kv (u : G))) x)) ∨
    Nonempty (((Kv (u : G)) ⧸ center (Kv (u : G))) ≃* Janko4.Model) at hmodels
  rcases hmodels with ⟨hp,e,f,hf⟩ | ⟨e⟩
  · let := hp
    obtain ⟨_,_,s,_,_,_,_,_,
      P,hSP,_,_,_,t,ht,_,hwne,_,hwS,hwQ,hzP,hzQ,_,hz2,
      _,_,_,_,_,hwnot,hznot,_,
      j,_,_,_,_,_,_,_,_,_,_,_,_,
      _,_,_,_,_,_,_,_,_,hJC,_,hJt⟩ := hmodel e
    let S₀ := (S : Subgroup (Gv (u : G))).map (Gv (u : G)).subtype
    let w := (MulAut.conj t) (u : G)
    let z := (u : G) * w
    let B := Gv (u : G) ⊓ Gv z
    let J := (primeToResidual 3 B).map B.subtype
    have hzS : z ∈ (center S₀).map S₀.subtype := by
      rw [map_center_subtype_eq_inf_centralizer] at hzP ⊢
      exact ⟨hTS hzQ.1,fun x hx => hzP.2 x (hSP hx)⟩
    have hZJ := H.nonsingular_hs_center_le_common_residual D u hu hK e S z hzS hz2 hznot
    have hcenter := (H.nonsingular_hs_original_geometry D u hu hK hTV hnot e).2.2.2
    have huJ : (u : G) ∈ J := hZJ (hcenter.symm ▸ mem_zpowers (u : G))
    change J.map (MulAut.conj t).toMonoidHom = J at hJt
    have hwJ : w ∈ J := hJt ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom huJ
    have hwC : w ∈ Kv (u : G) := (hJC hwJ).1
    have hw2 : w ^ 2 = 1 := by
      change (MulAut.conj t) (u : G) ^ 2 = 1
      rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian (u : G) u.property,map_one]
    have hwW := H.nonsingular_hs_core_involution_mem_moved D u hu hK e w hwC hwQ.2 hw2
    exact ⟨u,hu,hK,hp,e,f,hf,S,w,hwne,hw2,hwW,hwS,hwnot⟩
  · obtain ⟨e⟩ := e
    exact (H.original_nonsingular_not_jankoFour D u hu hK hTV hi e).elim

end CFSG.Quasithin.Chapter12.Section06
