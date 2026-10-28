module

public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.MinimalTransport
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.GroupTheory.SylowQuotientPreimage
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SylowNormalSupplementIntersection
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The residual--tau reduction for reverse quotient lifting

For an E-member `I`, the subgroup `O²(I)τ(I,T ∩ I,A)` contains the ambient
tau and has the same embedded two-residual as `I`. The prescribed Sylow
intersection is Sylow in this subgroup. These properties lift to its full
preimage under the literal quotient map, giving the source group `G₁`.

We also construct a genuine minimal supplement over `O²(G)Y`; its quotient
image is the whole quotient. This supplies the source minimality argument
without assuming a supplement certificate. These reduction results do not
yet assert the odd-prime or component E-membership of the final lift.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
proof of E.1.10(7), printed pp.211--212.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The source subgroup `O²(I)τ(I,T ∩ I,A)`, embedded in the ambient group. -/
def residualTau (T A I : Subgroup G) : Subgroup G :=
  (pResidual 2 I ⊔ tau (T.subgroupOf I) (A.subgroupOf I)).map I.subtype

omit [Finite G] in
/-- The residual--tau subgroup lies inside the original member. -/
theorem residualTau_le (T A I : Subgroup G) : residualTau T A I ≤ I :=
  map_subtype_le _

/-- The smaller source subgroup still contains the ambient tau. -/
theorem IsEMember.tau_le_residualTau {T A I : Subgroup G}
    (h : IsEMember T A I) : tau T A ≤ residualTau T A I := by
  exact (tau_le_map_tau T A I (h.2.2.2.1.trans inf_le_right)).trans
    (map_mono le_sup_right)

/-- Shrinking to the residual--tau subgroup preserves the intrinsic residual after embedding. -/
theorem IsEMember.residualTau_residual {T A I : Subgroup G}
    (h : IsEMember T A I) :
    (pResidual 2 (residualTau T A I)).map (residualTau T A I).subtype =
      (pResidual 2 I).map I.subtype := by
  let D := tau (T.subgroupOf I) (A.subgroupOf I)
  obtain ⟨S, hS⟩ := h.2.2.2.2.1
  have hD : IsPGroup 2 D := S.isPGroup'.to_le (hS.symm ▸ tau_le _ _)
  have he := embedded_pResidual_join_pGroup (pResidual 2 I) D
    (isPPerfect_pResidual 2) hD le_normalizer_of_normal
  have hm := congrArg (Subgroup.map I.subtype) he
  rw [map_embedded_pResidual] at hm
  exact hm

/-- The prescribed Sylow restricts to a Sylow of the residual--tau subgroup. -/
theorem IsEMember.residualTau_sylow {T A I : Subgroup G}
    (h : IsEMember T A I) :
    ∃ S : Sylow 2 (residualTau T A I),
      (S : Subgroup (residualTau T A I)) = T.subgroupOf (residualTau T A I) := by
  let L := pResidual 2 I ⊔ tau (T.subgroupOf I) (A.subgroupOf I)
  obtain ⟨P, hP⟩ := h.2.2.2.2.1
  obtain ⟨Q, hQ⟩ := P.exists_map_eq_inf_of_normal_supplement (pResidual 2 I) L
    (pResidual_sup_sylow_eq_top P) le_sup_left
  have hQ' : (Q : Subgroup L) = (T.subgroupOf I).subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hQ, subgroupOf_map_subtype, hP]
  let e := L.equivMapOfInjective I.subtype I.subtype_injective
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (Q : Subgroup L).map e.toMonoidHom = _
  rw [hQ', intrinsic_subgroupOf_map, subgroupOf_map_subtype]
  ext x
  change ((x : G) ∈ T ∧ (x : G) ∈ I) ↔ (x : G) ∈ T
  exact ⟨And.left, fun hx => ⟨hx, residualTau_le T A I x.property⟩⟩

/-- An E-member in the quotient supplies the actual Sylow intersection in its full preimage. -/
theorem IsEMemberAt.quotient_preimage {i : ℕ} (T : Sylow 2 G)
    (A Y : Subgroup G) [Y.Normal] {I : Subgroup (G ⧸ Y)}
    (hI : IsEMemberAt i ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I) :
    tau (T : Subgroup G) A ≤ I.comap (QuotientGroup.mk' Y) ∧
      A ≤ I.comap (QuotientGroup.mk' Y) ∧
      ∃ S : Sylow 2 (I.comap (QuotientGroup.mk' Y)),
        (S : Subgroup (I.comap (QuotientGroup.mk' Y))) =
          (T : Subgroup G).subgroupOf (I.comap (QuotientGroup.mk' Y)) := by
  refine ⟨?_, map_le_iff_le_comap.mp hI.1.2.2.1, ?_⟩
  · exact map_le_iff_le_comap.mp
      ((map_tau_le_of_surjective (QuotientGroup.mk' Y)
        (QuotientGroup.mk'_surjective Y) _ _).trans
          (hI.1.2.2.2.1.trans inf_le_right))
  · obtain ⟨P, hP⟩ := hI.1.2.2.2.2.1
    exact T.exists_subgroupOf_eq_comap (QuotientGroup.mk' Y) I P hP

/-- The source group `G₁` contains the ambient tau. -/
theorem IsEMemberAt.tau_le_residualTau_preimage {i : ℕ} (T : Sylow 2 G)
    (A Y : Subgroup G) [Y.Normal] {I : Subgroup (G ⧸ Y)}
    (hI : IsEMemberAt i ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I) :
    tau (T : Subgroup G) A ≤
      (residualTau ((T : Subgroup G).map (QuotientGroup.mk' Y))
        (A.map (QuotientGroup.mk' Y)) I).comap (QuotientGroup.mk' Y) :=
  map_le_iff_le_comap.mp
    ((map_tau_le_of_surjective (QuotientGroup.mk' Y)
      (QuotientGroup.mk'_surjective Y) _ _).trans hI.1.tau_le_residualTau)

/-- The full preimage of the residual--tau subgroup has the required tau, actor and Sylow arrangement. -/
theorem IsEMemberAt.residualTau_preimage {i : ℕ} (T : Sylow 2 G)
    (A Y : Subgroup G) [Y.Normal] [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) {I : Subgroup (G ⧸ Y)}
    (hI : IsEMemberAt i ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I) :
    let H := (residualTau ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I).comap (QuotientGroup.mk' Y)
    tau (T : Subgroup G) A ≤ H ∧ A ≤ H ∧
      ∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H := by
  dsimp only
  have ht := hI.tau_le_residualTau_preimage T A Y
  refine ⟨ht, (le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans ht, ?_⟩
  obtain ⟨P, hP⟩ := hI.1.residualTau_sylow
  exact T.exists_subgroupOf_eq_comap (QuotientGroup.mk' Y) _ P hP

/-- Construct the minimal supplement over `O²(G)Y` used in the source, with full quotient image. -/
theorem exists_minimalResidualSupplement (T : Sylow 2 G) (Y : Subgroup G) [Y.Normal] :
    ∃ K : Subgroup G,
      IsMinimalSupplement (T : Subgroup G) (pResidual 2 G ⊔ Y) Y K ∧
        K.map (QuotientGroup.mk' Y) = ⊤ := by
  obtain ⟨K, hK⟩ := exists_minimalSupplement (T : Subgroup G) (pResidual 2 G ⊔ Y) Y
    le_sup_right
  refine ⟨K, hK, ?_⟩
  have htop : (pResidual 2 G ⊔ Y) ⊔ (T : Subgroup G) = ⊤ := by
    rw [sup_right_comm, pResidual_sup_sylow_eq_top, top_sup_eq]
  have hm := congrArg (Subgroup.map (QuotientGroup.mk' Y)) hK.1.2.2
  simpa only [htop, Subgroup.map_sup, QuotientGroup.map_mk'_self,
    sup_bot_eq, map_top_of_surjective _ (QuotientGroup.mk'_surjective Y)] using hm

end CFSG.Quasithin.ChapterE
