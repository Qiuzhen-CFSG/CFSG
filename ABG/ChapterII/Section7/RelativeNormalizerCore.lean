module

public import ABG.ChapterII.Section6.Defs

/-!
# The normalizer-core reduction for relative stability

Let P be a subgroup satisfying either alternative of ABG relative-stability
eligibility, and let W be a subgroup invariant under the normalizer of P.
If L is the normal core of the normalizer of W, then the p-core of G/L is
trivial. This is the K = L step of Alperin--Brauer--Gorenstein, II.7,
Theorem 2 (article pp. 61--62, PDF pp. 62--63; local transcription
`refs/latex/alperin-brauer-gorenstein-pages/page-063.tex`). Its intended
application takes W to be the intersection of a normal p-subgroup B with
Z(J(P)).

Write K for the preimage of the p-core of G/L. In the quotient-containment
alternative, K lies in LP. In the other alternative, choose the stipulated
Sylow subgroup S in which P is normal: the p-core of G/L lies in the image
of S, so K lies in LS, and S normalizes P. Thus K normalizes W in both
cases. Since K is normal in G, it lies in L by the defining maximality of
the normal core. Its quotient image is therefore trivial.

Only the two eligibility alternatives are needed for this reduction; neither
ordinary ambient stability nor a Sylow assumption on P is introduced. The
normal-quotient quantifier is retained through RelativeStabilityAlternatives.
-/

namespace ABG

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

public theorem relative_normalizerCore_quotient_pCore_eq_bot
    (P W : Subgroup G) (hP : RelativeStabilityAlternatives p P)
    (hW : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (W : Set G)) :
    pCore p (G ⧸ (Subgroup.normalizer (W : Set G)).normalCore) = ⊥ := by
  let L := (Subgroup.normalizer (W : Set G)).normalCore
  let quotient := QuotientGroup.mk' L
  let K := (pCore p (G ⧸ L)).comap quotient
  have hL : L ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normalizer (W : Set G)).normalCore_le
  have hK : K ≤ Subgroup.normalizer (W : Set G) := by
    rcases hP with ⟨S, hPS, hnormal⟩ | hquotients
    · have hS : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hPS).mp hnormal).trans hW
      have hcore : pCore p (G ⧸ L) ≤ (S : Subgroup G).map quotient :=
        (pCore_isPGroup (G := G ⧸ L) (p := p)).le_sylow_of_normal
          (S.mapSurjective (f := quotient) (QuotientGroup.mk'_surjective L))
      calc
        K ≤ ((S : Subgroup G).map quotient).comap quotient := Subgroup.comap_mono hcore
        _ = (S : Subgroup G) ⊔ L := by rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
        _ ≤ Subgroup.normalizer (W : Set G) := sup_le hS hL
    · calc
        K ≤ (P.map quotient).comap quotient := Subgroup.comap_mono (hquotients L inferInstance)
        _ = P ⊔ L := by rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
        _ ≤ Subgroup.normalizer (W : Set G) := sup_le (P.le_normalizer.trans hW) hL
  have hKL : K ≤ L := Subgroup.normal_le_normalCore.mpr hK
  have hmap : K.map quotient = pCore p (G ⧸ L) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective L) _
  change pCore p (G ⧸ L) = ⊥
  rw [← hmap]
  apply (Subgroup.map_eq_bot_iff (f := quotient) (H := K)).mpr
  simpa only [quotient, QuotientGroup.ker_mk'] using hKL

end ABG
