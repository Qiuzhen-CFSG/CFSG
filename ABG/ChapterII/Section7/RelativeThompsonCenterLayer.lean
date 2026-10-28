module

public import ABG.ChapterII.Section6.Defs
public import Glauberman.Theorem4_2

/-!
# The relative Thompson center lies in the p-prime-p layer

For a finite p-constrained group and an actual subgroup P satisfying ABG
relative p-stability, the center of J(P) lies in O_{p',p}(G). No Sylow
assumption on P or ordinary ambient stability is required. This is the
containment step of Alperin--Brauer--Gorenstein II.7, Theorem 2, article
p. 62 / PDF p. 63 (`refs/latex/alperin-brauer-gorenstein-pages/page-063.tex`),
which refers to the normal-abelian-subgroup argument of Gorenstein 8.1.3.
The ordinary argument is formalized in `FeitThompson.Gorenstein.Chapter8_2`.

Put M = O_{p'}(G), L = O_{p',p}(G), Q = P intersect L, and A = Z(J(P)).
The stipulated Sylow intersection maps onto O_p(G/M), giving MQ = L.
Constraint therefore bounds C_G(Q) by L. Normalizer functoriality of J and
its center, supplied by Glauberman's public API, gives [Q,A,A] = 1. If Q
is trivial, constraint itself gives L = G. Otherwise the actual relative
stability clause puts the image of A in O_p(N_G(Q)/C_G(Q)). Coprime
normalizer lifting makes N_G(Q) map onto G/M, and the centralizer bound
then defines a surjection from its action quotient onto (G/M)/O_p(G/M).
The latter has trivial p-core, so the image of A vanishes there. This
proves the required containment for the relative ZJ factorization assembly.
-/

open scoped commutatorElement

namespace ABG

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem intersection_map_core (P : Subgroup G)
    (heligible : RelativeStabilityEligible p P) :
    (P ⊓ Op_p'p p G).map (QuotientGroup.mk' (pPrimeCore p G)) =
      pCore p (G ⧸ pPrimeCore p G) := by
  let M := pPrimeCore p G
  let L := Op_p'p p G
  let quotient := QuotientGroup.mk' M
  let core := pCore p (G ⧸ M)
  have hLmap : L.map quotient = core :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) core
  let restricted : L →* core :=
    (quotient.comp L.subtype).codRestrict core (fun element => element.property)
  have hrestricted : Function.Surjective restricted := by
    intro element
    have hmem : element.val ∈ L.map quotient := hLmap.symm ▸ element.property
    obtain ⟨preimage, hpreimage, heq⟩ := hmem
    exact ⟨⟨preimage, hpreimage⟩, Subtype.ext heq⟩
  obtain ⟨S, hS⟩ := heligible.2.1
  have htop : ((S.mapSurjective hrestricted) : Subgroup core) = ⊤ := by
    apply top_unique
    exact ((pCore_isPGroup (G := G ⧸ M) (p := p)).to_subgroup ⊤).le_sylow_of_normal _
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_right).trans_eq hLmap
  · intro element helement
    have hmem : (⟨element, helement⟩ : core) ∈ (S : Subgroup L).map restricted := by
      change (⟨element, helement⟩ : core) ∈ (S.mapSurjective hrestricted : Subgroup core)
      rw [htop]
      trivial
    obtain ⟨preimage, hpreimage, heq⟩ := hmem
    refine ⟨preimage.val, ⟨?_, preimage.property⟩, congrArg Subtype.val heq⟩
    have : preimage ∈ P.subgroupOf L := hS ▸ hpreimage
    exact this

public theorem relative_thompsonCenter_le_pPrimePCore
    (P : Subgroup G) (hconstrained : PConstrainedGroup (G := G) p)
    (hstable : RelativePStable p P) : thompsonCenter P ≤ Op_p'p p G := by
  classical
  obtain ⟨_, _, heligible, hstable⟩ := hstable
  let M := pPrimeCore p G
  let L := Op_p'p p G
  let Q := P ⊓ L
  let A := thompsonCenter P
  let quotient := QuotientGroup.mk' M
  have hQp : IsPGroup p Q := heligible.1.to_inf_left
  have hQmap : Q.map quotient = pCore p (G ⧸ M) := intersection_map_core P heligible
  have hMQ : M ⊔ Q = L := by
    have heq := congrArg (Subgroup.comap quotient) hQmap
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at heq
    exact (sup_comm M Q).trans heq
  have hMQnormal : (M ⊔ Q).Normal := hMQ ▸ inferInstance
  have hAleP : A ≤ P := by
    apply inf_le_left.trans
    apply sSup_le
    intro subgroup hsubgroup
    exact hsubgroup.1
  have hPNQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    relative_subgroup_normalized P Q heligible.1 inf_le_left hMQnormal
  have hPNA : P ≤ Subgroup.normalizer (A : Set G) :=
    P.le_normalizer.trans ((Glauberman.normalizer_le_normalizer_of_thompsonSubgroup P).trans
      (Glauberman.normalizer_le_normalizer_of_thompsonCenter P))
  have hQA : ⁅Q, A⁆ ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hPNA)
  have hquadratic : ⁅⁅Q, A⁆, A⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hQA.trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (Glauberman.thompsonCenter_isMulCommutative P)))
  let N := Subgroup.normalizer (Q : Set G)
  let C := Subgroup.centralizer (Q : Set G)
  have hCleL : C ≤ L := hconstrained Q hQp hMQ
  by_cases hQbot : Q = ⊥
  · have htop : (⊤ : Subgroup G) ≤ L := by
      intro element _
      apply hCleL
      change element ∈ Subgroup.centralizer (Q : Set G)
      rw [hQbot]
      intro point hpoint
      have : point = 1 := hpoint
      simp [this]
    exact le_top.trans htop
  have hNmap : N.map quotient = ⊤ := by
    let : Fact (IsPGroup p Q) := ⟨hQp⟩
    rw [← normalizer_map_quotient_eq_map_normalizer (p := p) Q M inferInstance
      (pPrimeCore_coprime_card (G := G) (p := p)), hQmap]
    exact Subgroup.normalizer_eq_top (H := pCore p (G ⧸ M))
  have hquotientN : Function.Surjective (quotient.comp N.subtype) := by
    intro element
    have hmem : element ∈ N.map quotient := by rw [hNmap]; trivial
    obtain ⟨preimage, hpreimage, heq⟩ := hmem
    exact ⟨⟨preimage, hpreimage⟩, heq⟩
  have hstableA : NormalizerActionImage Q A (hAleP.trans hPNQ) ≤
      pCore p (NormalizerAction Q) :=
    hstable Q A hQbot inf_le_left hMQnormal hAleP hquadratic
  let transfer : NormalizerAction Q →* (G ⧸ M) ⧸ pCore p (G ⧸ M) :=
    QuotientGroup.map (C.subgroupOf N) (pCore p (G ⧸ M))
      (quotient.comp N.subtype) (fun element helement => hCleL helement)
  have htransfer : Function.Surjective transfer := by
    intro element
    refine Quotient.inductionOn' element ?_
    intro representative
    obtain ⟨preimage, heq⟩ := hquotientN representative
    refine ⟨QuotientGroup.mk' (C.subgroupOf N) preimage, ?_⟩
    exact congrArg (QuotientGroup.mk' (pCore p (G ⧸ M))) heq
  have hcoremap : (pCore p (NormalizerAction Q)).map transfer ≤
      pCore p ((G ⧸ M) ⧸ pCore p (G ⧸ M)) := by
    exact le_sSup ⟨Subgroup.Normal.map inferInstance transfer htransfer,
      (pCore_isPGroup (G := NormalizerAction Q) (p := p)).map transfer⟩
  have hcorebot : pCore p ((G ⧸ M) ⧸ pCore p (G ⧸ M)) = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup (p := p) (pCore p (G ⧸ M))
      (pCore_isPGroup (G := G ⧸ M) (p := p))]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  intro element helement
  have hnormalizer : element ∈ N := hPNQ (hAleP helement)
  have hmem : QuotientGroup.mk' (C.subgroupOf N) ⟨element, hnormalizer⟩ ∈
      NormalizerActionImage Q A (hAleP.trans hPNQ) :=
    Subgroup.mem_map_of_mem _ helement
  have hzero := hcoremap (Subgroup.mem_map_of_mem transfer (hstableA hmem))
  rw [hcorebot] at hzero
  have heq : transfer (QuotientGroup.mk' (C.subgroupOf N) ⟨element, hnormalizer⟩) = 1 := hzero
  exact (QuotientGroup.eq_one_iff (N := pCore p (G ⧸ M)) (quotient element)).mp heq

end ABG
