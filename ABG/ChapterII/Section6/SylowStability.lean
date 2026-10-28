module
public import ABG.ChapterII.Section6.NormalizerActionTransport
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Relative stability at a Sylow subgroup

For a Sylow p-subgroup R of a finite group H, ABG relative p-stability with
respect to R is equivalent to ordinary ABG p-stability. Both predicates keep
the source's odd-prime and nontrivial-p-core conditions. R is automatically
eligible: its intersection with the normal subgroup O_{p',p}(H) is Sylow there,
and R is normal in itself. In addition, its image in every normal quotient
contains that quotient's p-core, so both source alternatives hold.

The forward implication tests arbitrary p-subgroups P and A with A normalizing
P. Their join is a p-group, so a single inner automorphism carries both into R.
Conjugation preserves nontriviality of P, normality of O_{p'}(H)P, and the
vanishing of the double commutator. The isomorphism transport theorem for the
exact action quotient N_H(P)/C_H(P) brings the relative bound back to P and A.
The reverse implication is the existing restriction theorem `PStable.relative`.

Source: Alperin--Brauer--Gorenstein, Chapter II, Section 6, article p. 55
(`refs/latex/alperin-brauer-gorenstein-pages/page-056.tex`). The printed phrase
that RK/K is Sylow in O_p(H/K) is a slip: it is Sylow in H/K, hence contains
the normal p-core. The quotient-core companion below records this intended
containment. Simultaneous conjugation of P and A combines the source's two
successive Sylow conjugations.
-/

namespace ABG

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

/-- A Sylow p-subgroup satisfies both clauses of relative-stability eligibility. -/
public theorem relativeStabilityEligible_sylow (R : Sylow p H) :
    RelativeStabilityEligible p (R : Subgroup H) := by
  refine ⟨R.isPGroup', R.exists_subgroupOf_eq_of_normal (Op_p'p p H), Or.inl ?_⟩
  refine ⟨R, le_rfl, ?_⟩
  rw [Subgroup.subgroupOf_self]
  infer_instance

/-- A Sylow subgroup also satisfies the quotient alternative of eligibility. -/
public theorem sylow_quotient_pCore_le (R : Sylow p H)
    (K : Subgroup H) [K.Normal] :
    pCore p (H ⧸ K) ≤ (R : Subgroup H).map (QuotientGroup.mk' K) := by
  exact (pCore_isPGroup (p := p) (G := H ⧸ K)).le_sylow_of_normal
    (R.mapSurjective (QuotientGroup.mk'_surjective K))

private theorem exists_conj_pair_le_sylow (R : Sylow p H)
    (P A : Subgroup H) (hP : IsPGroup p P) (hA : IsPGroup p A)
    (hAP : A ≤ Subgroup.normalizer (P : Set H)) :
    ∃ g : H, P.map (MulAut.conj g).toMonoidHom ≤ (R : Subgroup H) ∧
      A.map (MulAut.conj g).toMonoidHom ≤ (R : Subgroup H) := by
  obtain ⟨S, hS⟩ := (hP.to_sup_of_normal_left' hA hAP).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S R
  have hmap : (S : Subgroup H).map (MulAut.conj g).toMonoidHom = R := by
    exact congrArg Sylow.toSubgroup hg
  refine ⟨g, ?_, ?_⟩
  · exact (Subgroup.map_mono (le_sup_left.trans hS)).trans_eq hmap
  · exact (Subgroup.map_mono (le_sup_right.trans hS)).trans_eq hmap

private theorem conjugate_pair_conditions (R : Sylow p H)
    (P A : Subgroup H) (hne : P ≠ ⊥) (hn : (pPrimeCore p H ⊔ P).Normal)
    (hP : IsPGroup p P) (hA : IsPGroup p A)
    (hAP : A ≤ Subgroup.normalizer (P : Set H)) (hcomm : ⁅⁅P, A⁆, A⁆ = ⊥) :
    ∃ e : H ≃* H, P.map e.toMonoidHom ≠ ⊥ ∧
      (pPrimeCore p H ⊔ P.map e.toMonoidHom).Normal ∧
      P.map e.toMonoidHom ≤ (R : Subgroup H) ∧
      A.map e.toMonoidHom ≤ (R : Subgroup H) ∧
      ⁅⁅P.map e.toMonoidHom, A.map e.toMonoidHom⁆, A.map e.toMonoidHom⁆ = ⊥ := by
  obtain ⟨g, hPR, hAR⟩ := exists_conj_pair_le_sylow R P A hP hA hAP
  let e : H ≃* H := MulAut.conj g
  refine ⟨e, ?_, ?_, hPR, hAR, ?_⟩
  · intro hbot
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using hbot
  · have hmap := hn.map e.toMonoidHom e.surjective
    dsimp [e] at hmap ⊢
    simpa only [Subgroup.map_sup, Subgroup.Normal.map_conj_eq] using hmap
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hcomm, Subgroup.map_bot]

/-- Relative stability at a Sylow subgroup is ordinary stability in the same ABG domain. -/
public theorem relative_pStable_sylow_iff
    (R : Sylow p H) : RelativePStable p (R : Subgroup H) ↔ PStable p H := by
  constructor
  · rintro ⟨hp, hcore, hR, hstable⟩
    refine ⟨hp, hcore, ?_⟩
    intro P A hne hn hP hA hAP hcomm
    obtain ⟨e, hne', hn', hPR, hAR, hcomm'⟩ :=
      conjugate_pair_conditions R P A hne hn hP hA hAP hcomm
    exact (normalizerActionImage_le_pCore_map_iff p e P A hAP
      (hAR.trans (relative_subgroup_normalized _ _ hR.1 hPR hn'))).mp
        (hstable (P.map e.toMonoidHom) (A.map e.toMonoidHom) hne' hPR hn' hAR hcomm')
  · intro hstable
    exact hstable.relative _ (relativeStabilityEligible_sylow R)

end ABG
