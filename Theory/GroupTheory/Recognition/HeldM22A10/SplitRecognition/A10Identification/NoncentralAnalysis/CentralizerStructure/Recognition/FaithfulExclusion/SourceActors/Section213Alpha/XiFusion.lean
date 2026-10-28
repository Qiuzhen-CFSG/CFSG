module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion.InvolutionReduction

/-!
# Reduction of Held's normalized xi fusion to earlier normalizer arguments

The involution reduction of Lemma 2.2 is proved in `InvolutionReduction`.
If the three S-fusions of Lemmas 2.10--2.11 hold, its five representatives
lie in the pi or mu class. If pi, xi and pi*xi are not all conjugate, one
of the two xi choices avoids the pi class and therefore belongs to the mu class.

The xi-separation theorem (Lemma 2.7) and the S-normalizer fusion construction
remain explicit premises. Thus this module supplies a conditional assembly,
not yet the unconditional xi-fusion theorem or an alpha actor.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.2 and 2.7--2.11, pp.226, 229--230.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Replacing lambda by pi*lambda permutes the last two representatives. -/
public theorem section22_involution_representative_normalized [IsSimpleGroup G]
    (b : Bit) (x : G) (hx : orderOf x = 2) :
    IsConj x D.z ∨ IsConj x (D.a10ModelEmbedding e Coordinates.mu) ∨
      IsConj x (D.a10ModelEmbedding e tau) ∨
      IsConj x (D.a10ModelEmbedding e (normalizedLam b)) ∨
      IsConj x (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b)) := by
  have hswap : ∀ b : Bit,
      (lam = normalizedLam b ∧ Coordinates.pi * lam = Coordinates.pi * normalizedLam b) ∨
      (lam = Coordinates.pi * normalizedLam b ∧ Coordinates.pi * lam = normalizedLam b) := by
    decide +kernel
  rcases section22_involution_representative D e x hx with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases hswap b with ⟨hl, _⟩ | ⟨hl, _⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hl ▸ h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hl ▸ h))))
  · rcases hswap b with ⟨_, hl⟩ | ⟨_, hl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hl ▸ h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hl ▸ h))))

/-- The three S-fusions of Held 2.10--2.11 imply the global two-class bound. -/
public theorem involution_two_classes_of_s_fusion [IsSimpleGroup G] (b : Bit)
    (htau : IsConj D.z (D.a10ModelEmbedding e tau))
    (hlam : IsConj (D.a10ModelEmbedding e Coordinates.mu)
      (D.a10ModelEmbedding e (normalizedLam b)))
    (hpiLam : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b)))
    (x : G) (hx : orderOf x = 2) :
    IsConj x D.z ∨ IsConj x (D.a10NoncentralInvolution e) := by
  rcases section22_involution_representative_normalized D e b x hx with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl (h.trans htau.symm)
  · exact Or.inr (h.trans hlam.symm)
  · exact Or.inl (h.trans hpiLam.symm)

omit [Finite G] in
/-- Held 2.8's binary choice, conditional precisely on the separation in 2.7. -/
public theorem exists_normalizedXi_nonfusion
    (hsep : ¬ (IsConj D.z (D.a10ModelEmbedding e xi) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * xi)))) :
    ∃ d : Bit, ¬ IsConj D.z (D.a10ModelEmbedding e (normalizedXi d)) := by
  by_cases hx : IsConj D.z (D.a10ModelEmbedding e xi)
  · refine ⟨1, ?_⟩
    simpa only [normalizedXi, Fin.val_one, pow_one] using fun hp => hsep ⟨hx, hp⟩
  · refine ⟨0, ?_⟩
    simpa only [normalizedXi, Fin.val_zero, pow_zero, one_mul] using hx

omit [Finite G] in
private theorem normalizedXi_ambient_order (d : Bit) :
    orderOf (D.a10ModelEmbedding e (normalizedXi d)) = 2 := by
  rw [orderOf_injective (D.a10ModelEmbedding e) (D.a10ModelEmbedding_injective e)]
  apply orderOf_eq_prime
  · have h : ∀ d : Bit, normalizedXi d ^ 2 = 1 := by decide +kernel
    exact h d
  · have h : ∀ d : Bit, normalizedXi d ≠ 1 := by decide +kernel
    exact h d

/-- Assembly from the separation of 2.7 and the S-fusions of 2.10--2.11.
The two normalizer constructions supplying these premises remain separate obligations. -/
public theorem exists_xi_isConj_mu_of_separation_and_s_fusion [IsSimpleGroup G]
    (hsep : ¬ (IsConj D.z (D.a10ModelEmbedding e xi) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * xi))))
    (hs : ∃ b : Bit, IsConj D.z (D.a10ModelEmbedding e tau) ∧
      IsConj (D.a10ModelEmbedding e Coordinates.mu)
        (D.a10ModelEmbedding e (normalizedLam b)) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b))) :
    ∃ d : Bit, IsConj (D.a10ModelEmbedding e (normalizedXi d))
      (D.a10NoncentralInvolution e) := by
  obtain ⟨b, ht, hl, hpl⟩ := hs
  obtain ⟨d, hd⟩ := exists_normalizedXi_nonfusion D e hsep
  refine ⟨d, ?_⟩
  rcases involution_two_classes_of_s_fusion D e b ht hl hpl
      (D.a10ModelEmbedding e (normalizedXi d)) (normalizedXi_ambient_order D e d) with h | h
  · exact (hd h.symm).elim
  · exact h


end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
