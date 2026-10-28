module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramActorLift
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramModelPair
/-!
# The index-two stabilizer of the actual marked residual

The two distinct parabolic preimages have distinct perfect residuals because
the first residual is outside the Borel. The actual source action permutes
these residuals, and a diagram-moving element interchanges them. Its relative
normalizer therefore has index two in the original Sylow subgroup.

Source: Aschbacher–Smith, 14.2.8(3), printed p.983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

omit [Finite H] [Finite D] in
theorem markedParabolicResidual_le_preimage (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (P : Subgroup D) :
    markedParabolicResidual M K e P ≤ (markedParabolicPreimage M K e P).map K.subtype := by
  rintro x ⟨y,hy,rfl⟩
  exact ⟨y.val,y.property,rfl⟩

omit [Finite H] [Finite D] in
theorem markedParabolicResidual_pair_ne (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (P Q B : Subgroup D)
    (he : (componentOverlap M K).map e.toMonoidHom = B) (hB : P ⊓ Q = B)
    (hout : ¬ markedParabolicResidual M K e P ≤ M) :
    markedParabolicResidual M K e P ≠ markedParabolicResidual M K e Q := by
  intro h
  apply hout
  intro x hx
  obtain ⟨y,hy,rfl⟩ := markedParabolicResidual_le_preimage M K e P hx
  obtain ⟨z,hz,hzy⟩ := markedParabolicResidual_le_preimage M K e Q (h ▸ hx)
  have hzy' : z = y := K.subtype_injective hzy
  subst z
  apply (markedParabolicMap_mem_borel M K e he y).mp
  rw [← hB]
  exact ⟨hy,hz⟩

omit [Finite D] in
theorem markedParabolicResidual_normalizer_index_two
    (M K T : Subgroup H) [K.Normal] (hTM : T ≤ M)
    (e : sourceImage M K ≃* D) (P Q B : Subgroup D)
    (he : (componentOverlap M K).map e.toMonoidHom = B) (hB : P ⊓ Q = B)
    (hout : ¬ markedParabolicResidual M K e P ≤ M)
    (hpair : ∀ a : MulAut D, B.map a.toMonoidHom = B →
      (P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q) ∨
      (P.map a.toMonoidHom = Q ∧ Q.map a.toMonoidHom = P))
    (t : H) (ht : t ∈ T)
    (hmove : ¬ (PreservesParabolicClass (markedParabolicActor M K e t) P ∧
      PreservesParabolicClass (markedParabolicActor M K e t) Q)) :
    (normalizer (markedParabolicResidual M K e P : Set H)).relIndex T = 2 := by
  let L := markedParabolicResidual M K e P
  let W := markedParabolicResidual M K e Q
  have hh (g : H) (hg : g ∈ T) :=
    hpair (markedParabolicActor M K e g) (markedParabolicActor_borel M K e he g (hTM hg))
  have hconj (g : H) (hg : g ∈ T) :
      L.map (MulAut.conj g).toMonoidHom = L ∨ L.map (MulAut.conj g).toMonoidHom = W := by
    rcases hh g hg with h | h
    · exact Or.inl (markedParabolicResidual_conj M K e P P g h.1)
    · exact Or.inr (markedParabolicResidual_conj M K e P Q g h.1)
  apply normalizer_relIndex_eq_two_of_pair T L W hconj t ht
  intro hfix
  rcases hh t ht with h | h
  · apply hmove
    have h1 : (MulAut.conj (1 : D)).toMonoidHom = MonoidHom.id D := by ext x; simp
    exact ⟨⟨1,by rw [h1,map_id]; exact h.1⟩,⟨1,by rw [h1,map_id]; exact h.2⟩⟩
  · have hswap := markedParabolicResidual_conj M K e P Q t h.1
    exact markedParabolicResidual_pair_ne M K e P Q B he hB hout (hfix.symm.trans hswap)

omit [Finite H] [Finite D] in
theorem invariant_pair_of_both_images (P Q : Subgroup D) (hPQ : P ≠ Q)
    (a : MulAut D) (hp : P.map a.toMonoidHom = P ∨ P.map a.toMonoidHom = Q)
    (hq : Q.map a.toMonoidHom = P ∨ Q.map a.toMonoidHom = Q) :
    (P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q) ∨
      (P.map a.toMonoidHom = Q ∧ Q.map a.toMonoidHom = P) := by
  have hne : P.map a.toMonoidHom ≠ Q.map a.toMonoidHom :=
    fun he => hPQ (map_injective a.injective he)
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact (hne (hp.trans hq.symm)).elim
  · exact Or.inl ⟨hp,hq⟩
  · exact Or.inr ⟨hp,hq⟩
  · exact (hne (hp.trans hq.symm)).elim

omit [Finite D] in
theorem markedParabolicResidual_index_two_of_movesDiagram
    (M K T : Subgroup H) [K.Normal] (hTM : T ≤ M)
    (e : sourceImage M K ≃* D) (P Q B : Subgroup D)
    (he : (componentOverlap M K).map e.toMonoidHom = B) (hB : P ⊓ Q = B)
    (hout : ¬ markedParabolicResidual M K e P ≤ M)
    (hpair : ∀ a : MulAut D, B.map a.toMonoidHom = B →
      (P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q) ∨
      (P.map a.toMonoidHom = Q ∧ Q.map a.toMonoidHom = P))
    (hmove : MovesDiagram M K T e P Q) :
    (T ⊓ normalizer (markedParabolicResidual M K e P : Set H)).relIndex T = 2 := by
  obtain ⟨a,ha,hm⟩ := hmove
  obtain ⟨t,ht,heq⟩ := sourceAutomizer_eq_markedParabolicActor_image M K T e a ha
  rw [inf_comm,inf_relIndex_right]
  exact markedParabolicResidual_normalizer_index_two M K T hTM e P Q B he hB hout
    hpair t ht (heq ▸ hm)
end CFSG.Quasithin.Chapter14.Section02
