module

public import Theory.Quasithin.NormalTwoRank

/-!
# Transporting a parabolic rank obstruction through an embedding

A finite group with a nontrivial normal 2-subgroup and odd-prime rank at
least three cannot embed in a quasithin group. Transport quasithinness to
the image and then back along the injective homomorphism; the normal
2-subgroup is needed only inside the original parabolic. In particular it
does not have to be normal in a larger extension or completion.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, final
paragraph of the proof of F.1.12, printed p. 264 (including extensions of
the U₅(2) amalgam).
-/

public section

namespace Theory.Quasithin

/-- An embedding transports a local obstruction without any ambient-normality assumption. -/
theorem not_quasithin_of_embedded_normal_two_rank
    {G P : Type*} [Group G] [Finite G] [Group P] [Finite P]
    (f : P →* G) (hf : Function.Injective f)
    (Q : Subgroup P) [Q.Normal] (hQ : Q ≠ ⊥) (hQp : IsPGroup 2 Q)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hr : 3 ≤ primeRank p P) :
    ¬ IsQuasithin G := by
  intro hG
  have hP : IsQuasithin P :=
    (isQuasithin_congr (MonoidHom.ofInjective hf)).mpr (hG.subgroup f.range)
  have hle := primeRank_le_two_of_normal_two_subgroup hP Q hQ hQp p hp ho
  exact (Nat.not_succ_le_self 2) (hr.trans hle)

end Theory.Quasithin
