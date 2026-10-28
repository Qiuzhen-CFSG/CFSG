module

public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ParabolicRestrictions
public import Theory.GroupTheory.TwoLocalSurjective
public import Theory.Quasithin.Rank

/-!
# Passing the parabolic-section obstruction through the actual central quotient

A proper two-local subgroup in a surjective image lifts, by the Frattini
argument, to a proper two-local subgroup of the original finite group.
Its sections lift through the same surjection. Specializing the map to
G → G/Z(G) → H retains the literal central quotient and the supplied model
isomorphism; quasithinness of H is never assumed.

The smaller-section induction hypothesis for Theorem A, quasithinness and
the K-group hypothesis on G now bound every odd-prime rank of a semisimple
section of such a parabolic by two. A concrete Sp₆(2ᵃ) section contradicts
this bound using ParabolicRestrictions. Construction of the parabolics and
sections for the other Lie families remains separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.2.15(2)
and the first paragraph of A.2.18, printed pp.37–40 (refs/quasithin.pdf).
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u v w
variable {G : Type u} {H : Type v} {S : Type w}
  [Group G] [Finite G] [Group H] [Group S]

theorem exists_proper_twoLocal_section_lift
    (π : G →* H) (hπ : Function.Surjective π) {P : Subgroup H}
    (hP : P ≠ ⊤) (hlocal : IsTwoLocal P) (hsection : IsSectionOf S P) :
    ∃ M : Subgroup G, M ≠ ⊤ ∧ IsTwoLocal M ∧ M.map π = P ∧ IsSectionOf S M := by
  obtain ⟨M, hM, hmap, φ, hφ, _⟩ := hlocal.exists_surjective_of_surjective π hπ
  refine ⟨M, ?_, hM, hmap, hsection.ambient_surjective φ hφ⟩
  intro ht
  apply hP
  rw [ht, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπ] at hmap
  exact hmap.symm

theorem section_rank_bound_of_surjective {p : ℕ}
    (π : G →* H) (hπ : Function.Surjective π)
    (hsource : ∀ M : Subgroup G, M ≠ ⊤ → IsTwoLocal M →
      IsSectionOf S M → primeRank p S ≤ 2)
    {P : Subgroup H} (hP : P ≠ ⊤) (hlocal : IsTwoLocal P)
    (hsection : IsSectionOf S P) : primeRank p S ≤ 2 := by
  obtain ⟨M, hM, hl, _, hs⟩ := exists_proper_twoLocal_section_lift π hπ hP hlocal hsection
  exact hsource M hM hl hs

theorem section_rank_bound_of_center_quotient {p : ℕ}
    (e : (G ⧸ Subgroup.center G) ≃* H)
    (hsource : ∀ M : Subgroup G, M ≠ ⊤ → IsTwoLocal M →
      IsSectionOf S M → primeRank p S ≤ 2)
    {P : Subgroup H} (hP : P ≠ ⊤) (hlocal : IsTwoLocal P)
    (hsection : IsSectionOf S P) : primeRank p S ≤ 2 :=
  section_rank_bound_of_surjective
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hsource hP hlocal hsection

theorem false_of_center_quotient_parabolic_section {p : ℕ}
    (e : (G ⧸ Subgroup.center G) ≃* H)
    (hsource : ∀ M : Subgroup G, M ≠ ⊤ → IsTwoLocal M →
      IsSectionOf S M → primeRank p S ≤ 2)
    {P : Subgroup H} (hP : P ≠ ⊤) (hlocal : IsTwoLocal P)
    (hsection : IsSectionOf S P) (hrank : 2 < primeRank p S) : False :=
  (not_le_of_gt hrank) (section_rank_bound_of_center_quotient e hsource hP hlocal hsection)
/-- The actual A.2.15 rank input, derived from its smaller-section induction
hypothesis, applies to semisimple sections of parabolics in G/Z(G). -/
theorem semisimple_section_rank_of_center_quotient
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {T : Type u} [Group T] [Finite T]
    (e : (G ⧸ Subgroup.center G) ≃* H)
    {P : Subgroup H} (hP : P ≠ ⊤) (hlocal : IsTwoLocal P)
    (hsection : IsSectionOf T P) (hsemi : IsSemisimple T)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p T ≤ 2 := by
  apply section_rank_bound_of_center_quotient e ?_ hP hlocal hsection
  intro M hM hl hs
  have hr : primeRank p M ≤ 2 :=
    Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG M hl p hp ho
  have hA := ih M (IsProperSectionOf.subgroup M hM)
  exact ((hA (IsQuasithin.subgroup hG M) (hK.subgroup M) T hs hsemi p hp ho).2 hr).trans hr

/-- This quotient-parabolic strong-rank conclusion uses induction on proper
sections of G, not an assumed quasithin quotient. -/
theorem stronglyQuasithin_semisimple_section_of_center_quotient
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {T : Type u} [Group T] [Finite T]
    (e : (G ⧸ Subgroup.center G) ≃* H)
    {P : Subgroup H} (hP : P ≠ ⊤) (hlocal : IsTwoLocal P)
    (hsection : IsSectionOf T P) (hsemi : IsSemisimple T) : IsStronglyQuasithin T :=
  fun p hp ho => semisimple_section_rank_of_center_quotient ih hG hK e
    hP hlocal hsection hsemi p hp ho

/-- Source application: a rank-three symplectic section of a proper parabolic
contradicts A.2.15(2), for every positive characteristic-two exponent. -/
theorem false_of_symplectic_six_parabolic_section
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {T : Type u} [Group T] [Finite T]
    (e : (G ⧸ Subgroup.center G) ≃* H)
    {P : Subgroup H} (hP : P ≠ ⊤) (hlocal : IsTwoLocal P)
    (hsection : IsSectionOf T P) (hsemi : IsSemisimple T)
    {a : ℕ} (ha : 0 < a) (hmodel : ClassicalGroup.IsPSp T 3 (2 ^ a)) : False :=
  not_stronglyQuasithin_symplectic_six ha hmodel
    (stronglyQuasithin_semisimple_section_of_center_quotient ih hG hK e
      hP hlocal hsection hsemi)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
