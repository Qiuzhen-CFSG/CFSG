module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceInspectionSmall
public import Theory.SpecificGroups.PSL2.OddPerfectInnerAction

/-!
# Odd rank-one rows of the corrected source inspection

Faithful descent through the center transports the actual secondary image to
an inner perfect subgroup of the odd PSL₂ model. Its two-core is trivial,
so the torus centralizes it. In field degrees at most two this centralizer
is a two-group, whereas every prime in the source torus is odd. Core movement
and whole-radical generation force a nontrivial torus image, a contradiction.

This excludes the complete odd rank-one family in Theorem C on the literal
inner image, retaining every possible central cover of the full quotient.
The odd ternary, binary rank-two and sporadic rows still require inspection.
Source: Aschbacher--Smith, 4.3.12--16, printed pp.617--618; A.2.3, p.33.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- Every odd PSL₂ row of Theorem C is excluded through the same faithful
central descent of the original normal-quotient action. -/
theorem SecondarySourceData.not_odd_linear_two_inner_of_generation
    (s : SecondarySourceData c n) (hn : 0<n) (hg : SecondarySourceData.ActionGeneration s)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (hmodel : ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 2 (p^e)) : False := by
  let := s.normal
  let := s.quasisimple
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hmodel
  let b := (SecondarySourceData.centralQuotientEquiv s).trans a
  let f := MulAut.centralQuotientAction b
  have hf : Function.Injective f := MulAut.centralQuotientAction_injective b
  let X := SourceImages.image c s.component (secondary c)
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  let : Group.IsPerfect (X.map f) := Group.IsPerfect.map f
  have hi : X.map f ≤ MulAut.innerSubgroup (Theory.PSL2.Group F) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨q,rfl⟩ := SourceImages.secondary_inner c s.component s.secondary_le hx
    exact ⟨b (QuotientGroup.mk' _ q),(MulAut.centralQuotientAction_conj b q).symm⟩
  have hne : X.map f ≠ ⊥ := fun hz =>
    SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model
      ((X.map_eq_bot_iff_of_injective hf).mp hz)
  have hcore : X.pCoreIn 2 = ⊥ := by
    apply ((X.pCoreIn 2).map_eq_bot_iff_of_injective (f := f) hf).mp
    rw [map_pCoreIn_of_injective 2 X f hf]
    change (pCore 2 (X.map f)).map (X.map f).subtype = ⊥
    rw [Theory.PSL2.odd_perfect_inner_subgroup_twoCore_eq_bot
      (by rw [hF]; exact ho.pow) _ hi,Subgroup.map_bot]
  have hc : SecondarySourceData.CoreImageCentral s := by
    have hbound := SourceImages.secondary_core_le c s.component
    change SourceImages.image c s.component ((secondary c).pCoreIn 2) ≤ X.pCoreIn 2 at hbound
    rw [hcore] at hbound
    exact hbound.trans bot_le
  obtain ⟨r,hr,hro,_,y,hy,hyord⟩ :=
    SecondarySourceData.torus_prime_action_of_nontrivial_image s hn
      (SecondarySourceData.torusImage_ne_bot_of_central_core_and_generation s hc hg)
  have hY := SourceImages.torus_centralizes c s.component s.torus
    (s.secondary_le.trans (map_subtype_le _)) s.torus_le s.torus_secondary hc
  have hyC : f (s.action y) ∈ centralizer (X.map f : Set _) :=
    map_centralizer_le_centralizer_image X f
      (mem_map_of_mem f (hY (mem_map_of_mem s.action hy)))
  have htwo := Theory.PSL2.small_degree_perfect_inner_centralizer_isTwoGroup
    hp ho he hF (X.map f) hne hi
  have hcop := htwo.orderOf_coprime (Nat.coprime_two_left.mpr hro)
    (⟨f (s.action y),hyC⟩ : centralizer (X.map f : Set _))
  rw [←Subgroup.orderOf_coe,orderOf_injective f hf,hyord] at hcop
  exact hr.ne_one (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) (dvd_refl _))

/-- The odd-characteristic catalogue now retains only the ternary models;
the same explicit generation identity excludes every rank-one row. -/
theorem SecondarySourceData.inspection_remaining_models_without_odd_rank_one
    (s : SecondarySourceData c n) (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 3 p ∨
        ClassicalGroup.IsPSU (SecondarySourceData.componentImage s) 3 p)) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondarySourceData.componentImage s) f) ∨
      ChapterA.Section02.IsTheoremCSporadicModel (SecondarySourceData.componentImage s) := by
  rcases SecondarySourceData.inspection_remaining_models s hn hg D h with hm | hm
  · cases hm with
    | linear_two p e hp ho he hm =>
      exact (SecondarySourceData.not_odd_linear_two_inner_of_generation s
        (by omega) hg hp ho he hm).elim
    | linear_three p hp ho hm => exact Or.inl ⟨p,hp,ho,Or.inl hm⟩
    | unitary_three p hp ho hm => exact Or.inl ⟨p,hp,ho,Or.inr hm⟩
  · exact Or.inr hm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
