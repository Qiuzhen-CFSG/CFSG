module

public import Theory.SpecificGroups.AlternatingSix.SylowPointwiseTwoPower.Rank

/-!
# Fixed-point generation for a Sylow-fixing four-group on A₆

The faithful natural four-group centralizing a marked Sylow D₈ contains a
transposition and a triple transposition. Their fixed groups contain the
explicit cycles (012), (013), and (014)(235), which generate A₆. Sylow
conjugacy and an actual group equivalence transport this calculation.

The marked calculation is adapted from the existing private proof in
`CFSG/Quasithin/ChapterE/Section06/CentralizerStructure/Components/RemainingSieve/AlternatingActions/Six.lean`.
Here it is independent of the triple-cover assumptions and chapter inputs.
All finite identities are checked by kernel reduction.

Source: Aschbacher–Smith, E.6.8(2),(4), printed pp.247–248.
-/

public section
open Subgroup GLS3.Chapter5 AlternatingSix.ShadowLocal
namespace Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry

private abbrev S6 := Equiv.Perm (Fin 6)

local instance (g : Equiv.Perm (Fin 6)) : Decidable (g ∈ A6) :=
  inferInstanceAs (Decidable (Equiv.Perm.sign g = 1))

private def tailSwap : S6 := Equiv.swap 4 5
private def centralDoubleSwap : S6 := Equiv.swap 0 2 * Equiv.swap 1 3

/-- The permutations fixing the marked dihedral Sylow subgroup pointwise. -/
private def permutationFixer : Subgroup S6 :=
  centralizer ({dihedralRotation.val, dihedralReflection.val} : Set S6)

private instance : DecidablePred (fun x : S6 => x ∈ permutationFixer) := fun x =>
  decidable_of_iff (dihedralRotation.val * x = x * dihedralRotation.val ∧
    dihedralReflection.val * x = x * dihedralReflection.val)
      (by simp [permutationFixer, mem_centralizer_iff])

private theorem permutationFixer_card : Nat.card permutationFixer = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def cycle012 : A6 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide +kernel⟩
private def cycle013 : A6 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by decide +kernel⟩
private def pairCycle : A6 :=
  ⟨(Equiv.swap 0 1 * Equiv.swap 1 4) *
    (Equiv.swap 2 3 * Equiv.swap 3 5), by decide +kernel⟩

/-- The cycles (012), (013), and (014)(235) generate A₆. The two displayed
words give (014) and (015), after which the standard three-cycle theorem applies. -/
private theorem generators_generate (H : Subgroup A6)
    (ha : cycle012 ∈ H) (hb : cycle013 ∈ H) (hc : pairCycle ∈ H) : H = ⊤ := by
  have h4 : ((cycle013 * pairCycle * cycle012 * pairCycle * pairCycle : A6) : S6) =
      GroupTheory.AutAlternating.genPerm 6 4 := by decide +kernel
  have h5 : ((cycle012 * cycle012 * pairCycle * cycle012 * pairCycle * cycle013 * cycle012 : A6) : S6) =
      GroupTheory.AutAlternating.genPerm 6 5 := by decide +kernel
  have hgen : Subgroup.closure
      (Set.range fun i : {i : Fin 6 // i ≠ 0 ∧ i ≠ 1} =>
        GroupTheory.AutAlternating.genPerm 6 i.1) ≤
      H.map (alternatingGroup (Fin 6)).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨i, hi0, hi1⟩, rfl⟩
    fin_cases i
    · exact (hi0 rfl).elim
    · exact (hi1 rfl).elim
    · exact mem_map_of_mem _ ha
    · exact mem_map_of_mem _ hb
    · exact ⟨cycle013 * pairCycle * cycle012 * pairCycle * pairCycle, H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hb hc) ha) hc) hc, h4⟩
    · exact ⟨cycle012 * cycle012 * pairCycle * cycle012 * pairCycle * cycle013 * cycle012, H.mul_mem (H.mul_mem (H.mul_mem
        (H.mul_mem (H.mul_mem (H.mul_mem ha ha) hc) ha) hc) hb) ha, h5⟩
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  obtain ⟨x, hx, he⟩ := hgen
    (GroupTheory.AutAlternating.isThreeCycle_mem_closure_gen (by decide) hg)
  exact Subtype.val_injective he ▸ hx

/-- An order-four natural action fixing the marked Sylow subgroup contains
both the transposition and the commuting triple transposition. -/
private theorem standard_fixed_generation (J : Subgroup AutA6)
    (hJ : Nat.card J = 4) (hn : J ≤ natural)
    (hfixr : ∀ β ∈ J, β dihedralRotation = dihedralRotation)
    (hfixs : ∀ β ∈ J, β dihedralReflection = dihedralReflection)
    (H : Subgroup A6) (hH : ∀ β ∈ J, β ≠ 1 → automorphismFixedSubgroup β ≤ H) :
    H = ⊤ := by
  have hle : J ≤ permutationFixer.map permutationAction := by
    intro β hβ
    obtain ⟨π, hπ⟩ := hn hβ
    refine ⟨π, ?_, hπ⟩
    change π ∈ permutationFixer
    rw [permutationFixer, mem_centralizer_iff]
    rintro x (rfl | rfl)
    · have he := congrArg Subtype.val (hfixr β hβ)
      rw [← hπ] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · have he := congrArg Subtype.val (hfixs β hβ)
      rw [← hπ] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have heq : J = permutationFixer.map permutationAction := eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective permutationAction_injective, permutationFixer_card, hJ])
  have htC : tailSwap ∈ permutationFixer := by
    rw [permutationFixer, mem_centralizer_iff]
    rintro x (rfl | rfl) <;> decide +kernel
  have htuC : tailSwap * centralDoubleSwap ∈ permutationFixer := by
    rw [permutationFixer, mem_centralizer_iff]
    rintro x (rfl | rfl) <;> decide +kernel
  have ht : permutationAction tailSwap ∈ J := heq.symm ▸ mem_map_of_mem _ htC
  have htu : permutationAction (tailSwap * centralDoubleSwap) ∈ J := heq.symm ▸ mem_map_of_mem _ htuC
  have htn : permutationAction tailSwap ≠ 1 := by
    intro he
    have : tailSwap = 1 := permutationAction_injective (he.trans (map_one _).symm)
    exact (by decide +kernel : tailSwap ≠ 1) this
  have htun : permutationAction (tailSwap * centralDoubleSwap) ≠ 1 := by
    intro he
    have : tailSwap * centralDoubleSwap = 1 := permutationAction_injective (he.trans (map_one _).symm)
    exact (by decide +kernel : tailSwap * centralDoubleSwap ≠ 1) this
  exact generators_generate H
    (hH _ ht htn (by change permutationAction tailSwap cycle012 = cycle012; decide +kernel))
    (hH _ ht htn (by change permutationAction tailSwap cycle013 = cycle013; decide +kernel))
    (hH _ htu htun (by change permutationAction (tailSwap * centralDoubleSwap) pairCycle = pairCycle; decide +kernel))

/-- Sylow conjugacy reduces to the marked calculation. Naturalness follows
from the proved Sylow-fixing theorem, which treats exceptional automorphisms. -/
private theorem quotient_fixed_generation (P : Sylow 2 A6)
    (J : Subgroup AutA6) (hJ : IsPGroup 2 J)
    (hfix : ∀ β ∈ J, ∀ x ∈ (P : Subgroup A6), β x = x)
    (hcard : Nat.card J = 4)
    (H : Subgroup A6) (hH : ∀ β ∈ J, β ≠ 1 → automorphismFixedSubgroup β ≤ H) :
    H = ⊤ := by
  have hDcard : Nat.card dihedralEmbedding.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective dihedralEmbedding_injective).toEquiv,
      DihedralGroup.nat_card]
  have hp : IsPGroup 2 dihedralEmbedding.range := IsPGroup.of_card
    (show Nat.card dihedralEmbedding.range = 2 ^ 3 from hDcard)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hD : dihedralEmbedding.range = (Q : Subgroup A6) :=
    eq_of_le_of_card_ge hQ (by rw [hDcard, alternatingSylow_card])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A6 P Q
  let k : MulAut A6 := MulAut.conj g
  have hmap : (P : Subgroup A6).map k.toMonoidHom = (Q : Subgroup A6) :=
    congrArg Sylow.toSubgroup hg
  let J' : Subgroup AutA6 := J.map (MulAut.congr k).toMonoidHom
  have hfix' : ∀ β ∈ J', ∀ x ∈ (Q : Subgroup A6), β x = x := by
    rintro _ ⟨β, hβ, rfl⟩ x hx
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change k (β (k.symm (k y))) = k y
    rw [k.symm_apply_apply, hfix β hβ y hy]
  have hn : J' ≤ natural := by
    intro β hβ
    obtain ⟨n, hn⟩ := hJ.map (MulAut.congr k).toMonoidHom (⟨β, hβ⟩ : J')
    exact twoPower_mem_natural_of_fixes_sylow Q β
      (congrArg Subtype.val hn) (hfix' β hβ)
  have hr : dihedralRotation ∈ (Q : Subgroup A6) := by
    rw [← hD]
    exact ⟨DihedralGroup.r 1, by decide +kernel⟩
  have hs : dihedralReflection ∈ (Q : Subgroup A6) := by
    rw [← hD]
    exact ⟨DihedralGroup.sr 0, by decide +kernel⟩
  have htop : H.map k.toMonoidHom = ⊤ := by
    apply standard_fixed_generation J'
      (by rw [card_map_of_injective (MulAut.congr k).injective]; exact hcard) hn
      (fun β hβ => hfix' β hβ _ hr) (fun β hβ => hfix' β hβ _ hs)
    rintro _ ⟨β, hβ, rfl⟩ hne x hx
    have hβne : β ≠ 1 := by
      intro he
      exact hne (by rw [he, map_one])
    have hfixed : β (k.symm x) = k.symm x := by
      apply k.injective
      exact (show k (β (k.symm x)) = x from hx).trans (k.apply_symm_apply x).symm
    exact ⟨k.symm x, hH β hβ hβne hfixed, k.apply_symm_apply x⟩
  apply top_unique
  intro x _
  have hx : k x ∈ H.map k.toMonoidHom := htop.symm ▸ mem_top _
  obtain ⟨y, hy, he⟩ := hx
  exact k.injective he ▸ hy


/-- An order-four action fixing a Sylow subgroup pointwise generates the
actual group by the fixed subgroups of its nonidentity actors. -/
theorem fixed_generation {X : Type*} [Group X] [Finite X]
    (e : X ≃* A6) (S : Sylow 2 X) (J : Subgroup (MulAut X))
    (hJ : IsPGroup 2 J)
    (hfix : ∀ a ∈ J, ∀ x ∈ (S : Subgroup X), a x = x)
    (hcard : Nat.card J = 4)
    (H : Subgroup X)
    (hH : ∀ a ∈ J, a ≠ 1 → automorphismFixedSubgroup a ≤ H) : H = ⊤ := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let I := J.map (MulAut.congr e).toMonoidHom
  have hfixI : ∀ a ∈ I, ∀ x ∈ (P : Subgroup A6), a x = x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hfix a ha x hx]
  have he : H.map e.toMonoidHom = ⊤ := by
    apply quotient_fixed_generation P I (hJ.map _) hfixI
      (by rw [card_map_of_injective (MulAut.congr e).injective]; exact hcard)
    rintro _ ⟨a, ha, rfl⟩ hne x hx
    have ha1 : a ≠ 1 := by
      intro he
      exact hne (by rw [he, map_one])
    have hf : a (e.symm x) = e.symm x := by
      apply e.injective
      exact (show e (a (e.symm x)) = x from hx).trans (e.apply_symm_apply x).symm
    exact ⟨e.symm x, hH a ha ha1 hf, e.apply_symm_apply x⟩
  exact e.mapSubgroup.injective (he.trans e.mapSubgroup.map_top.symm)

end Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry

public section
open Subgroup GLS3.Chapter5 AlternatingSix.ShadowLocal
namespace Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry

/-- A Sylow-fixing four-group cannot fix an entire maximal proper subgroup.
Otherwise each nonidentity actor has exactly that fixed subgroup, contradicting
fixed-point generation. -/
theorem coatom_not_fixed_of_card_four {X : Type*} [Group X] [Finite X]
    (e : X ≃* A6) (S : Sylow 2 X) (J : Subgroup (MulAut X))
    (hJ : IsPGroup 2 J)
    (hfix : ∀ a ∈ J, ∀ x ∈ (S : Subgroup X), a x = x)
    (hcard : Nat.card J = 4) (H : Subgroup X) (hH : IsCoatom H) :
    ¬ ∀ a ∈ J, ∀ x ∈ H, a x = x := by
  intro hfixed
  apply hH.1
  apply fixed_generation e S J hJ hfix hcard H
  intro a ha ha1
  have hl : H ≤ automorphismFixedSubgroup a := hfixed a ha
  rcases eq_or_lt_of_le hl with he | hlt
  · exact he.ge
  · have ht := hH.2 _ hlt
    have he : a = 1 := by
      ext x
      exact (show x ∈ automorphismFixedSubgroup a from ht.symm ▸ mem_top x)
    exact (ha1 he).elim

end Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry
