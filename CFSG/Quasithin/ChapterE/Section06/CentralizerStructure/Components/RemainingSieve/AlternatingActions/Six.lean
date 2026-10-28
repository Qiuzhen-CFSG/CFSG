module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions.Transport
public import Theory.SpecificGroups.AlternatingSix.SylowPointwiseTwoPower.Rank
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms

/-!
# Sylow-fixing actions on the triple cover of A₆

The action descends faithfully through the whole center. The proved calculation
in Aut(A₆), including its exceptional automorphisms, bounds a Sylow-fixing
two-group by four and places it in the natural S₆. At order four, Sylow
conjugacy identifies it with the permutation centralizer of the marked D₈.
The fixed groups of its transposition and triple transposition contain the
explicit generators (012), (013), and (014)(235) of A₆.

An involution-fixed quotient element lifts to a fixed element through a kernel
of exponent three: correct a lift x by the inverse of α(x)x⁻¹. Thus the fixed
subgroups generate the quotient. A subgroup surjecting onto a perfect central
extension is the whole group, which gives generation in the actual cover.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(4),
printed pp.247–248, and the triple-cover alternative of 1.1.5(3)(c), pp.501–502.
The final interface retains the literal transposition action from that source;
the intrinsic calculation proves both conclusions without needing this marking.
-/

public section

open Subgroup Theory.GroupTheory
open AlternatingSix.ShadowLocal

namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions

private abbrev S6 := Equiv.Perm (Fin 6)

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
    (H : Subgroup A6) (hH : ∀ β ∈ J, β ≠ 1 → fixedSubgroup β ≤ H) :
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
    (H : Subgroup A6) (hH : ∀ β ∈ J, β ≠ 1 → fixedSubgroup β ≤ H) :
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

open PerfectCentralCovering
variable {X : Type*} [Group X] [Finite X] [IsQuasisimple X]

private def cover (e : (X ⧸ center X) ≃* A6) : Cover X A6 where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

omit [Finite X] in
private theorem cover_ker (e : (X ⧸ center X) ≃* A6) :
    (cover e).toMonoidHom.ker = center X := by
  change (e.toMonoidHom.comp (QuotientGroup.mk' (center X))).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

private theorem cover_fixing (e : (X ⧸ center X) ≃* A6)
    (E : Subgroup (MulAut X)) (S : Sylow 2 X)
    (hfix : ∀ a ∈ E, ∀ x ∈ (S : Subgroup X), a x = x) :
    ∀ a ∈ E.map ((cover e).autMap (cover_ker e)),
      ∀ x ∈ (S.mapSurjective (cover e).surjective : Subgroup A6), a x = x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
  rw [Cover.autMap_apply, hfix a ha x hx]

/-- Faithful descent bounds the actual action on any perfect central cover of A₆. -/
theorem six_cover_action_card_le_four (e : (X ⧸ center X) ≃* A6)
    (E : Subgroup (MulAut X)) [IsElementaryAbelian 2 E] (S : Sylow 2 X)
    (hfix : ∀ a ∈ E, ∀ x ∈ (S : Subgroup X), a x = x) : Nat.card E ≤ 4 := by
  have h := twoSubgroup_fixes_sylow_card_le_four
    (S.mapSurjective (cover e).surjective) (E.map ((cover e).autMap (cover_ker e)))
    ((IsElementaryAbelian.isPGroup 2 E).map _) (cover_fixing e E S hfix)
  rwa [card_map_of_injective ((cover e).autMap_injective (cover_ker e))] at h

/-- Correct a lift by its involutory displacement. This is the cubic-kernel
argument of Chapter2.ComponentRefinement.AlternatingSeven.CoverAction. -/
private theorem exists_fixed_lift_of_cube_kernel {K P : Type*} [Group K] [Group P]
    (f : K →* P) (hf : Function.Surjective f)
    (hker : ∀ c ∈ f.ker, c ^ 3 = 1) (α : MulAut K) (hα : α ^ 2 = 1)
    (y : P) (hy : ∀ x, f x = y → f (α x) = y) :
    ∃ x : K, f x = y ∧ α x = x := by
  obtain ⟨x, hx⟩ := hf y
  let c : K := α x * x⁻¹
  have hfc : f c = 1 := by simp [c, hy x hx, hx]
  have hc : c ^ 3 = 1 := hker c (MonoidHom.mem_ker.mpr hfc)
  have hαα : α (α x) = x := by
    have hh := DFunLike.congr_fun hα x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hαc : α c = c⁻¹ := by
    dsimp [c]
    rw [map_mul, map_inv, hαα]
    group
  have hαx : α x = c * x := by simp [c]
  have hcc : c * c = c⁻¹ := by
    apply (eq_inv_iff_mul_eq_one).mpr
    simpa only [pow_succ, pow_zero, one_mul] using hc
  refine ⟨c⁻¹ * x, by simp [hfc, hx], ?_⟩
  rw [map_mul, map_inv, hαc, inv_inv, hαx, ← mul_assoc, hcc]

omit [Finite X] in
private theorem cover_fixed_image (e : (X ⧸ center X) ≃* A6)
    (hz : Nonempty (center X ≃* Multiplicative (ZMod 3)))
    (α : MulAut X) (hα : α ^ 2 = 1) :
    (fixedSubgroup α).map (cover e).toMonoidHom =
      fixedSubgroup ((cover e).autMap (cover_ker e) α) := by
  have hcard : Nat.card (center X) = 3 := by
    obtain ⟨z⟩ := hz
    rw [Nat.card_congr z.toEquiv]
    simp
  have hker : ∀ c ∈ (cover e).toMonoidHom.ker, c ^ 3 = 1 := by
    intro c hc
    rw [cover_ker] at hc
    have hp := pow_card_eq_one' (x := (⟨c, hc⟩ : center X))
    rw [hcard] at hp
    exact congrArg Subtype.val hp
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change (cover e).autMap (cover_ker e) α ((cover e).toMonoidHom x) = _
    rw [Cover.autMap_apply, (show α x = x from hx)]
    rfl
  · intro y hy
    obtain ⟨x, hx, hfixed⟩ := exists_fixed_lift_of_cube_kernel
      (cover e).toMonoidHom (cover e).surjective hker α hα y (by
        intro x hx
        rw [← Cover.autMap_apply, hx]
        exact hy)
    exact ⟨x, hfixed, hx⟩

/-- Fixed-subgroup generation in the quotient lifts through the cubic center.
Perfectness then rules out a proper subgroup mapping onto the whole quotient. -/
theorem six_cover_fixedSubgroup_generation (e : (X ⧸ center X) ≃* A6)
    (hz : Nonempty (center X ≃* Multiplicative (ZMod 3)))
    (E : Subgroup (MulAut X)) [IsElementaryAbelian 2 E] (S : Sylow 2 X)
    (hfix : ∀ a ∈ E, ∀ x ∈ (S : Subgroup X), a x = x) (hcard : Nat.card E = 4) :
    (⊤ : Subgroup X) ≤ ⨆ (a : E) (_ : a ≠ 1), fixedSubgroup (a : MulAut X) := by
  let H : Subgroup X := ⨆ (a : E) (_ : a ≠ 1), fixedSubgroup (a : MulAut X)
  have himage : H.map (cover e).toMonoidHom = ⊤ := by
    apply quotient_fixed_generation (S.mapSurjective (cover e).surjective)
      (E.map ((cover e).autMap (cover_ker e)))
      ((IsElementaryAbelian.isPGroup 2 E).map _) (cover_fixing e E S hfix)
      (by rw [card_map_of_injective ((cover e).autMap_injective (cover_ker e)), hcard])
    rintro _ ⟨a, ha, rfl⟩ hne
    let a' : E := ⟨a, ha⟩
    have ha' : a' ≠ 1 := by
      intro he
      have he' : a = 1 := congrArg Subtype.val he
      exact hne (by rw [he', map_one])
    have ha2 : a ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) a')
    rw [← cover_fixed_image e hz a ha2]
    exact map_mono (le_iSup_of_le a' (le_iSup_of_le ha' le_rfl))
  have hsurj : Function.Surjective ((cover e).toMonoidHom.comp H.subtype) := by
    intro y
    obtain ⟨x, hx, he⟩ := (show y ∈ H.map (cover e).toMonoidHom from himage.symm ▸ mem_top _)
    exact ⟨⟨x, hx⟩, he⟩
  have hfull := surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    (cover e).toMonoidHom H.subtype hsurj (cover e).ker_le_center
  intro x _
  obtain ⟨y, rfl⟩ := hfull x
  exact y.property

/-- The intrinsic triple-A₆ calculation used in E.6.8(4). The quotient is
identified by the supplied equivalence, and the marked action is the literal
conjugation by the supplied transposition. -/
theorem six_cover_image_calculations
    (hz : Nonempty (center X ≃* Multiplicative (ZMod 3)))
    (e : (X ⧸ center X) ≃* alternatingGroup (Fin 6))
    (E : Subgroup (MulAut X)) [IsElementaryAbelian 2 E]
    (S : Sylow 2 X)
    (hfix : ∀ a ∈ E, ∀ x ∈ (S : Subgroup X), a x = x)
    (α : MulAut X) (_hα : α ∈ E)
    (σ : Equiv.Perm (Fin 6)) (_hσ : σ.IsSwap)
    (_haction : ∀ x : X,
      (e (QuotientGroup.mk' (center X) (α x)) : Equiv.Perm (Fin 6)) =
        σ * (e (QuotientGroup.mk' (center X) x) : Equiv.Perm (Fin 6)) * σ⁻¹) :
    Nat.card E ≤ 4 ∧ (Nat.card E = 4 →
      (⊤ : Subgroup X) ≤ ⨆ (a : E) (_ : a ≠ 1), fixedSubgroup (a : MulAut X)) :=
  ⟨six_cover_action_card_le_four e E S hfix,
    six_cover_fixedSubgroup_generation e hz E S hfix⟩

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions
