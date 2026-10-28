module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore
public import Theory.SpecificGroups.FFLinearPrimeCore
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Selecting and marking the two-factor FF alternative

Two distinct ordinary components and full commutator generation select the
complete B.5.6(3) alternative. The trivial, quasisimple, S₃ and outer A₆–C₃
actors have at most one component. The hyperplane alternative contradicts
full commutator generation. For the product alternative, each concrete factor
has at most one component: SL₂ is simple or solvable, SL₃ is quasisimple,
and perfectness puts the components of S₅ in A₅.

Surjective product projections carry a component to a component or to the
identity. Distinct components cannot have the same nontrivial image, so the
two original components occupy separate factors. The product equivalence
then recovers their literal inclusions. Exchanging the factors exchanges
both subrepresentations and their complete source action data as well.

The genuine B.5.3 hypothesis and the complete classification alternative are
explicit inputs. In the source application, `FFFactors.OrbitActor` and
`FFFactors.SourceOrbit` supply the original component images in the offender
actor. The assembly of 13.8.16 and the recognition of the marked modules
remain with the parent; this module proves its branch and placement deduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3 and
B.5.6, printed pp.104–105, and proof of 13.8.16(1), case (a), printed p.952
(PDF p.969). The imported concrete model results retain their ATLAS attribution.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.ClassifiedGroups
universe u v
variable {G H : Type*} [Group G] [Group H]

private theorem component_ne_bot {A : Subgroup G} (hA : IsComponent G A) : A ≠ ⊥ := by
  let := hA.2
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  exact (nontrivial_iff_ne_bot A).mp inferInstance

private theorem no_component_of_solvable [Group.IsSolvable G]
    {A : Subgroup G} (hA : IsComponent G A) : False := by
  let := hA.2
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr (component_ne_bot hA)
  exact Group.IsPerfect.not_isSolvable A inferInstance

private theorem perfect_image_bot [Group.IsSolvable H]
    (A : Subgroup G) [Group.IsPerfect A] (f : G →* H) : A.map f = ⊥ := by
  let : Group.IsPerfect (A.map f) := Group.IsPerfect.map f
  by_contra h
  let : Nontrivial (A.map f) := (nontrivial_iff_ne_bot _).mpr h
  exact Group.IsPerfect.not_isSolvable (A.map f) inferInstance

private def UniqueComponents (G : Type*) [Group G] : Prop :=
  ∀ (A B : Subgroup G), IsComponent G A → IsComponent G B → A = B

private theorem unique_of_simple [IsSimpleGroup G] : UniqueComponents G := by
  intro A B hA hB
  have hAt := hA.1.eq_bot_or_top_of_isSimpleGroup (inferInstance : IsSimpleGroup G)
  have hBt := hB.1.eq_bot_or_top_of_isSimpleGroup (inferInstance : IsSimpleGroup G)
  exact (hAt.resolve_left (component_ne_bot hA)).trans
    (hBt.resolve_left (component_ne_bot hB)).symm

private theorem unique_of_quasisimple [IsQuasisimple G] : UniqueComponents G := by
  intro A B hA hB
  have ht : IsComponent G ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv (topEquiv).symm⟩
  exact (hA.eq_of_le ht le_top).trans (hB.eq_of_le ht le_top).symm

private theorem unique_of_equiv (e : G ≃* H) (hH : UniqueComponents H) :
    UniqueComponents G := by
  intro A B hA hB
  exact Subgroup.map_injective e.injective (hH _ _ (hA.map_equiv e) (hB.map_equiv e))

private theorem unique_of_overgroup {N : Subgroup G} (hN : UniqueComponents N)
    {A B : Subgroup G} (hA : IsComponent G A) (hB : IsComponent G B)
    (ha : A ≤ N) (hb : B ≤ N) : A = B := by
  have h := congrArg (Subgroup.map N.subtype)
    (hN _ _ (hA.subgroupOf ha) (hB.subgroupOf hb))
  simpa only [map_subgroupOf_eq_of_le ha, map_subgroupOf_eq_of_le hb] using h

private theorem unique_of_solvable_quotient (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] (hN : UniqueComponents N) : UniqueComponents G := by
  intro A B hA hB
  let := hA.2
  let := hB.2
  exact unique_of_overgroup hN hA hB
    (le_of_isPerfect_of_solvable_quotient A N) (le_of_isPerfect_of_solvable_quotient B N)

private theorem ne_bot_projection {A : Subgroup (G × H)} (hA : IsComponent (G × H) A)
    (hf : A.map (MonoidHom.fst G H) = ⊥) : A.map (MonoidHom.snd G H) ≠ ⊥ := by
  intro hs
  apply component_ne_bot hA
  apply eq_bot_iff.mpr
  intro x hx
  apply Prod.ext
  · exact mem_bot.mp (hf ▸ mem_map_of_mem (MonoidHom.fst G H) hx)
  · exact mem_bot.mp (hs ▸ mem_map_of_mem (MonoidHom.snd G H) hx)

private theorem eq_of_nontrivial_projection (hG : UniqueComponents G)
    {A B : Subgroup (G × H)} (hA : IsComponent (G × H) A)
    (hB : IsComponent (G × H) B)
    (ha : A.map (MonoidHom.fst G H) ≠ ⊥) (hb : B.map (MonoidHom.fst G H) ≠ ⊥) :
    A = B := by
  have hf : Function.Surjective (MonoidHom.fst G H) := fun x => ⟨(x, 1), rfl⟩
  exact hA.eq_of_map_eq hB _
    (hG _ _ ((hA.map_surjective _ hf).resolve_left ha)
      ((hB.map_surjective _ hf).resolve_left hb)) ha

private theorem unique_prod_solvable [Group.IsSolvable H]
    (hG : UniqueComponents G) : UniqueComponents (G × H) := by
  intro A B hA hB
  let := hA.2
  let := hB.2
  have ha := perfect_image_bot A (MonoidHom.snd G H)
  have hb := perfect_image_bot B (MonoidHom.snd G H)
  apply eq_of_nontrivial_projection hG hA hB
  · intro he
    exact ne_bot_projection hA he ha
  · intro he
    exact ne_bot_projection hB he hb

private theorem alternating_unique (n : ℕ) (hn : 5 ≤ n) :
    UniqueComponents (alternatingGroup (Fin n)) := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa)
  exact unique_of_simple

private theorem symmetric_five_unique : UniqueComponents (Equiv.Perm (Fin 5)) := by
  intro A B hA hB
  let := hA.2
  let := hB.2
  exact unique_of_overgroup (alternating_unique 5 le_rfl) hA hB
    (le_of_isPerfect_of_index_eq_two A _ alternatingGroup.index_eq_two)
    (le_of_isPerfect_of_index_eq_two B _ alternatingGroup.index_eq_two)

private theorem symmetric_three_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

private theorem sl_two_small_solvable (F : BinaryField) (hF : Nat.card F.Carrier = 2) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) := by
  classical
  let : Fintype F.Carrier := Fintype.ofFinite _
  let : FaithfulSMul (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) (Fin 2 → F.Carrier) := ⟨by
    intro a b h
    apply Subtype.ext
    exact Matrix.ext_iff_mulVec.mpr h⟩
  let e : (Fin 2 → F.Carrier) ≃ Fin 4 := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hF]
    rfl)
  let f : Matrix.SpecialLinearGroup (Fin 2) F.Carrier →* Equiv.Perm (Fin 4) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom _ _)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective
    (f := f) (e.permCongrHom.injective.comp MulAction.toPerm_injective)

-- Only the intrinsic model facts used by the component argument are needed.
private theorem factor_unique (h : FactorModel G) : UniqueComponents G := by
  cases h with
  | linearTwo F e =>
    apply unique_of_equiv e
    by_cases hc : Nat.card F.Carrier = 2
    · let := sl_two_small_solvable F hc
      intro A B hA _
      exact (no_component_of_solvable hA).elim
    · have hfour : 4 ≤ Nat.card F.Carrier := by
        have ht := Finite.one_lt_card (α := F.Carrier)
        let := Fintype.ofFinite F.Carrier
        have hd : 2 ∣ Nat.card F.Carrier := by
          rw [Nat.card_eq_fintype_card]
          exact (CharP.cast_eq_zero_iff F.Carrier 2 _).mp (Nat.cast_card_eq_zero F.Carrier)
        omega
      let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F.Carrier) hfour
      let q : Matrix.SpecialLinearGroup (Fin 2) F.Carrier ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier :=
        ((QuotientGroup.quotientMulEquivOfEq
          Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans QuotientGroup.quotientBot).symm
      exact unique_of_equiv q unique_of_simple
  | symmetricFive e => exact unique_of_equiv e symmetric_five_unique
  | linearThree F _ e =>
    let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
      { toIsPerfect := Atlas.sl_perfect 3 (by decide)
        simple := Atlas.psl_simple_high_rank 3 (by decide) }
    exact unique_of_equiv e unique_of_quasisimple

-- Nontrivial projections of two distinct components cannot occupy the same factor.
private theorem product_separate (hG : UniqueComponents G) (hH : UniqueComponents H)
    {A B : Subgroup (G × H)} (hA : IsComponent (G × H) A)
    (hB : IsComponent (G × H) B) (hne : A ≠ B) :
    (A.map (MonoidHom.fst G H) = ⊥ ∧ B.map (MonoidHom.snd G H) = ⊥) ∨
    (A.map (MonoidHom.snd G H) = ⊥ ∧ B.map (MonoidHom.fst G H) = ⊥) := by
  have heq (ha : A.map (MonoidHom.snd G H) ≠ ⊥)
      (hb : B.map (MonoidHom.snd G H) ≠ ⊥) : A = B := by
    have hs : Function.Surjective (MonoidHom.snd G H) := fun x => ⟨(1, x), rfl⟩
    exact hA.eq_of_map_eq hB _
      (hH _ _ ((hA.map_surjective _ hs).resolve_left ha)
        ((hB.map_surjective _ hs).resolve_left hb)) ha
  by_cases ha : A.map (MonoidHom.fst G H) = ⊥
  · left
    refine ⟨ha, ?_⟩
    by_contra hb
    exact hne (heq (ne_bot_projection hA ha) hb)
  · right
    have hb : B.map (MonoidHom.fst G H) = ⊥ := by
      by_contra hb
      exact hne (eq_of_nontrivial_projection hG hA hB ha hb)
    refine ⟨?_, hb⟩
    by_contra ha'
    exact hne (heq ha' (ne_bot_projection hB hb))

private theorem internal_separate {X Y A B : Subgroup G}
    (p : InternalProduct X Y) (hX : UniqueComponents X) (hY : UniqueComponents Y)
    (hA : IsComponent G A) (hB : IsComponent G B) (hne : A ≠ B) :
    (A ≤ X ∧ B ≤ Y) ∨ (A ≤ Y ∧ B ≤ X) := by
  have hfst (L : Subgroup G)
      (h : (L.map p.equiv.symm.toMonoidHom).map (MonoidHom.fst X Y) = ⊥) : L ≤ Y := by
    intro x hx
    have hh : (p.equiv.symm x).1 = 1 := mem_bot.mp
      (h ▸ mem_map_of_mem (MonoidHom.fst X Y) (mem_map_of_mem p.equiv.symm.toMonoidHom hx))
    have he := p.apply_eq (p.equiv.symm x).1 (p.equiv.symm x).2
    change p.equiv (p.equiv.symm x) = _ at he
    rw [p.equiv.apply_symm_apply, hh, coe_one, one_mul] at he
    exact he ▸ (p.equiv.symm x).2.property
  have hsnd (L : Subgroup G)
      (h : (L.map p.equiv.symm.toMonoidHom).map (MonoidHom.snd X Y) = ⊥) : L ≤ X := by
    intro x hx
    have hh : (p.equiv.symm x).2 = 1 := mem_bot.mp
      (h ▸ mem_map_of_mem (MonoidHom.snd X Y) (mem_map_of_mem p.equiv.symm.toMonoidHom hx))
    have he := p.apply_eq (p.equiv.symm x).1 (p.equiv.symm x).2
    change p.equiv (p.equiv.symm x) = _ at he
    rw [p.equiv.apply_symm_apply, hh, coe_one, mul_one] at he
    exact he ▸ (p.equiv.symm x).1.property
  rcases product_separate hX hY (hA.map_equiv p.equiv.symm) (hB.map_equiv p.equiv.symm)
      (fun h => hne (Subgroup.map_injective p.equiv.symm.injective h)) with h | h
  · exact Or.inr ⟨hfst A h.1, hsnd B h.2⟩
  · exact Or.inl ⟨hsnd A h.1, hfst B h.2⟩

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

-- Perfectness kills the cyclic quotient and the solvable C₃ projection.
private theorem outer_unique (c : OuterSixThreeCase ρ) : UniqueComponents D := by
  let := c.product_normal ρ
  let := c.quotient_isCyclic ρ
  let := IsCyclic.commGroup (α := D ⧸ (c.first ⊔ c.second))
  apply unique_of_solvable_quotient (c.first ⊔ c.second)
  apply unique_of_equiv c.product.symm
  let : Group.IsSolvable c.second := Group.isSolvable_of_isSolvable_injective
    (f := c.secondEquiv.toMonoidHom) c.secondEquiv.injective
  exact unique_prod_solvable (unique_of_equiv c.firstEquiv (alternating_unique 6 (by decide)))

/-- Exchange the complete classified group and module data together. -/
def exchange (c : SourceTwoFactorCase ρ) : SourceTwoFactorCase ρ where
  first := c.second
  second := c.first
  product := {
    equiv := MulEquiv.prodComm.trans c.product.equiv
    apply_eq := by
      intro b a
      change c.product.equiv (a, b) = (b : D) * (a : D)
      rw [c.product.apply_eq]
      have h := congrArg c.product.equiv
        (show (a, (1 : c.second)) * (1, b) = (1, b) * (a, 1) by ext <;> simp)
      simp only [map_mul] at h
      simpa only [c.product.apply_eq, coe_one, mul_one, one_mul] using h }
  firstSpace := c.secondSpace
  secondSpace := c.firstSpace
  decomposition := c.decomposition.symm
  firstCase := c.secondCase
  secondCase := c.firstCase

/-- Two distinct components generating the whole moved module select B.5.6(3).
The factors retain the original component inclusions. -/
theorem exists_marked_twoFactorCase [Finite D] {K : GroupClass.{u}}
    (_hyp : FFHypothesis K ρ) (hclass : SourceAlternative ρ)
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B)
    (hfull : Representation.BinaryOffender.subspaceCommutator ρ ⊤ (A ⊔ B) = ⊤) :
    ∃ c : SourceTwoFactorCase ρ, A ≤ c.first ∧ B ≤ c.second := by
  cases hclass with
  | trivial ht =>
    let := ht
    exact (component_ne_bot hA (Subsingleton.elim _ _)).elim
  | quasisimple hq _ =>
    let := hq
    exact (hne (unique_of_overgroup unique_of_quasisimple hA hB
      (component_le_generalizedFitting D A hA) (component_le_generalizedFitting D B hB))).elim
  | symmetricThree c =>
    let := symmetric_three_solvable
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom) c.equiv.injective
    exact (no_component_of_solvable hA).elim
  | twoFactors c =>
    rcases internal_separate c.product (factor_unique (c.firstCase.factorModel ρ))
        (factor_unique (c.secondCase.factorModel ρ)) hA hB hne with h | h
    · exact ⟨c, h⟩
    · exact ⟨exchange ρ c, h.1, h.2⟩
  | outerSixThree c => exact (hne (outer_unique ρ c A B hA hB)).elim
  | hyperplane c =>
    have hm : moved ρ ⊤ = ⊤ := by
      apply top_unique
      rw [← hfull]
      apply Submodule.span_mono
      rintro _ ⟨g, _, v, hv, rfl⟩
      exact ⟨g, mem_top _, v, hv, rfl⟩
    have hc := c.hyperplane
    rw [hm, top_sup_eq] at hc
    have hz : Module.finrank (ZMod 2) (V ⧸ (⊤ : Submodule (ZMod 2) V)) = 0 :=
      Module.finrank_zero_of_subsingleton
    omega

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.ClassifiedGroups
