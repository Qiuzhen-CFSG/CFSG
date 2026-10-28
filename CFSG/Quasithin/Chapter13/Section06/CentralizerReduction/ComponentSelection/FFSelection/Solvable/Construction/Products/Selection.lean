module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection.ProductBranches.Factors
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.GroupTheory.NormalSymmetricThreeMarked

/-!
# Selecting the cubic residuals in the native B.5.6 product alternatives

A normal solvable two-perfect subgroup has trivial projection to each
nonsolvable source factor. In an S₃ factor its projection is either trivial
or the cubic residual, and in both cases it equals its commutator with the
factor. Commuting against each coordinate separately then rules out all
diagonals. The nontrivial subgroup therefore selects one S₃ residual or both.
The hyperplane branch selects only its second factor, because SL₃(2) has
order 168.

The native Chapter B action isomorphisms determine the actual group models.
The field adapter changes the record type while keeping its carrier and
all instances. No legacy universal classification implication is used.
The quotient-space and hyperplane module clauses are not needed for this
group step and remain obligations of the support construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3),(5), printed p.105, and the first construction in 13.6.13, p.929.
-/

@[expose] public section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.ProductBranches
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives (FactorModel)
variable {D E : Type*} [Group D] [Group E]

private theorem residual_card (e : D ≃* Equiv.Perm (Fin 3)) : Nat.card (pResidual 2 D) = 3 := by
  rw [← card_map_of_injective (K := pResidual 2 D) (f := e.toMonoidHom) e.injective, map_pResidual,
    Equiv.Perm.twoResidual_eq_alternating, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem residual_commutator (e : D ≃* Equiv.Perm (Fin 3)) :
    ⁅pResidual 2 D, (⊤ : Subgroup D)⁆ = pResidual 2 D := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_commutator, map_pResidual, map_top_of_surjective _ e.surjective,
    Equiv.Perm.twoResidual_eq_alternating]
  apply le_antisymm (commutator_le_left _ _) _
  intro x hx
  have he : ∀ x : Equiv.Perm (Fin 3), x ∈ alternatingGroup (Fin 3) →
      ∃ a : Equiv.Perm (Fin 3), a ∈ alternatingGroup (Fin 3) ∧
        ∃ b : Equiv.Perm (Fin 3), ⁅a, b⁆ = x := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  obtain ⟨a, ha, b, rfl⟩ := he x hx
  exact commutator_mem_commutator ha (mem_top b)

/-- A solvable normal two-perfect subgroup of a source factor is trivial,
or is exactly the cubic residual of an actual S₃ factor. -/
theorem factor_solvable_residual [Finite D] (hD : FactorModel D)
    (A : Subgroup D) [A.Normal] (hs : Group.IsSolvable A) (hp : IsPPerfect 2 A) :
    A = ⊥ ∨ (Nonempty (D ≃* Equiv.Perm (Fin 3)) ∧ A = pResidual 2 D) := by
  rcases factor_structure hD with he | ⟨_, _, h⟩
  · obtain ⟨e⟩ := he
    by_cases hb : A = ⊥
    · exact Or.inl hb
    · right
      have hle := le_pResidual_of_isPPerfect A hp
      have hd : Nat.card A ∣ 3 := residual_card e ▸ card_dvd_of_le hle
      have hc : Nat.card A = 3 := (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left
        (fun hc => hb (card_eq_one.mp hc))
      exact ⟨⟨e⟩, eq_of_le_of_card_ge hle (by rw [residual_card e, hc])⟩
  · exact Or.inl (h A inferInstance hs)

private theorem factor_commutator [Finite D] (hD : FactorModel D)
    (A : Subgroup D) [A.Normal] (hs : Group.IsSolvable A) (hp : IsPPerfect 2 A) :
    ⁅A, (⊤ : Subgroup D)⁆ = A := by
  rcases factor_solvable_residual hD A hs hp with rfl | ⟨⟨e⟩, rfl⟩
  · exact commutator_bot_left _
  · exact residual_commutator e

private theorem fst_axis_le (A : Subgroup (D × E)) [A.Normal]
    (hc : ⁅A.map (MonoidHom.fst D E), (⊤ : Subgroup D)⁆ = A.map (MonoidHom.fst D E)) :
    (A.map (MonoidHom.fst D E)).map (MonoidHom.inl D E) ≤ A := by
  let B : Subgroup (D × E) := (⊤ : Subgroup D).prod ⊥
  have hm : B.map (MonoidHom.fst D E) = ⊤ := by
    apply top_unique
    intro d _
    exact ⟨(d, 1), ⟨mem_top _, rfl⟩, rfl⟩
  have hC : (⁅A, B⁆).map (MonoidHom.fst D E) = A.map (MonoidHom.fst D E) := by
    rw [map_commutator, hm, hc]
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨⟨x, y⟩, hxy, he⟩ := hC.symm ▸ hd
  have hy : y = 1 := (commutator_le_right A B hxy).2
  have hh := commutator_le_left A B hxy
  change x = d at he
  change (d, 1) ∈ A
  simpa only [hy, he] using hh

private theorem snd_axis_le (A : Subgroup (D × E)) [A.Normal]
    (hc : ⁅A.map (MonoidHom.snd D E), (⊤ : Subgroup E)⁆ = A.map (MonoidHom.snd D E)) :
    (A.map (MonoidHom.snd D E)).map (MonoidHom.inr D E) ≤ A := by
  let B : Subgroup (D × E) := (⊥ : Subgroup D).prod ⊤
  have hm : B.map (MonoidHom.snd D E) = ⊤ := by
    apply top_unique
    intro d _
    exact ⟨(1, d), ⟨rfl, mem_top _⟩, rfl⟩
  have hC : (⁅A, B⁆).map (MonoidHom.snd D E) = A.map (MonoidHom.snd D E) := by
    rw [map_commutator, hm, hc]
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨⟨x, y⟩, hxy, he⟩ := hC.symm ▸ hd
  have hx : x = 1 := (commutator_le_right A B hxy).1
  have hh := commutator_le_left A B hxy
  change y = d at he
  change (1, d) ∈ A
  simpa only [hx, he] using hh

/-- Normality eliminates every diagonal: the subgroup is the product of its
actual projections, with no irreducibility or transitivity assumption. -/
theorem solvable_product_projections [Finite D] [Finite E]
    (hD : FactorModel D) (hE : FactorModel E)
    (A : Subgroup (D × E)) [A.Normal] (hs : Group.IsSolvable A) (hp : IsPPerfect 2 A) :
    A = (A.map (MonoidHom.fst D E)).prod (A.map (MonoidHom.snd D E)) := by
  let := hs
  have hf : Function.Surjective (MonoidHom.fst D E) := Prod.fst_surjective
  have hg : Function.Surjective (MonoidHom.snd D E) := Prod.snd_surjective
  let : (A.map (MonoidHom.fst D E)).Normal := (inferInstance : A.Normal).map _ hf
  let : (A.map (MonoidHom.snd D E)).Normal := (inferInstance : A.Normal).map _ hg
  have hs₁ := Group.isSolvable_of_surjective ((MonoidHom.fst D E).subgroupMap_surjective A)
  have hs₂ := Group.isSolvable_of_surjective ((MonoidHom.snd D E).subgroupMap_surjective A)
  have hp₁ := hp.of_surjective _ ((MonoidHom.fst D E).subgroupMap_surjective A)
  have hp₂ := hp.of_surjective _ ((MonoidHom.snd D E).subgroupMap_surjective A)
  apply le_antisymm (le_prod_iff.mpr ⟨le_rfl, le_rfl⟩)
  exact prod_le_iff.mpr ⟨fst_axis_le A (factor_commutator hD _ hs₁ hp₁),
    snd_axis_le A (factor_commutator hE _ hs₂ hp₂)⟩

/-- The three possible choices, on the literal internal factor inclusions.
The full choice uses the intrinsic two-residual of the whole actor. -/
def ResidualChoice (A B X : Subgroup D) : Prop :=
  (Nonempty (A ≃* Equiv.Perm (Fin 3)) ∧ X = (pResidual 2 A).map A.subtype) ∨
  (Nonempty (B ≃* Equiv.Perm (Fin 3)) ∧ X = (pResidual 2 B).map B.subtype) ∨
  (Nonempty (A ≃* Equiv.Perm (Fin 3)) ∧ Nonempty (B ≃* Equiv.Perm (Fin 3)) ∧
    X = pResidual 2 D)

private theorem product_residual :
    pResidual 2 (D × E) = (pResidual 2 D).prod (pResidual 2 E) := by
  apply le_antisymm
  · exact le_prod_iff.mpr ⟨map_pResidual_le 2 (MonoidHom.fst D E),
      map_pResidual_le 2 (MonoidHom.snd D E)⟩
  · exact prod_le_iff.mpr ⟨map_pResidual_le 2 (MonoidHom.inl D E),
      map_pResidual_le 2 (MonoidHom.inr D E)⟩

private theorem internal_prod_map {A B : Subgroup D} (h : InternalProduct A B)
    (R : Subgroup A) (S : Subgroup B) :
    (R.prod S).map h.equiv.toMonoidHom = R.map A.subtype ⊔ S.map B.subtype := by
  apply le_antisymm
  · rintro _ ⟨⟨a,b⟩, hab, rfl⟩
    change h.equiv (a,b) ∈ _
    rw [h.apply_eq]
    exact (R.map A.subtype ⊔ S.map B.subtype).mul_mem
      ((le_sup_left : R.map A.subtype ≤ R.map A.subtype ⊔ S.map B.subtype)
        (mem_map_of_mem A.subtype hab.1))
      ((le_sup_right : S.map B.subtype ≤ R.map A.subtype ⊔ S.map B.subtype)
        (mem_map_of_mem B.subtype hab.2))
  · apply sup_le
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨(a,1), ⟨ha, S.one_mem⟩, by simp [h.apply_eq]⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact ⟨(1,b), ⟨R.one_mem, hb⟩, by simp [h.apply_eq]⟩

/-- A nontrivial solvable normal two-perfect subgroup selects either one
actual S₃ residual, or both. The proof rules out diagonals by commutators. -/
theorem internal_solvable_choice [Finite D] {A B : Subgroup D}
    (h : InternalProduct A B) (hA : FactorModel A) (hB : FactorModel B)
    (X : Subgroup D) [X.Normal] (hs : Group.IsSolvable X)
    (hp : IsPPerfect 2 X) (hne : X ≠ ⊥) : ResidualChoice A B X := by
  let := hs
  let Y := X.map h.equiv.symm.toMonoidHom
  let f := MonoidHom.fst A B
  let g := MonoidHom.snd A B
  let : Y.Normal := (inferInstance : X.Normal).map _ h.equiv.symm.surjective
  let : Group.IsSolvable Y :=
    Group.isSolvable_of_surjective (h.equiv.symm.toMonoidHom.subgroupMap_surjective X)
  have hYp : IsPPerfect 2 Y := hp.of_surjective _
    (h.equiv.symm.toMonoidHom.subgroupMap_surjective X)
  have hXY : Y.map h.equiv.toMonoidHom = X := by
    simp [Y, map_map]
  have hY := solvable_product_projections hA hB Y inferInstance hYp
  let : (Y.map f).Normal := (inferInstance : Y.Normal).map f Prod.fst_surjective
  let : (Y.map g).Normal := (inferInstance : Y.Normal).map g Prod.snd_surjective
  have hf := factor_solvable_residual hA (Y.map f)
    (Group.isSolvable_of_surjective (f.subgroupMap_surjective Y))
    (hYp.of_surjective _ (f.subgroupMap_surjective Y))
  have hg := factor_solvable_residual hB (Y.map g)
    (Group.isSolvable_of_surjective (g.subgroupMap_surjective Y))
    (hYp.of_surjective _ (g.subgroupMap_surjective Y))
  change Y = (Y.map f).prod (Y.map g) at hY
  have hx : X = (Y.map f).map A.subtype ⊔ (Y.map g).map B.subtype := by
    calc
      X = Y.map h.equiv.toMonoidHom := hXY.symm
      _ = ((Y.map f).prod (Y.map g)).map h.equiv.toMonoidHom := congrArg _ hY
      _ = _ := internal_prod_map h _ _
  rcases hf with hf | ⟨heA, hf⟩
  · rcases hg with hg | ⟨heB, hg⟩
    · exfalso
      apply hne
      simpa only [hf, hg, Subgroup.map_bot, bot_sup_eq] using hx
    · exact Or.inr (Or.inl ⟨heB, by simpa only [hf, hg, Subgroup.map_bot, bot_sup_eq] using hx⟩)
  · rcases hg with hg | ⟨heB, hg⟩
    · exact Or.inl ⟨heA, by simpa only [hf, hg, Subgroup.map_bot, sup_bot_eq] using hx⟩
    · refine Or.inr (Or.inr ⟨heA, heB, ?_⟩)
      rw [← hXY, hY, hf, hg, ← product_residual, map_pResidual]

private def modelField (F : ChapterB.QuasisimpleSource.BinaryField) :
    Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField where
  Carrier := F.Carrier
  degree := F.degree
  degree_pos := F.degree_pos
  card_eq := F.card_eq

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)

/-- Extract models from the native Chapter B contract and its actual action
isomorphisms; no legacy classification implication is used. -/
theorem sourceFactor_model {F : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ F U) : FactorModel F := by
  cases h with
  | natural _ h =>
    cases h with
    | linearTwo F h => exact .linearTwo (modelField F) h.some.groupEquiv
    | symmetricFive h => exact .symmetricFive h.some.groupEquiv
    | linearThree F ho h => exact .linearThree (modelField F) ho h.some.groupEquiv
  | doubleNatural F ho _ h => exact .linearThree (modelField F) ho h.some.groupEquiv
  | exceptional _ h => exact .linearThree (modelField ChapterB.QuasisimpleSource.BinaryField.two) (by decide) h.natural.groupEquiv

/-- The second hyperplane factor retains its own central quotient convention. -/
theorem hyperplaneSecond_model {F : Subgroup D} {U : Subrepresentation ρ}
    (h : HyperplaneSecondCase ρ F U) : FactorModel F := by
  cases h with
  | linearThree _ _ h => exact .linearThree (modelField ChapterB.QuasisimpleSource.BinaryField.two) (by decide) h.some.groupEquiv
  | linearTwo F h => exact .linearTwo (modelField F) h.some.groupEquiv

/-- Coordinate selection from all clauses of native B.5.6(3). Only the
actor isomorphisms are used in this group step; the quotient-space clauses
remain available for construction of the supports. -/
theorem twoFactor_solvable_choice [Finite D] (c : SourceTwoFactorCase ρ)
    (X : Subgroup D) [X.Normal] (hs : Group.IsSolvable X)
    (hp : IsPPerfect 2 X) (hne : X ≠ ⊥) : ResidualChoice c.first c.second X :=
  internal_solvable_choice c.product (sourceFactor_model ρ c.firstCase)
    (sourceFactor_model ρ c.secondCase) X hs hp hne

/-- B.5.6(5)'s SL₃(2) factor cannot support any part of X. The second
factor is S₃, and its embedded cubic residual is exactly X. -/
theorem hyperplane_solvable_choice [Finite D] (c : HyperplaneCase ρ)
    (X : Subgroup D) [X.Normal] (hs : Group.IsSolvable X)
    (hp : IsPPerfect 2 X) (hne : X ≠ ⊥) :
    Nonempty (c.second ≃* Equiv.Perm (Fin 3)) ∧
      X = (pResidual 2 c.second).map c.second.subtype := by
  have hfirst : ¬ Nonempty (c.first ≃* Equiv.Perm (Fin 3)) := by
    rintro ⟨e⟩
    have hc : Nat.card c.first = 168 :=
      (Nat.card_congr c.firstEquiv.toEquiv).trans Matrix.PSL3Two.card_SL
    have hd : Nat.card c.first = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      decide
    omega
  have hh := internal_solvable_choice c.product
    (.linearThree (modelField ChapterB.QuasisimpleSource.BinaryField.two) (by decide)
      c.firstEquiv) (hyperplaneSecond_model ρ c.secondCase) X hs hp hne
  rcases hh with h | h | h
  · exact (hfirst h.1).elim
  · exact h
  · exact (hfirst h.1).elim

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
