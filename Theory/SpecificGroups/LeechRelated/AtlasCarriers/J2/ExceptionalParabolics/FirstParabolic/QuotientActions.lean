module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.QuotientActions.BlockData

/-!
# The first Hall--Janko five-point quotient actions

The five sixteen-point blocks in `BlockData` define actual actions of the
literal centralizer `Seed.l₁` and the full outer numerator `Seed.l₁s`.
Compatibility with the block coloring is closed under products and inverses.
The certified generators `a,c,c⁻¹` therefore give the inner action through A₅;
adjoining the fixed outer word extends it to an S₅ action.

Sixty distinct word images exhaust A₅. The outer image also contains the
transposition induced by the outer word, so it exhausts S₅. Each fixed radical
generator fixes every color. Finally the numerator orders 1920 and 3840,
together with the explicit hypothesis `Nat.card radical = 32`, give the two
exact kernel equalities. No normality or quotient recognition is assumed.

The radical-order hypothesis is deliberately left to the separate radical
structure calculation. These maps supply the inputs of `QuotientReduction`;
the source-facing module retains assembly with the quaternion--dihedral factors
and the actual PSL₂(4) equivalence.

Source: Aschbacher--Smith F.1.12(I)(10)--(11), printed p.263 (PDF p.274),
and the retained ATLAS J2G1-p100B0 degree-100 permutation model.
-/

public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.QuotientActions
open Theory.GroupTheory GeneratorPair Seed
set_option maxRecDepth 4000

/-- Compatibility with the coloring of the eighty-point orbit. -/
@[expose] def Compatible (p : Equiv.Perm (Fin 100)) (q : Equiv.Perm (Fin 5)) : Prop :=
  ∀ x, color (p x) = (color x).map q

private theorem compatible_one : Compatible 1 1 := by
  intro x
  simp

private theorem compatible_mul {p r : Equiv.Perm (Fin 100)}
    {q s : Equiv.Perm (Fin 5)} (hp : Compatible p q) (hr : Compatible r s) :
    Compatible (p * r) (q * s) := by
  intro x
  rw [Equiv.Perm.mul_apply, hp, hr]
  cases color x <;> rfl

private theorem compatible_inv {p : Equiv.Perm (Fin 100)}
    {q : Equiv.Perm (Fin 5)} (hp : Compatible p q) : Compatible p⁻¹ q⁻¹ := by
  intro x
  have h := congrArg (Option.map (q⁻¹ : Equiv.Perm (Fin 5))) (hp (p⁻¹ x))
  simpa [Option.map_map, Function.comp_def] using h.symm

private theorem compatible_unique {p : Equiv.Perm (Fin 100)}
    {q r : Equiv.Perm (Fin 5)} (hq : Compatible p q) (hr : Compatible p r) : q = r := by
  apply Equiv.ext
  intro i
  have h := (hq (basePoint i)).symm.trans (hr (basePoint i))
  simpa only [color_basePoint, Option.map_some, Option.some.injEq] using h

/-- Permutations inducing an action on the five colors through `H`. -/
private def liftGroup (H : Subgroup (Equiv.Perm (Fin 5))) :
    Subgroup (Equiv.Perm (Fin 100)) where
  carrier := {p | ∃ q : H, Compatible p q.val}
  one_mem' := ⟨1, compatible_one⟩
  mul_mem' := by
    rintro p r ⟨q, hq⟩ ⟨s, hs⟩
    exact ⟨q * s, compatible_mul hq hs⟩
  inv_mem' := by
    rintro p ⟨q, hq⟩
    exact ⟨q⁻¹, compatible_inv hq⟩

private noncomputable def liftAction (H : Subgroup (Equiv.Perm (Fin 5))) :
    liftGroup H →* H where
  toFun p := Classical.choose p.property
  map_one' := Subtype.ext (compatible_unique (Classical.choose_spec (1 : liftGroup H).property)
    compatible_one)
  map_mul' p r := Subtype.ext (compatible_unique
    (Classical.choose_spec (p * r).property)
    (compatible_mul (Classical.choose_spec p.property) (Classical.choose_spec r.property)))

private theorem liftAction_spec (H : Subgroup (Equiv.Perm (Fin 5))) (p : liftGroup H) :
    Compatible p.val (liftAction H p).val := Classical.choose_spec p.property

private theorem letter_compatible (s : Fin 3) :
    Compatible (inclusion (FirstFusion.centralizerLetter s)) (letterPerm s) := by
  intro x
  rw [← FirstFusion.LocalCertificate.localLetterValue_eq]
  exact letter_color_check s x

private theorem inner_le_lift :
    l₁ ≤ (liftGroup (alternatingGroup (Fin 5))).comap inclusion := by
  change FirstFusion.centralizer ≤ _
  rw [FirstFusion.LocalCertificate.centralizer_eq_closure_letters]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨s, rfl⟩
  exact ⟨evenLetter s, letter_compatible s⟩

/-- The action of the literal first centralizer on its five blocks. -/
noncomputable def innerAction : l₁ →* alternatingGroup (Fin 5) :=
  (liftAction (alternatingGroup (Fin 5))).comp
    (inclusion.comp l₁.subtype |>.codRestrict _ (fun g => inner_le_lift g.property))

theorem innerAction_spec (g : l₁) :
    Compatible (inclusion g.val) (innerAction g).val :=
  liftAction_spec _ ⟨inclusion g.val, inner_le_lift g.property⟩

private theorem outerElement_compatible :
    Compatible (extension.subtype outerElement) outerPerm := by
  rw [SecondParabolic.outerElement_inclusion]
  exact outer_color_check

private theorem outer_le_lift : l₁s ≤ (liftGroup ⊤).comap extension.subtype := by
  rw [l₁s_eq_sup_outerElement]
  apply sup_le
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨(innerAction ⟨g, hg⟩).val, Subgroup.mem_top _⟩, innerAction_spec ⟨g, hg⟩⟩
  · apply Subgroup.zpowers_le.mpr
    exact ⟨⟨outerPerm, Subgroup.mem_top _⟩, outerElement_compatible⟩

/-- The five-block action of the source's full outer numerator. -/
noncomputable def outerAction : l₁s →* Equiv.Perm (Fin 5) :=
  (⊤ : Subgroup (Equiv.Perm (Fin 5))).subtype.comp ((liftAction ⊤).comp
    (extension.subtype.comp l₁s.subtype |>.codRestrict _ (fun g => outer_le_lift g.property)))

theorem outerAction_spec (g : l₁s) :
    Compatible (extension.subtype g.val) (outerAction g) :=
  liftAction_spec _ ⟨extension.subtype g.val, outer_le_lift g.property⟩

private def innerLetter (s : Fin 3) : l₁ :=
  ⟨FirstFusion.centralizerLetter s, FirstFusion.centralizerLetter_mem s⟩

private theorem innerAction_letter (s : Fin 3) : innerAction (innerLetter s) = evenLetter s :=
  Subtype.ext (compatible_unique (innerAction_spec _) (letter_compatible s))

private theorem innerAction_word (w : List (Fin 3)) :
    innerAction (evalWord innerLetter w) = evalWord evenLetter w := by
  induction w with
  | nil => exact map_one _
  | cons s w ih => rw [evalWord, map_mul, innerAction_letter, ih, evalWord]

theorem innerAction_surjective : Function.Surjective innerAction := by
  have hs := (imageRepresentative_injective.bijective_of_nat_card_le (by
    rw [nat_card_alternatingGroup, Nat.card_fin, Nat.card_fin]
    decide)).surjective
  intro g
  obtain ⟨i, rfl⟩ := hs g
  exact ⟨evalWord innerLetter (imageWord i), innerAction_word _⟩

/-- The actual carrier inclusion between the two source numerators. -/
def numeratorInclusion : l₁ →* l₁s :=
  (intoExtension.comp l₁.subtype).codRestrict _ (fun g =>
    (le_sup_left : outerL 0 ≤ l₁s) (Subgroup.mem_map_of_mem intoExtension g.property))

theorem outerAction_numeratorInclusion (g : l₁) :
    outerAction (numeratorInclusion g) = (innerAction g).val :=
  compatible_unique (outerAction_spec _) (innerAction_spec g)

private def outerGenerator : l₁s := ⟨outerElement, by
  rw [l₁s_eq_sup_outerElement]
  exact (le_sup_right : Subgroup.zpowers outerElement ≤
    outerL 0 ⊔ Subgroup.zpowers outerElement) (Subgroup.mem_zpowers outerElement)⟩

private theorem outerAction_generator : outerAction outerGenerator = outerPerm :=
  compatible_unique (outerAction_spec _) outerElement_compatible

theorem outerAction_surjective : Function.Surjective outerAction := by
  have he (q : Equiv.Perm (Fin 5)) (hq : q ∈ alternatingGroup (Fin 5)) :
      ∃ g, outerAction g = q := by
    obtain ⟨g, hg⟩ := innerAction_surjective ⟨q, hq⟩
    exact ⟨numeratorInclusion g, (outerAction_numeratorInclusion g).trans
      (congrArg Subtype.val hg)⟩
  intro q
  by_cases hq : q ∈ alternatingGroup (Fin 5)
  · exact he q hq
  · have hodd : outerPerm ∉ alternatingGroup (Fin 5) := by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    have hprod : q * outerPerm ∈ alternatingGroup (Fin 5) :=
      ((alternatingGroup (Fin 5)).mul_mem_iff_of_index_two
        alternatingGroup.index_eq_two).mpr (iff_of_false hq hodd)
    obtain ⟨g, hg⟩ := he _ hprod
    refine ⟨g * outerGenerator, ?_⟩
    rw [map_mul, hg, outerAction_generator, mul_assoc]
    have hsq : outerPerm * outerPerm = 1 := by decide +kernel
    rw [hsq, mul_one]

private theorem radicalPerm_spec (i : Fin 4) : inclusion (radicalGenerator i) = radicalPerm i := by
  have h (w : List (Fin 7)) :
      inclusion (evalWord sGenerator w) = evalWord PairNormalizer.SylowData.sGenTable w := by
    induction w with
    | nil => exact map_one _
    | cons s w ih => rw [evalWord, map_mul, PairNormalizer.sGenerator_inclusion, ih, evalWord]
  exact h _

private theorem radical_le_trivial_lift : radical ≤ (liftGroup ⊥).comap inclusion := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨1, ?_⟩
  rw [radicalPerm_spec]
  intro x
  simpa using radical_color_check i x

private theorem radical_compatible (g : Carrier) (hg : g ∈ radical) :
    Compatible (inclusion g) 1 := by
  obtain ⟨q, hq⟩ := radical_le_trivial_lift hg
  have hq1 : q.val = 1 := q.property
  simpa only [hq1] using hq

theorem radical_le_innerAction_ker : radical.subgroupOf l₁ ≤ innerAction.ker := by
  intro g hg
  apply Subtype.ext
  exact compatible_unique (innerAction_spec g) (radical_compatible g.val hg)

theorem outerRadical_le_outerAction_ker : outerRadical.subgroupOf l₁s ≤ outerAction.ker := by
  rintro g ⟨x, hx, hxg⟩
  change outerAction g = 1
  apply compatible_unique (outerAction_spec g)
  change intoExtension x = g.val at hxg
  rw [← hxg]
  exact radical_compatible x hx

private theorem card_ker_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card f.ker * Nat.card H = Nat.card G := by
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at h
  exact h

/-- Kernel equality needs only the separate order calculation for the fixed radical. -/
theorem innerAction_ker (hcard : Nat.card radical = 32) :
    innerAction.ker = radical.subgroupOf l₁ := by
  apply (Subgroup.eq_of_le_of_card_ge radical_le_innerAction_ker _).symm
  have hk := card_ker_of_surjective innerAction innerAction_surjective
  rw [nat_card_alternatingGroup, Nat.card_fin, card_l₁] at hk
  have hr : Nat.card (radical.subgroupOf l₁) = 32 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe radical_le_l₁).toEquiv).trans hcard
  rw [hr]
  change Nat.card innerAction.ker * 60 = 1920 at hk
  omega

/-- The outer action has exactly the same fixed radical, included in the extension. -/
theorem outerAction_ker (hcard : Nat.card radical = 32) :
    outerAction.ker = outerRadical.subgroupOf l₁s := by
  apply (Subgroup.eq_of_le_of_card_ge outerRadical_le_outerAction_ker _).symm
  have hk := card_ker_of_surjective outerAction outerAction_surjective
  rw [Nat.card_perm, Nat.card_fin, card_l₁s] at hk
  have hr : Nat.card (outerRadical.subgroupOf l₁s) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe outerRadical_le_l₁s).toEquiv,
      outerRadical, Subgroup.card_map_of_injective SecondParabolic.intoExtension_injective,
      hcard]
  rw [hr]
  change Nat.card outerAction.ker * 120 = 3840 at hk
  omega

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.QuotientActions
