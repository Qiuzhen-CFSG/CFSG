module

public import Theory.Representation.SixLetterRadicalDisplacement

/-!
# Radical fixers and displacement spaces in degree six

The pointwise fixers of the canonical natural plane and the augmentation pair
space are the eight independent pair swaps. Their alternating part has order
four. Enumerating the subsets of these eight words gives the seven four-groups:
three coordinate planes, three mixed planes, and the even plane. This is the
same small subgroup lattice used in Chapter B's `Offenders.Six.Structure.DLattice`,
proved here at the representation layer without a dependency on CFSG.

Every four-group has the canonical natural displacement. The augmentation
identity holds for the three mixed planes. The coordinate four-groups are
conjugate and fix letters, explaining the obstruction already certified in the
parent module. These structural theorems explicitly retain coordinate-plane
exclusion; the marked noncentral quotient must supply it in final assembly.
The original counterexample and quotient dimensions are preserved by import.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 13.8.34, printed p.968 (PDF p.985), and the
six-letter geometry of B.3.4, printed pp.84–85.
-/

@[expose] public section

open BinaryPermutation Representation Module
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
namespace Representation.SixLetterRadicalDisplacement
set_option maxRecDepth 4096

private def radicalSet : Finset S :=
  {1, swap01, swap23, swap45, swap01 * swap23, swap01 * swap45,
    swap23 * swap45, swap01 * swap23 * swap45}

private def radicalGroup : Subgroup S where
  carrier := radicalSet
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    simp only [radicalSet, Finset.mem_insert, Finset.mem_singleton, Finset.mem_coe] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro a ha
    simp only [radicalSet, Finset.mem_insert, Finset.mem_singleton, Finset.mem_coe] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem D_eq_radicalGroup : D = radicalGroup := by
  apply le_antisymm
  · rw [D, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl) <;> change _ ∈ radicalSet <;> decide
  · intro g hg
    change g ∈ radicalSet at hg
    simp only [radicalSet, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact D.one_mem
    · exact swap01_mem_D
    · exact swap23_mem_D
    · exact swap45_mem_D
    · exact D.mul_mem swap01_mem_D swap23_mem_D
    · exact D.mul_mem swap01_mem_D swap45_mem_D
    · exact D.mul_mem swap23_mem_D swap45_mem_D
    · exact D.mul_mem (D.mul_mem swap01_mem_D swap23_mem_D) swap45_mem_D

theorem mem_D_iff (g : S) : g ∈ D ↔
    g = 1 ∨ g = swap01 ∨ g = swap23 ∨ g = swap45 ∨
    g = swap01 * swap23 ∨ g = swap01 * swap45 ∨
    g = swap23 * swap45 ∨ g = swap01 * swap23 * swap45 := by
  rw [D_eq_radicalGroup]
  simp [radicalGroup, radicalSet]

private instance : Fintype radicalGroup := Fintype.ofFinset radicalSet (by intro; rfl)

theorem D_card : Nat.card D = 8 := by
  rw [D_eq_radicalGroup, Nat.card_eq_fintype_card]
  decide

private def evenRadical : Subgroup S := radicalGroup ⊓ alternatingGroup (Fin 6)
private instance : DecidablePred (· ∈ evenRadical) := fun g =>
  inferInstanceAs (Decidable (g ∈ radicalSet ∧ Equiv.Perm.sign g = 1))
private instance : Fintype evenRadical :=
  Fintype.ofFinset (radicalSet.filter (fun g => Equiv.Perm.sign g = 1)) (by intro; simp [evenRadical, radicalGroup])

theorem D0_card : Nat.card D0 = 4 := by
  rw [D0, D_eq_radicalGroup]
  change Nat.card evenRadical = 4
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_eq_four_of_le_D (E : Subgroup S) (hED : E ≤ D)
    (hD0 : ¬ D0 ≤ E) (hcard : 2 < Nat.card E) : Nat.card E = 4 := by
  have hd := Subgroup.card_dvd_of_le hED
  rw [D_card] at hd
  have hle := Nat.le_of_dvd (by decide : 0 < 8) hd
  have hne : Nat.card E ≠ 8 := by
    intro he
    have hEq := Subgroup.eq_of_le_of_card_ge hED (by rw [D_card, he])
    exact hD0 (hEq ▸ inf_le_left)
  interval_cases hc : Nat.card E <;> norm_num at hd <;> omega

theorem card_le_two_of_le_D0 (E : Subgroup S) (hED : E ≤ D0)
    (hD0 : ¬ D0 ≤ E) : Nat.card E ≤ 2 := by
  have hd := Subgroup.card_dvd_of_le hED
  rw [D0_card] at hd
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hne : Nat.card E ≠ 4 := by
    intro he
    have hEq := Subgroup.eq_of_le_of_card_ge hED (by rw [D0_card, he])
    exact hD0 hEq.ge
  interval_cases hc : Nat.card E <;> norm_num at hd <;> omega

private theorem fixes_span_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V →ₗ[ZMod 2] V) (s : Set V) :
    (∀ v ∈ Submodule.span (ZMod 2) s, f v = v) ↔ ∀ v ∈ s, f v = v := by
  constructor
  · intro h v hv
    exact h v (Submodule.subset_span hv)
  · intro h v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => exact map_zero f
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul a x _ hx => simp only [map_smul, hx]

private theorem fixes_pairs_iff (g : S) :
    (pair (g 0) (g 1) = pair 0 1 ∧ pair (g 2) (g 3) = pair 2 3) ↔ g ∈ D := by
  rw [mem_D_iff]
  constructor
  · rintro ⟨h01, h23⟩
    have hp : ∀ a b c d : Fin 6, pair a b = pair c d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by decide
    rcases hp _ _ _ _ h01 with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
      rcases hp _ _ _ _ h23 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    all_goals
      have h4 : g 4 = 4 ∨ g 4 = 5 := by
        have hd0 := g.injective.ne (by decide : (4 : Fin 6) ≠ 0)
        have hd1 := g.injective.ne (by decide : (4 : Fin 6) ≠ 1)
        have hd2 := g.injective.ne (by decide : (4 : Fin 6) ≠ 2)
        have hd3 := g.injective.ne (by decide : (4 : Fin 6) ≠ 3)
        generalize he : g 4 = e at *
        fin_cases e <;> simp_all
      have h5 : g 5 = 4 ∨ g 5 = 5 := by
        have hd0 := g.injective.ne (by decide : (5 : Fin 6) ≠ 0)
        have hd1 := g.injective.ne (by decide : (5 : Fin 6) ≠ 1)
        have hd2 := g.injective.ne (by decide : (5 : Fin 6) ≠ 2)
        have hd3 := g.injective.ne (by decide : (5 : Fin 6) ≠ 3)
        generalize he : g 5 = e at *
        fin_cases e <;> simp_all
      have h45 := g.injective.ne (by decide : (4 : Fin 6) ≠ 5)
      rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
        first
        | exact False.elim (h45 (h4.trans h5.symm))
        | simp [Equiv.Perm.ext_iff, Fin.forall_fin_succ, h0, h1, h2, h3, h4, h5,
            swap01, swap23, swap45, Equiv.swap_apply_def]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem natural_plane_fixer (g : S) :
    (∀ v ∈ canonicalPlane, naturalRepresentation (Fin 6) g v = v) ↔ g ∈ D := by
  rw [canonicalPlane, fixes_span_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    pairVector_map]
  rw [pairVector_eq_iff (g.injective.ne (by decide)) (by decide),
    pairVector_eq_iff (g.injective.ne (by decide)) (by decide)]
  exact fixes_pairs_iff g

/-- The natural module is the quotient image of the augmentation core. -/
def toNatural : U →ₗ[ZMod 2] natural (Fin 6) where
  toFun v := ⟨(constants (Fin 6)).mkQ v.val, ⟨v.val, v.property, rfl⟩⟩
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a v := by apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem toNatural_q (i j : Fin 6) : toNatural (q i j) = pairVector i j := rfl

theorem toNatural_equivariant (g : S) (v : U) :
    toNatural (coreRepresentation (Fin 6) g v) =
      naturalRepresentation (Fin 6) g (toNatural v) := rfl

theorem toNatural_surjective : Function.Surjective toNatural := by
  rintro ⟨_, v, hv, rfl⟩
  exact ⟨⟨v, hv⟩, rfl⟩

theorem augmentation_pair_fixer (g : S) :
    (∀ v ∈ F ⊔ W, coreRepresentation (Fin 6) g v = v) ↔ g ∈ D := by
  rw [F_sup_W_eq_pairSpan, fixes_span_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨h01, h23, _⟩
    apply (natural_plane_fixer g).mp
    rw [canonicalPlane, fixes_span_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact ⟨by simpa only [toNatural_equivariant, toNatural_q] using congrArg toNatural h01,
      by simpa only [toNatural_equivariant, toNatural_q] using congrArg toNatural h23⟩
  · intro hg
    rw [mem_D_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem alternating_natural_plane_fixer (g : S) :
    (g ∈ alternatingGroup (Fin 6) ∧
      ∀ v ∈ canonicalPlane, naturalRepresentation (Fin 6) g v = v) ↔ g ∈ D0 := by
  rw [natural_plane_fixer]
  exact and_comm

theorem alternating_augmentation_pair_fixer (g : S) :
    (g ∈ alternatingGroup (Fin 6) ∧
      ∀ v ∈ F ⊔ W, coreRepresentation (Fin 6) g v = v) ↔ g ∈ D0 := by
  rw [augmentation_pair_fixer]
  exact and_comm

private def fourChoices (s : Finset S) : Prop :=
  s = {1, swap01, swap23, swap01 * swap23} ∨
  s = {1, swap01, swap45, swap01 * swap45} ∨
  s = {1, swap23, swap45, swap23 * swap45} ∨
  s = {1, swap01 * swap23, swap45, swap01 * swap23 * swap45} ∨
  s = {1, swap01 * swap45, swap23, (swap01 * swap45) * swap23} ∨
  s = {1, swap23 * swap45, swap01, (swap23 * swap45) * swap01} ∨
  s = {1, swap01 * swap23, swap01 * swap45, (swap01 * swap23) * (swap01 * swap45)}

private instance (s : Finset S) : Decidable (fourChoices s) := by unfold fourChoices; infer_instance

private def radicalList : List S :=
  [1, swap01, swap23, swap45, swap01 * swap23, swap01 * swap45,
    swap23 * swap45, swap01 * swap23 * swap45]

private theorem radicalList_toFinset : radicalList.toFinset = radicalSet := by decide

private theorem four_choices_certificate :
    radicalList.sublists.all (fun l =>
      (!(decide (l.toFinset.card = 4) &&
        l.all (fun a => l.all (fun b => decide (a * b ∈ l.toFinset))))) ||
      decide (fourChoices l.toFinset)) = true := by decide

/-- The seven planes of the elementary abelian radical, by generating pairs. -/
theorem four_subgroup_cases (E : Subgroup S) (hED : E ≤ D) (hcard : Nat.card E = 4) :
    E = Subgroup.closure {swap01, swap23} ∨ E = Subgroup.closure {swap01, swap45} ∨
    E = Subgroup.closure {swap23, swap45} ∨ E = Subgroup.closure {swap01 * swap23, swap45} ∨
    E = Subgroup.closure {swap01 * swap45, swap23} ∨
    E = Subgroup.closure {swap23 * swap45, swap01} ∨
    E = Subgroup.closure {swap01 * swap23, swap01 * swap45} := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let s : Finset S := Finset.univ.image (fun g : E => g.val)
  have hs (g : S) : g ∈ s ↔ g ∈ E := by simp [s]
  let l := radicalList.filter (fun g => decide (g ∈ s))
  have hl : l.toFinset = s := by
    ext g
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, l]
    constructor
    · exact And.right
    · intro hg
      refine ⟨?_, hg⟩
      rw [← List.mem_toFinset, radicalList_toFinset]
      have := hED ((hs g).mp hg)
      rwa [D_eq_radicalGroup] at this
  have hlmem : l ∈ radicalList.sublists := List.mem_sublists.mpr List.filter_sublist
  have hc : s.card = 4 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard]
  have hm : l.all (fun a => l.all (fun b => decide (a * b ∈ l.toFinset))) = true := by
    simp only [List.all_eq_true, ← List.mem_toFinset, hl, decide_eq_true_eq]
    intro a ha b hb
    exact (hs _).mpr (E.mul_mem ((hs _).mp ha) ((hs _).mp hb))
  have ht := List.all_eq_true.mp four_choices_certificate l hlmem
  rw [hm, hl] at ht
  simp only [hc, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at ht
  have heq (a b : S) (he : s = {1, a, b, a * b}) : E = Subgroup.closure {a, b} := by
    apply le_antisymm
    · intro g hg
      have := (hs g).mpr hg
      rw [he] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      rintro g (rfl | rfl) <;> apply (hs _).mp <;> simp [he]
  rcases ht with ht | ht | ht | ht | ht | ht | ht
  · exact Or.inl (heq _ _ ht)
  · exact Or.inr (Or.inl (heq _ _ ht))
  · exact Or.inr (Or.inr (Or.inl (heq _ _ ht)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (heq _ _ ht))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (heq _ _ ht)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (heq _ _ ht))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (heq _ _ ht))))))


private theorem D0_le_of_doubles (E : Subgroup S)
    (ha : swap01 * swap23 ∈ E) (hb : swap01 * swap45 ∈ E) : D0 ≤ E := by
  intro g hg
  have h := (mem_D_iff g).mp hg.1
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact E.one_mem
  · exact False.elim ((by decide : swap01 ∉ alternatingGroup (Fin 6)) hg.2)
  · exact False.elim ((by decide : swap23 ∉ alternatingGroup (Fin 6)) hg.2)
  · exact False.elim ((by decide : swap45 ∉ alternatingGroup (Fin 6)) hg.2)
  · exact ha
  · exact hb
  · simpa only [show (swap01 * swap23) * (swap01 * swap45) = swap23 * swap45 by decide]
      using E.mul_mem ha hb
  · exact False.elim ((by decide : swap01 * swap23 * swap45 ∉ alternatingGroup (Fin 6)) hg.2)

/-- After excluding the coordinate four-groups, precisely the three mixed planes remain. -/
theorem mixed_four_cases (E : Subgroup S) (hED : E ≤ D) (hD0 : ¬ D0 ≤ E)
    (hcard : 2 < Nat.card E)
    (hfix : ∀ i : Fin 6, ∃ g ∈ E, g i ≠ i) :
    E = Subgroup.closure {swap01 * swap23, swap45} ∨
    E = Subgroup.closure {swap01 * swap45, swap23} ∨
    E = Subgroup.closure {swap23 * swap45, swap01} := by
  have hc := card_eq_four_of_le_D E hED hD0 hcard
  have hnofix (a b : S) (i : Fin 6) (ha : a i = i) (hb : b i = i)
      (he : E = Subgroup.closure {a, b}) : False := by
    have hle : E ≤ MulAction.stabilizer S i := by
      rw [he, Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact ha
      · exact hb
    obtain ⟨g, hg, hn⟩ := hfix i
    exact hn (hle hg)
  rcases four_subgroup_cases E hED hc with he | he | he | he | he | he | he
  · exact False.elim (hnofix _ _ 4 (by decide) (by decide) he)
  · exact False.elim (hnofix _ _ 2 (by decide) (by decide) he)
  · exact False.elim (hnofix _ _ 0 (by decide) (by decide) he)
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)
  · exact False.elim (hD0 (D0_le_of_doubles E
      (he ▸ Subgroup.subset_closure (by simp)) (he ▸ Subgroup.subset_closure (by simp))))

private theorem mem_pairSpan (v : U)
    (h01 : v.val 0 = v.val 1) (h23 : v.val 2 = v.val 3)
    (h45 : v.val 4 = v.val 5) : v ∈ F ⊔ W := by
  rw [F_sup_W_eq_pairSpan]
  have he : v = v.val 0 • q 0 1 + v.val 2 • q 2 3 + v.val 4 • q 4 5 := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [q, h01, h23, h45]
  rw [he]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- Every radical displacement lies in the three-dimensional pair space. -/
theorem displacement_le_pairSpace (E : Subgroup S) (hED : E ≤ D) :
    displacement E ≤ F ⊔ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,v⟩,rfl⟩
  change coreRepresentation (Fin 6) g.val v - v ∈ F ⊔ W
  have hg := (mem_D_iff g.val).mp (hED g.property)
  apply mem_pairSpan
  all_goals
    rcases hg with hg | hg | hg | hg | hg | hg | hg | hg <;> rw [hg]
    all_goals
      change v.val (_ : Fin 6) - v.val _ = v.val _ - v.val _
      simp [swap01, swap23, swap45, Equiv.Perm.mul_def, Equiv.swap_apply_def,
        CharTwo.sub_eq_add, add_comm]

private theorem difference_mem (E : Subgroup S) (g : S) (hg : g ∈ E) (v w : U)
    (h : coreRepresentation (Fin 6) g v - v = w) : w ∈ displacement E :=
  Coinvariants.mem_ker_of_eq (ρ := (coreRepresentation (Fin 6)).comp E.subtype) ⟨g,hg⟩ v w h

/-- Total displacement on the actual natural module. -/
def naturalDisplacement (E : Subgroup S) : Submodule (ZMod 2) (natural (Fin 6)) :=
  Coinvariants.ker ((naturalRepresentation (Fin 6)).comp E.subtype)

theorem map_displacement (E : Subgroup S) :
    (displacement E).map toNatural = naturalDisplacement E := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change toNatural (coreRepresentation (Fin 6) g.val v - v) ∈ naturalDisplacement E
    rw [map_sub, toNatural_equivariant]
    exact Coinvariants.sub_mem_ker (ρ := (naturalRepresentation (Fin 6)).comp E.subtype) g _
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    obtain ⟨u,rfl⟩ := toNatural_surjective v
    exact ⟨coreRepresentation (Fin 6) g.val u - u,
      Coinvariants.sub_mem_ker (ρ := (coreRepresentation (Fin 6)).comp E.subtype) g u,
      by rw [map_sub, toNatural_equivariant]; rfl⟩

theorem map_pairSpace : (F ⊔ W).map toNatural = canonicalPlane := by
  rw [F_sup_W_eq_pairSpan, Submodule.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, toNatural_q]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v (rfl | rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [pairVector_add]
      exact canonicalPlane.add_mem (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
  · apply Submodule.span_mono
    intro v hv
    rcases hv with rfl | rfl <;> simp


private theorem plane_le_of_pairs (E : Subgroup S)
    (hp : (q 0 1 ∈ displacement E ∧ q 2 3 ∈ displacement E) ∨
      (q 0 1 ∈ displacement E ∧ q 4 5 ∈ displacement E) ∨
      (q 2 3 ∈ displacement E ∧ q 4 5 ∈ displacement E)) :
    canonicalPlane ≤ naturalDisplacement E := by
  have hm {v : U} (hv : v ∈ displacement E) : toNatural v ∈ naturalDisplacement E := by
    rw [← map_displacement]
    exact Submodule.mem_map_of_mem hv
  have hz (v : natural (Fin 6)) : v + v = 0 := by
    simpa only [add_smul, one_smul, zero_smul] using
      congrArg (fun a : ZMod 2 => a • v) (by decide : (1 : ZMod 2) + 1 = 0)
  have h01 : pairVector 0 1 = pairVector 2 3 + pairVector 4 5 := by
    rw [pairVector_add, add_left_comm, hz, add_zero]
  have h23 : pairVector 2 3 = pairVector 0 1 + pairVector 4 5 := by
    rw [pairVector_add, ← add_assoc, hz, zero_add]
  have hpair : pairVector 0 1 ∈ naturalDisplacement E ∧
      pairVector 2 3 ∈ naturalDisplacement E := by
    rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨hm ha, hm hb⟩
    · exact ⟨hm ha, h23 ▸ (naturalDisplacement E).add_mem (hm ha) (hm hb)⟩
    · exact ⟨h01 ▸ (naturalDisplacement E).add_mem (hm ha) (hm hb), hm ha⟩
  apply Submodule.span_le.mpr
  rintro v (rfl | rfl)
  · exact hpair.1
  · exact hpair.2

/-- Every four-subgroup of the radical has the canonical natural displacement. -/
theorem natural_displacement_of_four (E : Subgroup S) (hED : E ≤ D)
    (hcard : Nat.card E = 4) : naturalDisplacement E = canonicalPlane := by
  apply le_antisymm
  · rw [← map_displacement, ← map_pairSpace]
    exact Submodule.map_mono (displacement_le_pairSpace E hED)
  · apply plane_le_of_pairs
    have hgen {a b : S} (he : E = Subgroup.closure {a,b}) : a ∈ E ∧ b ∈ E := by
      rw [he]
      exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
    rcases four_subgroup_cases E hED hcard with he | he | he | he | he | he | he
    · exact Or.inl ⟨difference_mem E _ (hgen he).1 (q 0 4) _ (by decide),
        difference_mem E _ (hgen he).2 (q 2 4) _ (by decide)⟩
    · exact Or.inr (Or.inl ⟨difference_mem E _ (hgen he).1 (q 0 2) _ (by decide),
        difference_mem E _ (hgen he).2 (q 4 2) _ (by decide)⟩)
    · exact Or.inr (Or.inr ⟨difference_mem E _ (hgen he).1 (q 2 0) _ (by decide),
        difference_mem E _ (hgen he).2 (q 4 0) _ (by decide)⟩)
    · exact Or.inl ⟨difference_mem E _ (hgen he).1 (q 0 4) _ (by decide),
        difference_mem E _ (hgen he).1 (q 2 4) _ (by decide)⟩
    · exact Or.inl ⟨difference_mem E _ (hgen he).1 (q 0 2) _ (by decide),
        difference_mem E _ (hgen he).2 (q 2 0) _ (by decide)⟩
    · exact Or.inl ⟨difference_mem E _ (hgen he).2 (q 0 2) _ (by decide),
        difference_mem E _ (hgen he).1 (q 2 0) _ (by decide)⟩
    · exact Or.inl ⟨difference_mem E _ (hgen he).1 (q 0 4) _ (by decide),
        difference_mem E _ (hgen he).1 (q 2 4) _ (by decide)⟩

theorem natural_displacement (E : Subgroup S) (hED : E ≤ D)
    (hD0 : ¬ D0 ≤ E) (hcard : 2 < Nat.card E) :
    Nat.card E = 4 ∧ naturalDisplacement E = canonicalPlane := by
  have hc := card_eq_four_of_le_D E hED hD0 hcard
  exact ⟨hc, natural_displacement_of_four E hED hc⟩

/-- The corrected augmentation calculation, with the fixed-letter obstruction removed.
The marked noncentral quotient supplies this condition in the final assembly. -/
theorem augmentation_displacement_of_no_fixed_letter (E : Subgroup S) (hED : E ≤ D)
    (hD0 : ¬ D0 ≤ E) (hcard : 2 < Nat.card E)
    (hfix : ∀ i : Fin 6, ∃ g ∈ E, g i ≠ i) : displacement E = F ⊔ W := by
  apply le_antisymm (displacement_le_pairSpace E hED)
  rw [F_sup_W_eq_pairSpan]
  apply Submodule.span_le.mpr
  have hgen {a b : S} (he : E = Subgroup.closure {a,b}) : a ∈ E ∧ b ∈ E := by
    rw [he]
    exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
  rcases mixed_four_cases E hED hD0 hcard hfix with he | he | he
  · rintro v (rfl | rfl | rfl)
    · exact difference_mem E _ (hgen he).1 (q 0 4) _ (by decide)
    · exact difference_mem E _ (hgen he).1 (q 2 4) _ (by decide)
    · exact difference_mem E _ (hgen he).2 (q 4 0) _ (by decide)
  · rintro v (rfl | rfl | rfl)
    · exact difference_mem E _ (hgen he).1 (q 0 2) _ (by decide)
    · exact difference_mem E _ (hgen he).2 (q 2 0) _ (by decide)
    · exact difference_mem E _ (hgen he).1 (q 4 2) _ (by decide)
  · rintro v (rfl | rfl | rfl)
    · exact difference_mem E _ (hgen he).2 (q 0 2) _ (by decide)
    · exact difference_mem E _ (hgen he).1 (q 2 0) _ (by decide)
    · exact difference_mem E _ (hgen he).1 (q 4 0) _ (by decide)


/-- Relabeling the last two pairs carries the coordinate four-group to the second one. -/
theorem coordinateFour_conjugate_02 :
    coordinateFour.map (MulAut.conj (Equiv.swap 2 4 * Equiv.swap 3 5 : S)).toMonoidHom =
      Subgroup.closure {swap01, swap45} := by
  rw [coordinateFour_eq_closure, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  rw [show (MulAut.conj (Equiv.swap 2 4 * Equiv.swap 3 5 : S)).toMonoidHom swap01 = swap01 by decide,
    show (MulAut.conj (Equiv.swap 2 4 * Equiv.swap 3 5 : S)).toMonoidHom swap23 = swap45 by decide]

/-- Relabeling the first and last pairs gives the third coordinate four-group. -/
theorem coordinateFour_conjugate_12 :
    coordinateFour.map (MulAut.conj (Equiv.swap 0 4 * Equiv.swap 1 5 : S)).toMonoidHom =
      Subgroup.closure {swap23, swap45} := by
  rw [coordinateFour_eq_closure, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  rw [show (MulAut.conj (Equiv.swap 0 4 * Equiv.swap 1 5 : S)).toMonoidHom swap01 = swap45 by decide,
    show (MulAut.conj (Equiv.swap 0 4 * Equiv.swap 1 5 : S)).toMonoidHom swap23 = swap23 by decide,
    Set.pair_comm]

/-- Excluding the three coordinate planes leaves exactly the three mixed planes. -/
theorem mixed_four_cases_of_not_coordinate (E : Subgroup S) (hED : E ≤ D)
    (hD0 : ¬ D0 ≤ E) (hcard : 2 < Nat.card E)
    (hcoord : ∀ g : S, E ≠ coordinateFour.map (MulAut.conj g).toMonoidHom) :
    E = Subgroup.closure {swap01 * swap23, swap45} ∨
    E = Subgroup.closure {swap01 * swap45, swap23} ∨
    E = Subgroup.closure {swap23 * swap45, swap01} := by
  have hc := card_eq_four_of_le_D E hED hD0 hcard
  rcases four_subgroup_cases E hED hc with he | he | he | he | he | he | he
  · apply False.elim
    apply hcoord 1
    have hid : (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S := by
      apply MonoidHom.ext
      intro g
      change 1 * g * 1⁻¹ = g
      simp
    simpa only [hid, Subgroup.map_id, coordinateFour_eq_closure] using he
  · exact False.elim (hcoord _ (he.trans coordinateFour_conjugate_02.symm))
  · exact False.elim (hcoord _ (he.trans coordinateFour_conjugate_12.symm))
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)
  · exact False.elim (hD0 (D0_le_of_doubles E
      (by rw [he]; exact Subgroup.subset_closure (by simp))
      (by rw [he]; exact Subgroup.subset_closure (by simp))))

/-- None of the three mixed planes fixes a letter. -/
theorem no_fixed_letter_of_not_coordinate (E : Subgroup S) (hED : E ≤ D)
    (hD0 : ¬ D0 ≤ E) (hcard : 2 < Nat.card E)
    (hcoord : ∀ g : S, E ≠ coordinateFour.map (MulAut.conj g).toMonoidHom) :
    ∀ i : Fin 6, ∃ g ∈ E, g i ≠ i := by
  have hm (a b : S) (he : E = Subgroup.closure {a,b})
      (hmove : ∀ i : Fin 6, a i ≠ i ∨ b i ≠ i) :
      ∀ i : Fin 6, ∃ g ∈ E, g i ≠ i := by
    intro i
    rcases hmove i with ha | hb
    · exact ⟨a, by rw [he]; exact Subgroup.subset_closure (by simp), ha⟩
    · exact ⟨b, by rw [he]; exact Subgroup.subset_closure (by simp), hb⟩
  rcases mixed_four_cases_of_not_coordinate E hED hD0 hcard hcoord with he | he | he
  · exact hm _ _ he (by decide)
  · exact hm _ _ he (by decide)
  · exact hm _ _ he (by decide)

/-- Structural assembly of the corrected calculation from coordinate-plane exclusion. -/
theorem augmentation_displacement_of_not_coordinate (E : Subgroup S) (hED : E ≤ D)
    (hD0 : ¬ D0 ≤ E) (hcard : 2 < Nat.card E)
    (hcoord : ∀ g : S, E ≠ coordinateFour.map (MulAut.conj g).toMonoidHom) :
    displacement E = F ⊔ W :=
  augmentation_displacement_of_no_fixed_letter E hED hD0 hcard
    (no_fixed_letter_of_not_coordinate E hED hD0 hcard hcoord)

end Representation.SixLetterRadicalDisplacement
