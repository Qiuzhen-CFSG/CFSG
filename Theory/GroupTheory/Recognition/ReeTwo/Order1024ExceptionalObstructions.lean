module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024Representatives
public import Theory.GroupTheory.CentricRadicalAutomorphisms
public import Theory.GroupTheory.CentricRadicalObstructions
public import Theory.SpecificGroups.ReeTwo.SylowTailCoordinates
public import Theory.SpecificGroups.ReeTwo.MaximalCharacters

/-!
# Radical obstructions for the three exceptional Ree two subgroups

Conjugation by Shinoda root 6 normalizes each exceptional representative and
acts trivially on its Frattini quotient. Its displacements on the generators
are roots 7, 10, and 12, which are products of squares and commutators inside
the representative. Burnside's Frattini kernel theorem places this action
in the automorphism two-core.

The representatives are self-centralizing, but root 6 belongs to none of
them, so its action is not inner. Two binary characters exclude root 6 from
the first two representatives; an invariant core-coordinate kernel excludes
it from the third. Ambient isomorphism transport gives the same obstruction
for every Sylow conjugate.

Source: Shinoda (1975), (2.3), pp. 81–82, using the verified coordinate group
in `ReeTwo.Sylow`. The finite root and centralizer tests are checked by Lean's
kernel; no subgroup census or external automorphism calculation is assumed.
-/

open ReeTwo
open scoped commutatorElement
private theorem norm_apply {G : Type*} [Group G] (E : Subgroup G)
    (g : Subgroup.normalizer (E : Set G)) (x : E) :
    (E.normalizerMonoidHom g x : G) = g * x * (g : G)⁻¹ := rfl
namespace ReeTwo.SylowModel
set_option maxRecDepth 8192

private def extra (i : Fin 3) (j : Fin 3) : SylowModel :=
  ![![root 2 * root 3, root 1 * root 3, rootOne],
    ![root 2 * root 3, root 1 * root 3, rootOne * root 3],
    ![root 2 * root 3, root 1, rootOne]] i j

private theorem extra_mem (i : Fin 3) (j : Fin 3) : extra i j ∈ exceptionalCandidate i := by
  apply Subgroup.mem_sup_right
  apply Subgroup.subset_closure
  fin_cases i <;> fin_cases j
  all_goals change _ ∈ ({_, _, _} : Set SylowModel)
  all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)

private theorem tail_mem (i : Fin 3) (j : CoreRoot) (hj : 4 ≤ j.val) :
    root j ∈ exceptionalCandidate i :=
  tailSubgroup_le_exceptionalCandidate i (Subgroup.subset_closure ⟨j, hj, rfl⟩)

set_option maxHeartbeats 2000000 in
private theorem root_frattini (i : Fin 3) :
    root 4 ∈ (frattini (exceptionalCandidate i)).map (exceptionalCandidate i).subtype ∧
    root 7 ∈ (frattini (exceptionalCandidate i)).map (exceptionalCandidate i).subtype ∧
    root 9 ∈ (frattini (exceptionalCandidate i)).map (exceptionalCandidate i).subtype := by
  let E := exceptionalCandidate i
  let F := (frattini E).map E.subtype
  let : Fact (IsPGroup 2 E) := ⟨(IsPGroup.of_card (n := 12) card).to_subgroup E⟩
  have hc (x y : SylowModel) (hx : x ∈ E) (hy : y ∈ E) : rightComm x y ∈ F := by
    apply Subgroup.mem_map_of_mem E.subtype
      (x := rightComm (⟨x, hx⟩ : E) ⟨y, hy⟩)
    apply commutator_le_frattini_of_isPGroup (p := 2)
    simpa only [commutatorElement_def, inv_inv, rightComm, commutator_def] using
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top (⟨x, hx⟩ : E)⁻¹) (Subgroup.mem_top (⟨y, hy⟩ : E)⁻¹))
  have hs (x : SylowModel) (hx : x ∈ E) : x ^ 2 ∈ F :=
    Subgroup.mem_map_of_mem E.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x, hx⟩ : E))
  have ha := extra_mem i 0
  have hc' := extra_mem i 2
  have h8 : root 8 ∈ F := by
    have h := hc _ _ ha (tail_mem i 4 (by decide))
    rwa [show rightComm (extra i 0) (root 4) = root 8 from
      (by decide +kernel : ∀ k : Fin 3, rightComm (extra k 0) (root 4) = root 8) i] at h
  have h9 : root 9 ∈ F := by
    have h := hc _ _ ha (tail_mem i 6 (by decide))
    rwa [show rightComm (extra i 0) (root 6) = root 9 from
      (by decide +kernel : ∀ k : Fin 3, rightComm (extra k 0) (root 6) = root 9) i] at h
  have h7 : root 7 ∈ F := by
    have h := hs _ ha
    rw [show extra i 0 ^ 2 = root 7 * root 8 * root 9 from
      (by decide +kernel : ∀ k : Fin 3, extra k 0 ^ 2 = root 7 * root 8 * root 9) i] at h
    exact (F.mul_mem_cancel_right h8).mp ((F.mul_mem_cancel_right h9).mp h)
  refine ⟨?_, h7, h9⟩
  have h := hc _ _ ha hc'
  have he : rightComm (extra i 0) (extra i 2) = root 4 ∨
      rightComm (extra i 0) (extra i 2) = root 4 * root 7 :=
    (by decide +kernel : ∀ k : Fin 3,
      rightComm (extra k 0) (extra k 2) = root 4 ∨
      rightComm (extra k 0) (extra k 2) = root 4 * root 7) i
  rcases he with he | he
  · exact he ▸ h
  · exact (F.mul_mem_cancel_right h7).mp (he ▸ h)

private theorem extra_displacement : ∀ (i j : Fin 3),
    (extra i j)⁻¹ * (root 3 * extra i j * (root 3)⁻¹) =
      ![root 7, 1, root 4] j := by decide +kernel

private theorem tail_displacement : ∀ j : CoreRoot, 4 ≤ j.val →
    (root j)⁻¹ * (root 3 * root j * (root 3)⁻¹) =
      if j = 6 then root 9 else 1 := by decide +kernel

private theorem candidate_le (i : Fin 3) (H : Subgroup SylowModel)
    (he : ∀ j : Fin 3, extra i j ∈ H)
    (ht : ∀ j : CoreRoot, 4 ≤ j.val → root j ∈ H) : exceptionalCandidate i ≤ H := by
  apply sup_le
  · exact (Subgroup.closure_le _).mpr (by rintro x ⟨j, hj, rfl⟩; exact ht j hj)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    fin_cases i
    all_goals change x ∈ ({_, _, _} : Set SylowModel) at hx
    all_goals rcases hx with rfl | rfl | rfl
    all_goals first | exact he 0 | exact he 1 | exact he 2

private theorem root_normalizes (i : Fin 3) :
    root 3 ∈ Subgroup.normalizer (exceptionalCandidate i : Set SylowModel) := by
  let E := exceptionalCandidate i
  have hconj : E.map (MulAut.conj (root 3)).toMonoidHom ≤ E := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply candidate_le
    · intro j
      change root 3 * extra i j * (root 3)⁻¹ ∈ E
      have hd : (extra i j)⁻¹ * (root 3 * extra i j * (root 3)⁻¹) ∈ E := by
        rw [extra_displacement]
        fin_cases j
        · exact tail_mem i 7 (by decide)
        · exact E.one_mem
        · exact tail_mem i 4 (by decide)
      simpa only [mul_inv_cancel_left] using E.mul_mem (extra_mem i j) hd
    · intro j hj
      change root 3 * root j * (root 3)⁻¹ ∈ E
      have hd : (root j)⁻¹ * (root 3 * root j * (root 3)⁻¹) ∈ E := by
        rw [tail_displacement j hj]
        split
        · exact tail_mem i 9 (by decide)
        · exact E.one_mem
      simpa only [mul_inv_cancel_left] using E.mul_mem (tail_mem i j hj) hd
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  exact Subgroup.eq_of_le_of_card_ge hconj
    (Nat.card_congr (E.equivMapOfInjective (MulAut.conj (root 3)).toMonoidHom
      (MulAut.conj (root 3)).injective).toEquiv).le

set_option maxHeartbeats 2000000 in
private theorem frattini_action (i : Fin 3) :
    Subgroup.quotientAut (frattini (exceptionalCandidate i))
      ((exceptionalCandidate i).normalizerMonoidHom ⟨root 3, root_normalizes i⟩) = 1 := by
  let E := exceptionalCandidate i
  let F := frattini E
  let a : MulAut E := E.normalizerMonoidHom ⟨root 3, root_normalizes i⟩
  have ha_apply (x : E) : (a x : SylowModel) = root 3 * x * (root 3)⁻¹ := by
    have hi : @Inv.inv SylowModel (inferInstance : Group SylowModel).toInv (root 3) =
        (root 3)⁻¹ := by rfl
    have hh := @norm_apply SylowModel (inferInstance : Group SylowModel) E
      ⟨root 3, root_normalizes i⟩ x
    simpa only [hi] using hh
  let q := QuotientGroup.mk' F
  let L := (q.comp a.toMonoidHom).eqLocus q
  have hle : E ≤ L.map E.subtype := by
    apply candidate_le
    · intro j
      refine ⟨⟨extra i j, extra_mem i j⟩, ?_, rfl⟩
      change q (a ⟨extra i j, extra_mem i j⟩) = q ⟨extra i j, extra_mem i j⟩
      apply Eq.symm
      apply QuotientGroup.eq.mpr
      have hh : (extra i j)⁻¹ * (root 3 * extra i j * (root 3)⁻¹) ∈ F.map E.subtype := by
        rw [extra_displacement]
        fin_cases j
        · exact (root_frattini i).2.1
        · exact (F.map E.subtype).one_mem
        · exact (root_frattini i).1
      obtain ⟨z, hz, he⟩ := hh
      have he' : z = (⟨extra i j, extra_mem i j⟩ : E)⁻¹ * a ⟨extra i j, extra_mem i j⟩ :=
        Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.subtype_apply, ha_apply] using he)
      exact he' ▸ hz
    · intro j hj
      refine ⟨⟨root j, tail_mem i j hj⟩, ?_, rfl⟩
      change q (a ⟨root j, tail_mem i j hj⟩) = q ⟨root j, tail_mem i j hj⟩
      apply Eq.symm
      apply QuotientGroup.eq.mpr
      have hh : (root j)⁻¹ * (root 3 * root j * (root 3)⁻¹) ∈ F.map E.subtype := by
        rw [tail_displacement j hj]
        split
        · exact (root_frattini i).2.2
        · exact (F.map E.subtype).one_mem
      obtain ⟨z, hz, he⟩ := hh
      have he' : z = (⟨root j, tail_mem i j hj⟩ : E)⁻¹ * a ⟨root j, tail_mem i j hj⟩ :=
        Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.subtype_apply, ha_apply] using he)
      exact he' ▸ hz
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change Subgroup.quotientAut F a (q x) = q x
    rw [Subgroup.quotientAut_apply_mk]
    obtain ⟨y, hy, he⟩ := hle x.property
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy

private theorem le_character_ker_zero : exceptionalCandidate 0 ≤ coreCharacter.ker := by
  apply candidate_le
  · exact (by decide +kernel : ∀ j : Fin 3, coreCharacter (extra 0 j) = 1)
  · exact (by decide +kernel : ∀ j : CoreRoot, 4 ≤ j.val → coreCharacter (root j) = 1)

private theorem le_character_ker_one : exceptionalCandidate 1 ≤ mixedCharacter.ker := by
  apply candidate_le
  · exact (by decide +kernel : ∀ j : Fin 3, mixedCharacter (extra 1 j) = 1)
  · exact (by decide +kernel : ∀ j : CoreRoot, 4 ≤ j.val → mixedCharacter (root j) = 1)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 1024 in
private theorem centralizer_test : ∀ (i : Fin 3) (g : SylowModel),
    extra i 0 * g = g * extra i 0 →
    extra i 1 * g = g * extra i 1 →
    extra i 2 * g = g * extra i 2 →
    root 4 * g = g * root 4 → root 5 * g = g * root 5 →
    g.right = 1 ∧ g.left.b0 = 0 ∧ g.left.b1 = 0 ∧
      g.left.b2 = 0 ∧ g.left.b3 = 0 := by
  intro i
  fin_cases i <;> decide +kernel

private theorem candidate_centric (i : Fin 3) :
    Subgroup.centralizer (exceptionalCandidate i : Set SylowModel) ≤ exceptionalCandidate i := by
  intro g hg
  apply tailSubgroup_le_exceptionalCandidate i
  rw [mem_tailSubgroup]
  apply centralizer_test i g
  · exact Subgroup.mem_centralizer_iff.mp hg _ (extra_mem i 0)
  · exact Subgroup.mem_centralizer_iff.mp hg _ (extra_mem i 1)
  · exact Subgroup.mem_centralizer_iff.mp hg _ (extra_mem i 2)
  · exact Subgroup.mem_centralizer_iff.mp hg _ (tail_mem i 4 (by decide))
  · exact Subgroup.mem_centralizer_iff.mp hg _ (tail_mem i 5 (by decide))

private def middleCharacter : Core →* FiveFour.Cyclic 2 where
  toFun x := Multiplicative.ofAdd (x.b2 + x.b3)
  map_one' := by rfl
  map_mul' x y := by
    change Multiplicative.ofAdd ((x.b2 + y.b2) + (x.b3 + y.b3)) =
      Multiplicative.ofAdd ((x.b2 + x.b3) + (y.b2 + y.b3))
    congr 1
    ring

private theorem middle_action_a : middleCharacter.comp Core.a.toMonoidHom =
    middleCharacter * Core.rootThreeCharacter := by
  apply Core.hom_ext
  exact (by decide +kernel : ∀ j : CoreRoot,
    middleCharacter (Core.a (Core.root j)) =
      middleCharacter (Core.root j) * Core.rootThreeCharacter (Core.root j))

private def middleKernel : Subgroup Core :=
  Core.rootThreeCharacter.ker ⊓ middleCharacter.ker

private theorem middleKernel_action (t : FiveFour.Cyclic 4) (x : Core)
    (hx : x ∈ middleKernel) :
    Core.complementAction (SemidirectProduct.inr t) x ∈ middleKernel := by
  rw [← FiveFour.generator_pow_val t, map_pow, map_pow]
  change (Core.a ^ t.toAdd.val) x ∈ middleKernel
  have ha (y : Core) (hy : y ∈ middleKernel) : Core.a y ∈ middleKernel := by
    constructor
    · exact (Core.rootThreeCharacter_action (FiveFour.generator 4) y).trans hy.1
    · have h := DFunLike.congr_fun middle_action_a y
      change middleCharacter (Core.a y) = middleCharacter y * Core.rootThreeCharacter y at h
      change middleCharacter (Core.a y) = 1
      rw [h, hy.1, hy.2, mul_one]
  generalize t.toAdd.val = n
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact ha _ ih

private def thirdBound : Subgroup SylowModel where
  carrier := {g | g.left ∈ middleKernel}
  one_mem' := middleKernel.one_mem
  mul_mem' {x y} hx hy := middleKernel.mul_mem hx (middleKernel_action x.right y.left hy)
  inv_mem' {x} hx := middleKernel_action x.right⁻¹ x.left⁻¹ (middleKernel.inv_mem hx)

private theorem le_thirdBound : exceptionalCandidate 2 ≤ thirdBound := by
  apply candidate_le
  · change ∀ j : Fin 3, Core.rootThreeCharacter (extra 2 j).left = 1 ∧
      middleCharacter (extra 2 j).left = 1
    decide +kernel
  · change ∀ j : CoreRoot, 4 ≤ j.val → Core.rootThreeCharacter (root j).left = 1 ∧
      middleCharacter (root j).left = 1
    decide +kernel

private theorem root_not_mem (i : Fin 3) : root 3 ∉ exceptionalCandidate i := by
  fin_cases i
  · intro h
    exact (by decide +kernel : coreCharacter (root 3) ≠ 1) (le_character_ker_zero h)
  · intro h
    exact (by decide +kernel : mixedCharacter (root 3) ≠ 1) (le_character_ker_one h)
  · intro h
    have hh := le_thirdBound h
    change Core.rootThreeCharacter (root 3).left = 1 ∧ middleCharacter (root 3).left = 1 at hh
    exact (by decide +kernel : middleCharacter (root 3).left ≠ 1) hh.2

/-- Each exceptional representative has a non-inner normalizer action in the
normal two-subgroup of automorphisms fixing its Frattini quotient. -/
public theorem exceptionalCandidate_not_intrinsic_radical (i : Fin 3) :
    ¬ ((exceptionalCandidate i).normalizerMonoidHom.range ⊓
      pCore 2 (MulAut (exceptionalCandidate i)) ≤
      (MulAut.conj : exceptionalCandidate i →* MulAut (exceptionalCandidate i)).range) := by
  intro h
  exact root_not_mem i
    (Subgroup.mem_of_intrinsic_radical_of_frattini_action_eq_one (exceptionalCandidate i)
      ((IsPGroup.of_card (n := 12) card).to_subgroup _) (candidate_centric i) h
      ⟨root 3, root_normalizes i⟩ (frattini_action i))

/-- Every Sylow conjugate of one of the three exceptional representatives fails
the intrinsic radical condition. -/
public theorem exceptionalCandidate_map_conj_not_intrinsic_radical (i : Fin 3) (g : SylowModel) :
    let E := (exceptionalCandidate i).map (MulAut.conj g).toMonoidHom
    ¬ (E.normalizerMonoidHom.range ⊓ pCore 2 (MulAut E) ≤
      (MulAut.conj : E →* MulAut E).range) := by
  dsimp only
  intro h
  exact exceptionalCandidate_not_intrinsic_radical i
    (Subgroup.intrinsic_radical_of_map_equiv (MulAut.conj g) (exceptionalCandidate i) 2 h)

end ReeTwo.SylowModel
