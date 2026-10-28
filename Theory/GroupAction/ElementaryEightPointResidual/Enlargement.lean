module
public import Theory.GroupAction.ElementaryEightPointResidual.Conjugation
public import Theory.GroupTheory.ElementaryEightSylowFour
public import Theory.GroupTheory.ElementaryEightFixedPointOrder24
public import Theory.GroupAction.ElementaryEightPointEnlargement
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Two distinct fixed lines on the same elementary eight-group

An automorphism subgroup containing an order-twelve subgroup with a unique
nonidentity fixed point is the full GL₃(2) as soon as it moves that point.
The possible subgroup orders are 12, 24, 84, 168. At 24 the order-twelve
subgroup is normal, so its unique fixed point is preserved. The Sylow-four
calculation excludes 84. Thus two residual images with distinct fixed
lines require only one order-twelve image to generate the full action.

The conjugation application preserves the literal image and centralizer
kernel. It leaves the simultaneous cubic alternative explicit. In the
full-image branch the actual point-normalizer images are the full point
stabilizers, each isomorphic to S₄, and the original normalizer modulo its
action kernel is the concrete PSL₃(2). No ambient component recognition
or exclusion of the cubic branch is asserted.

Source application: Aschbacher–Smith, 14.7.6, printed pp.1044–1045 of
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupAction.ElementaryEightPointResidual
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

omit [Finite E] [IsElementaryAbelian 2 E] in
private theorem normalizer_fixes_unique_point
    (B : Subgroup (MulAut E)) (z : E) (hz : z ≠ 1)
    (hfix : ∀ b : B, (b : MulAut E) z = z)
    (hunique : ∀ x : E, (∀ b : B, (b : MulAut E) x = x) → x = 1 ∨ x = z) :
    normalizer (B : Set (MulAut E)) ≤ MulAction.stabilizer (MulAut E) z := by
  intro a ha
  have hb (b : B) : (b : MulAut E) (a z) = a z := by
    have hc : a⁻¹ * b * a ∈ B :=
      (mem_normalizer_iff.mp ((normalizer (B : Set (MulAut E))).inv_mem ha) b).mp b.property
    have hh := congrArg (fun f : E => a f) (hfix ⟨a⁻¹ * b * a,hc⟩)
    simpa using hh
  rcases hunique (a z) hb with he | he
  · exact (hz (a.injective (he.trans a.map_one.symm))).elim
  · exact he

/-- One order-twelve point image and an automorphism moving its unique
nonidentity fixed point generate the full automorphism group. -/
theorem eq_top_of_twelve_point_image_of_moves
    (hE : Nat.card E = 8) (A B : Subgroup (MulAut E))
    (hBA : B ≤ A) (hB : Nat.card B = 12)
    (z : E) (hz : z ≠ 1)
    (hfix : ∀ b : B, (b : MulAut E) z = z)
    (hunique : ∀ x : E, (∀ b : B, (b : MulAut E) x = x) → x = 1 ∨ x = z)
    (hmoves : ∃ a ∈ A, a z ≠ z) : A = ⊤ := by
  have hdiv : Nat.card A ∣ 168 := (card_mulAut_of_elementary_eight E hE) ▸ A.card_subgroup_dvd_card
  have h12 : 12 ∣ Nat.card A := hB ▸ card_dvd_of_le hBA
  have hc : Nat.card A = 12 ∨ Nat.card A = 24 ∨ Nat.card A = 84 ∨ Nat.card A = 168 := by
    have hm := Nat.mem_divisors.mpr ⟨hdiv,(by decide : (168 : ℕ) ≠ 0)⟩
    have hd : (168 : ℕ).divisors = {1,2,3,4,6,7,8,12,14,21,24,28,42,56,84,168} := by decide
    rw [hd] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    omega
  rcases hc with hc | hc | hc | hc
  · have he : B = A := eq_of_le_of_card_ge hBA (by omega)
    obtain ⟨a,ha,hmove⟩ := hmoves
    exact (hmove (hfix ⟨a,he.symm ▸ ha⟩)).elim
  · have hcard : Nat.card (B.subgroupOf A) = 12 :=
      (Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv).trans hB
    have hi : (B.subgroupOf A).index = 2 := by
      have hh := (B.subgroupOf A).card_mul_index
      rw [hcard,hc] at hh
      omega
    have hn : A ≤ normalizer (B : Set (MulAut E)) :=
      (normal_subgroupOf_iff_le_normalizer hBA).mp (normal_of_index_eq_two hi)
    have hAZ := hn.trans (normalizer_fixes_unique_point B z hz hfix hunique)
    obtain ⟨a,ha,hmove⟩ := hmoves
    exact (hmove (hAZ ha)).elim
  · let P : Sylow 2 A := Classical.choice inferInstance
    have hP : Nat.card P = 4 := by rw [P.card_eq_multiplicity,hc]; decide +kernel
    have hh := card_eq_four_or_twelve_of_elementary_eight_automorphisms E hE A P hP
    omega
  · exact eq_top_of_card_eq A (hc.trans (card_mulAut_of_elementary_eight E hE).symm)

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The fixed points of the literal image are the original centralizer. -/
theorem fixed_by_conjugationImage_iff
    (B C : Subgroup G) (hn : B ≤ normalizer (C : Set G)) (x : C) :
    (∀ b : conjugationImage B C, (b : MulAut C) x = x) ↔
      (x : G) ∈ centralizer (B : Set G) := by
  rw [conjugationImage_eq_range B C hn]
  constructor
  · intro hx b hb
    have hh := congrArg (fun c : C => (c : G)) (hx ⟨_,⟨⟨b,hb⟩,rfl⟩⟩)
    rw [conjugationAction_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro hx b
    obtain ⟨b,hb⟩ := b.property
    rw [←hb]
    apply Subtype.ext
    rw [conjugationAction_apply]
    rw [hx b b.property,mul_inv_cancel_right]

/-- An actual order-twelve endpoint image and a distinct fixed line at
the other endpoint force the full ambient normalizer image. -/
theorem normalizer_image_eq_top_of_twelve_of_distinct_fixed_lines
    (B D C Z W : Subgroup G) [IsElementaryAbelian 2 C]
    (hc : Nat.card C = 8) (hz : Nat.card Z = 2) (hw : Nat.card W = 2)
    (hnB : B ≤ normalizer (C : Set G)) (hnD : D ≤ normalizer (C : Set G))
    (hfixedB : C ⊓ centralizer (B : Set G) = Z)
    (hfixedD : C ⊓ centralizer (D : Set G) = W)
    (hne : Z ≠ W) (hB : Nat.card (conjugationImage B C) = 12) :
    conjugationImage (normalizer (C : Set G)) C = ⊤ := by
  obtain ⟨z,hz1,hzu⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hz
  have hZC : Z ≤ C := hfixedB ▸ inf_le_left
  let zC : C := ⟨z,hZC z.property⟩
  have hzC : zC ≠ 1 := fun he => hz1 (Subtype.ext (congrArg (fun c : C => (c : G)) he))
  have hfix : ∀ b : conjugationImage B C, (b : MulAut C) zC = zC :=
    (fixed_by_conjugationImage_iff B C hnB zC).mpr (show (z : G) ∈ C ⊓ centralizer (B : Set G) from hfixedB.symm ▸ z.property).2
  have huniq (x : C) (hx : ∀ b : conjugationImage B C, (b : MulAut C) x = x) :
      x = 1 ∨ x = zC := by
    have hxZ : (x : G) ∈ Z := hfixedB ▸
      (show (x : G) ∈ C ⊓ centralizer (B : Set G) from
        ⟨x.property,(fixed_by_conjugationImage_iff B C hnB x).mp hx⟩)
    by_cases h1 : x = 1
    · exact Or.inl h1
    · right
      apply Subtype.ext
      exact congrArg (fun v : Z => (v : G)) (hzu ⟨x,hxZ⟩
        (fun he => h1 (Subtype.ext (congrArg (fun v : Z => (v : G)) he))))
  have hmove : ∃ a ∈ conjugationImage (normalizer (C : Set G)) C, a zC ≠ zC := by
    by_contra! hn
    have hzD : (z : G) ∈ centralizer (D : Set G) :=
      (fixed_by_conjugationImage_iff D C hnD zC).mp
        (fun a => hn a (conjugationImage_mono hnD a.property))
    have hzW : (z : G) ∈ W := hfixedD ▸ ⟨hZC z.property,hzD⟩
    have hZW : Z ≤ W := by
      intro x hx
      by_cases he : x = 1
      · simpa only [he] using W.one_mem
      · have hxe : (⟨x,hx⟩ : Z) = z := hzu _ (fun heq => he (congrArg Subtype.val heq))
        have hxeG : x = (z : G) := congrArg Subtype.val hxe
        rwa [hxeG]
    exact hne (eq_of_le_of_card_ge hZW (by omega))
  exact eq_top_of_twelve_point_image_of_moves hc _ _
    (conjugationImage_mono hnB) hB zC hzC hfix huniq hmove

/-- For the two original cubic residuals there is only one outstanding
action branch: both images are cubic. Otherwise the full normalizer is GL₃(2). -/
theorem cubic_pair_or_full_normalizer
    (B D C Z W : Subgroup G) [IsElementaryAbelian 2 C]
    (hc : Nat.card C = 8) (hz : Nat.card Z = 2) (hw : Nat.card W = 2)
    (hnB : B ≤ normalizer (C : Set G)) (hnD : D ≤ normalizer (C : Set G))
    (hfixedB : C ⊓ centralizer (B : Set G) = Z)
    (hfixedD : C ⊓ centralizer (D : Set G) = W) (hne : Z ≠ W)
    (hB : Nat.card (conjugationImage B C) = 3 ∨ Nat.card (conjugationImage B C) = 12)
    (hD : Nat.card (conjugationImage D C) = 3 ∨ Nat.card (conjugationImage D C) = 12) :
    (Nat.card (conjugationImage B C) = 3 ∧ Nat.card (conjugationImage D C) = 3) ∨
      conjugationImage (normalizer (C : Set G)) C = ⊤ := by
  rcases hB with hB | hB
  · rcases hD with hD | hD
    · exact Or.inl ⟨hB,hD⟩
    · exact Or.inr (normalizer_image_eq_top_of_twelve_of_distinct_fixed_lines
        D B C W Z hc hw hz hnD hnB hfixedD hfixedB hne.symm hD)
  · exact Or.inr (normalizer_image_eq_top_of_twelve_of_distinct_fixed_lines
      B D C Z W hc hz hw hnB hnD hfixedB hfixedD hne hB)


/-- The full stabilizer of any nonidentity point has order twenty-four
and is the concrete symmetric group on four letters. -/
theorem full_point_stabilizer
    (hE : Nat.card E = 8) (z : E) (hz : z ≠ 1) :
    Nat.card (MulAction.stabilizer (MulAut E) z) = 24 ∧
      Nonempty (MulAction.stabilizer (MulAut E) z ≃* Equiv.Perm (Fin 4)) := by
  classical
  let A := MulAction.stabilizer (MulAut E) z
  have hle : Nat.card A ≤ 24 := Nat.le_of_dvd (by decide)
    (elementaryEight_fixed_point_image_card_dvd_twentyfour hE z hz A (fun a => a.property))
  have ho : Nat.card (MulAction.orbit (MulAut E) z) ≤ 7 := by
    let f : MulAction.orbit (MulAut E) z → {x : E // x ≠ 1} := fun x =>
      ⟨x,by
        obtain ⟨a,ha⟩ := MulAction.mem_orbit_iff.mp x.property
        intro hx
        exact hz (a.injective ((ha.trans hx).trans a.map_one.symm))⟩
    have hf : Function.Injective f := fun x y he => Subtype.ext (congrArg (fun y : {x : E // x ≠ 1} => (y : E)) he)
    have hb := Nat.card_le_card_of_injective f hf
    let : Fintype E := Fintype.ofFinite E
    have hc : Nat.card {x : E // x ≠ 1} = 7 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
      simp only [Fintype.card_unique,←Nat.card_eq_fintype_card,hE]
    exact hb.trans hc.le
  have hm := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (MulAut E) z)
  rw [Nat.card_prod,card_mulAut_of_elementary_eight E hE] at hm
  have hc : Nat.card A = 24 := by
    change Nat.card (MulAction.orbit (MulAut E) z) * Nat.card A = 168 at hm
    nlinarith
  exact ⟨hc,elementaryEight_fixed_point_order24_equiv_S4 hE z hz A hc (fun a => a.property)⟩

/-- Surjectivity of the ambient action identifies the literal point
normalizer image with the full point stabilizer, including its S₄ model. -/
theorem point_normalizer_image_of_full_normalizer
    (C Z : Subgroup G) [IsElementaryAbelian 2 C]
    (hc : Nat.card C = 8) (hz : Nat.card Z = 2) (hZC : Z ≤ C)
    (hfull : conjugationImage (normalizer (C : Set G)) C = ⊤) :
    ∃ z : C, z ≠ 1 ∧ (z : G) ∈ Z ∧
      conjugationImage (normalizer (C : Set G) ⊓ normalizer (Z : Set G)) C =
        MulAction.stabilizer (MulAut C) z ∧
      Nat.card (conjugationImage (normalizer (C : Set G) ⊓ normalizer (Z : Set G)) C) = 24 ∧
      Nonempty (conjugationImage (normalizer (C : Set G) ⊓ normalizer (Z : Set G)) C ≃*
        Equiv.Perm (Fin 4)) := by
  obtain ⟨z,hz1,hzu⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hz
  let zC : C := ⟨z,hZC z.property⟩
  have hzC : zC ≠ 1 := fun he => hz1 (Subtype.ext (congrArg (fun c : C => (c : G)) he))
  let N := normalizer (C : Set G) ⊓ normalizer (Z : Set G)
  have he : conjugationImage N C = MulAction.stabilizer (MulAut C) zC := by
    rw [conjugationImage_eq_range N C inf_le_left]
    apply le_antisymm
    · rintro _ ⟨g,rfl⟩
      change conjugationAction N C inf_le_left g zC = zC
      apply Subtype.ext
      rw [conjugationAction_apply]
      have hg : (g : G) ∈ centralizer (Z : Set G) :=
        normalizer_le_centralizer_of_card_two Z hz g.property.2
      rw [←hg z z.property,mul_inv_cancel_right]
    · intro a ha
      have hs : Function.Surjective C.normalizerMonoidHom :=
        MonoidHom.range_eq_top.mp ((conjugationImage_normalizer C).symm.trans hfull)
      obtain ⟨g,hg⟩ := hs a
      have hgz : (g : G) * (z : G) * (g : G)⁻¹ = z := by
        have hh := congrArg (fun f : MulAut C => (f zC : G)) hg
        exact hh.trans (congrArg (fun c : C => (c : G)) ha)
      have hgc : (g : G) ∈ centralizer (Z : Set G) := by
        intro x hx
        by_cases hx1 : x = 1
        · simp only [hx1,mul_one,one_mul]
        · have hxz : x = (z : G) := congrArg Subtype.val
            (hzu ⟨x,hx⟩ (fun heq => hx1 (congrArg Subtype.val heq)))
          rw [hxz]
          exact (mul_inv_eq_iff_eq_mul.mp hgz).symm
      let gN : N := ⟨g,g.property,(Subgroup.centralizer_le_normalizer _) hgc⟩
      refine ⟨gN,?_⟩
      apply MulEquiv.ext
      intro c
      apply Subtype.ext
      rw [conjugationAction_apply]
      exact congrArg (fun f : MulAut C => (f c : G)) hg
  obtain ⟨hcard,hmodel⟩ := full_point_stabilizer hc zC hzC
  exact ⟨zC,hzC,z.property,he,he ▸ hcard,he ▸ hmodel⟩

/-- The full action identifies the actual normalizer modulo its literal
centralizer kernel with the concrete PSL₃(2) model. -/
theorem normalizer_quotient_of_full_image
    (C : Subgroup G) [IsElementaryAbelian 2 C] (hc : Nat.card C = 8)
    (hfull : conjugationImage (normalizer (C : Set G)) C = ⊤) :
    Nonempty (((normalizer (C : Set G)) ⧸ C.normalizerMonoidHom.ker) ≃*
      Matrix.PSL3Two.PSL) := by
  have hs : Function.Surjective C.normalizerMonoidHom :=
    MonoidHom.range_eq_top.mp ((conjugationImage_normalizer C).symm.trans hfull)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective C.normalizerMonoidHom hs).trans
    (MulAut.elementaryEight_equiv_PSL3 hc).some⟩

end Theory.GroupAction.ElementaryEightPointResidual
