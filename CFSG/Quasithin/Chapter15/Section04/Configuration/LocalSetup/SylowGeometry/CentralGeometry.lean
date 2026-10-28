module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Hyperplanes
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Geometry
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# Central fixed subgroups for the four factor choices

Aschbacher–Smith, combined manuscript (1 March 2004), 15.4.19,
printed p.1163. The uniqueness overgroups separate the actual omega-center
from the center of each amalgam, and force each factor outside the other
maximal local. Two fixed hyperplanes then have intersection of codimension
at most two; a disjoint central four-group complements that intersection.
Counting the product with the fixed line yields the required nontrivial
intersection with `Z(I)V₁`.

The fixed-hyperplane and fixed-line inputs to the last calculation have not
yet been constructed from 15.4.12(5–6). They are explicit intermediate
hypotheses, not additional clauses of the earlier source theorem. All centers
and two-cores used here are intrinsic subgroups mapped into the ambient group.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The finite dimension calculation: two hyperplanes in a group of order at least eight
have nontrivial intersection, and a disjoint four-group meets any additional line modulo it. -/
theorem central_intersection_of_two_hyperplanes {E E₁ E₂ Z F : Subgroup G} [IsMulCommutative E]
    (h₁ : E₁ ≤ E) (h₂ : E₂ ≤ E) (hZ : Z ≤ E) (hF : F ≤ E)
    (hi₁ : E₁.relIndex E = 2) (hi₂ : E₂.relIndex E = 2)
    (hlarge : 4 < Nat.card E) (hZcard : Nat.card Z = 4)
    (hdisZ : (E₁ ⊓ E₂) ⊓ Z = ⊥)
    (hFcard : Nat.card F = 2) (hdisF : (E₁ ⊓ E₂) ⊓ F = ⊥) :
    E₁ ⊓ E₂ ≠ ⊥ ∧ (E₁ ⊓ E₂) ⊔ Z = E ∧
      Z ⊓ ((E₁ ⊓ E₂) ⊔ F) ≠ ⊥ := by
  let A := E₁ ⊓ E₂
  have hA : A ≤ E := (inf_le_inf h₁ h₂).trans inf_le_left
  have hindex : A.relIndex E ≤ 4 := by
    simpa only [hi₁, hi₂] using (relIndex_inf_le (H := E₁) (K := E₂) (L := E))
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) A E bot_le hA
  simp only [relIndex_bot_left] at hcard
  have hupper : Nat.card E ≤ 4 * Nat.card A := by nlinarith
  have hAne : A ≠ ⊥ := by
    intro heq
    have ha1 : Nat.card A = 1 := heq ▸ card_bot
    omega
  have hnorm (U V : Subgroup G) (hU : U ≤ E) (hV : V ≤ E) :
      V ≤ normalizer (U : Set G) :=
    ((hV.trans (le_centralizer E)).trans (centralizer_le hU)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hAZ : Nat.card (A ⊔ Z : Subgroup G) = Nat.card A * 4 := by
    simpa only [hZcard] using card_sup_eq_mul_of_normalizes_of_disjoint A Z
      (hnorm A Z hA hZ) (disjoint_iff.mpr hdisZ)
  have hAZeq : A ⊔ Z = E := eq_of_le_of_card_ge (sup_le hA hZ) (by omega)
  have hAF : Nat.card (A ⊔ F : Subgroup G) = Nat.card A * 2 := by
    simpa only [hFcard] using card_sup_eq_mul_of_normalizes_of_disjoint A F
      (hnorm A F hA hF) (disjoint_iff.mpr hdisF)
  refine ⟨hAne, hAZeq, ?_⟩
  intro hbot
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z (A ⊔ F)
    (hnorm Z (A ⊔ F) hZ (sup_le hA hF))
  rw [hZcard, hbot, card_bot, one_mul, hAF] at hprod
  have hbound : Nat.card (Z ⊔ (A ⊔ F) : Subgroup G) ≤ Nat.card E :=
    card_le_of_le (sup_le hZ (sup_le hA hF))
  have hpos : 0 < Nat.card A := Nat.card_pos
  nlinarith

omit [Finite G] in
/-- Centralization inside a subgroup uses the image of its intrinsic center. -/
theorem fixed_subgroup_le_center_image {E I : Subgroup G} (hEI : E ≤ I) :
    E ⊓ centralizer (I : Set G) ≤ (center I).map I.subtype := by
  rintro x ⟨hxE, hxC⟩
  refine ⟨⟨x, hEI hxE⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro i
  exact Subtype.ext (mem_centralizer_iff.mp hxC i i.property)

omit [Finite G] in
/-- A nontrivial central two-subgroup lies in the intrinsic two-core. -/
theorem mem_H_of_nontrivial_fixed_subgroup {E I : Subgroup G} (hE : IsPGroup 2 E)
    (hEI : E ≤ I) (hne : E ⊓ centralizer (I : Set G) ≠ ⊥) :
    I ∈ Chapter1.H G := by
  intro hbot
  apply hne
  apply le_bot_iff.mp
  rw [← hbot]
  apply le_pCoreIn_of_normalizes (hE.to_le inf_le_left) (inf_le_left.trans hEI)
  exact (le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
/-- The fixed subgroup of a join is the intersection of the two fixed subgroups. -/
theorem fixed_subgroup_join (E A B : Subgroup G) :
    E ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G) =
      (E ⊓ centralizer (A : Set G)) ⊓ (E ⊓ centralizer (B : Set G)) := by
  apply le_antisymm
  · exact le_inf (inf_le_inf_left E (centralizer_le (show A ≤ A ⊔ B from le_sup_left)))
      (inf_le_inf_left E (centralizer_le (show B ≤ A ⊔ B from le_sup_right)))
  · apply le_inf (inf_le_left.trans inf_le_left)
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp (inf_le_left.trans inf_le_right)
    · exact le_centralizer_iff.mp (inf_le_right.trans inf_le_right)

omit [Finite G] in
/-- 15.4.19(2) for both factors of both actual normalizer overgroups. -/
theorem outside_factors
    (d : Source.Geometry G)
    (hXgen : ∀ i, d.X i ⊔ (d.T : Subgroup G) = d.wholeX ⊔ (d.T : Subgroup G))
    (hYgen : ∀ j, d.Y j ⊔ (d.T : Subgroup G) = d.wholeY ⊔ (d.T : Subgroup G))
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ M → M = d.M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeY ⊔ (d.T : Subgroup G) ≤ M → M = d.M₂)
    (hM₁ : IsMaximalTwoLocal d.M₁) (hM₂ : IsMaximalTwoLocal d.M₂)
    (hT₁ : (d.T : Subgroup G) ≤ d.M₁) (hT₂ : (d.T : Subgroup G) ≤ d.M₂)
    (hne : d.M₁ ≠ d.M₂) :
    (∀ i, ¬ d.X i ≤ d.M₂) ∧ (∀ j, ¬ d.Y j ≤ d.M₁) := by
  exact ⟨fun i => factor_not_le_other
    (hXgen i) huniqueX hM₂ hT₂ hne,
    fun j => factor_not_le_other
      (hYgen j) huniqueY hM₁ hT₁ hne.symm⟩

/-- The first paragraph of the proof of 15.4.19: no nonidentity element of the
actual omega-center can centralize either generated amalgam. -/
theorem center_image_disjoint_Z
    (d : Source.Geometry G)
    (hZ : d.Z = Stellmacher.omegaOneCenterAmbient (d.T : Subgroup G))
    (hXgen : ∀ i, d.X i ⊔ (d.T : Subgroup G) = d.wholeX ⊔ (d.T : Subgroup G))
    (hYgen : ∀ j, d.Y j ⊔ (d.T : Subgroup G) = d.wholeY ⊔ (d.T : Subgroup G))
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ M → M = d.M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeY ⊔ (d.T : Subgroup G) ≤ M → M = d.M₂)
    (hne : d.M₁ ≠ d.M₂) (i j : Bool) :
    d.Z ⊓ (center (d.I i j)).map (d.I i j).subtype = ⊥ := by
  let : IsElementaryAbelian 2 d.Z := hZ ▸
    Stellmacher.omegaOneCenterAmbient_elementaryAbelian (d.T : Subgroup G)
  have hTC : (d.T : Subgroup G) ≤ centralizer (d.Z : Set G) := by
    intro t ht
    rw [mem_centralizer_iff]
    intro z hz
    rw [hZ] at hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht |>.symm
  have hd := centralizers_disjoint_of_unique hTC
    (fun M hM hXM => huniqueX M hM ((hXgen i) ▸ hXM))
    (fun M hM hYM => huniqueY M hM ((hYgen j) ▸ hYM)) hne
  apply le_bot_iff.mp
  rw [← hd]
  intro z hz
  obtain ⟨zI, hzI, rfl⟩ := hz.2
  have hzcentral := mem_center_iff.mp hzI
  refine ⟨⟨hz.1, ?_⟩, ⟨hz.1, ?_⟩⟩
  · apply mem_centralizer_iff.mpr
    intro x hx
    exact congrArg Subtype.val (hzcentral ⟨x, d.X_le_I i j hx⟩)
  · apply mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (hzcentral ⟨y, d.Y_le_I i j hy⟩)

/-- The actual omega-center of the Thompson subgroup lies in the Baumann subgroup. -/
theorem thompsonAlpha_le_baumann (T : Subgroup G) :
    ChapterB.thompsonAlpha T ≤ ChapterB.baumann T := by
  let E := ChapterB.thompsonAlpha T
  let : IsElementaryAbelian 2 E :=
    Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  apply le_inf _ (le_centralizer E)
  change ChapterB.thompsonAlpha T ≤ T
  rw [ChapterB.thompsonAlpha_eq]
  intro x hx
  exact ChapterB.thompsonJ_le T 0
    (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx).1)

/-- The central-geometry calculation with the actual `E = Ω₁(Z(J(T)))` and
commutator module `V₁`. Construction of the displayed fixed hyperplanes, the
fixed line, and the lower order bound from 15.4.12(5–6) is still required;
this conditional lemma alone does not establish 15.4.19(1,3). -/
theorem central_geometry_of_fixed_hyperplanes
    (d : Source.Geometry G)
    (hS : ChapterB.baumann (d.T : Subgroup G) ≤ d.T₀)
    (hZcard : Nat.card d.Z = 4) (i j : Bool)
    (hZi : d.Z ≤ ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.T₀ : Set G))
    (hZdis : d.Z ⊓ (center (d.I i j)).map (d.I i j).subtype = ⊥)
    (hlarge : 4 < Nat.card
      ↥(ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.T₀ : Set G)))
    (hhyper₁ : (ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓
      centralizer (d.G₁ i : Set G)).relIndex
        (ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.T₀ : Set G)) = 2)
    (hhyper₂ : (ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓
      centralizer (d.G₂ j : Set G)).relIndex
        (ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.T₀ : Set G)) = 2)
    (hF : d.V₁ i ⊓ centralizer (d.T₀ : Set G) ≤ ChapterB.thompsonAlpha (d.T : Subgroup G))
    (hFcard : Nat.card ↥(d.V₁ i ⊓ centralizer (d.T₀ : Set G)) = 2)
    (hdisF : (ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.G₁ i : Set G)) ⊓
      (d.V₁ i ⊓ centralizer (d.T₀ : Set G)) = ⊥) :
    ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.I i j : Set G) ≠ ⊥ ∧
    ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.I i j : Set G) ≤
      (center (d.I i j)).map (d.I i j).subtype ∧
    d.I i j ∈ Chapter1.H G ∧
    d.Z ⊓ ((center (d.I i j)).map (d.I i j).subtype ⊔ d.V₁ i) ≠ ⊥ := by
  let E := ChapterB.thompsonAlpha (d.T : Subgroup G)
  let EI := E ⊓ centralizer (d.T₀ : Set G)
  let E₁ := E ⊓ centralizer (d.G₁ i : Set G)
  let E₂ := E ⊓ centralizer (d.G₂ j : Set G)
  let E₀ := E ⊓ centralizer (d.I i j : Set G)
  let F := d.V₁ i ⊓ centralizer (d.T₀ : Set G)
  have hEI₀ : E ≤ d.T₀ := (thompsonAlpha_le_baumann _).trans hS
  have hEI : E ≤ d.I i j := hEI₀.trans (d.T₀_le_I i j)
  have hc : E₀ ≤ (center (d.I i j)).map (d.I i j).subtype := fixed_subgroup_le_center_image hEI
  have heq : E₀ = E₁ ⊓ E₂ := fixed_subgroup_join E (d.G₁ i) (d.G₂ j)
  let : IsElementaryAbelian 2 E :=
    Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  let : IsMulCommutative EI := le_centralizer_iff_isMulCommutative.mp
    ((show EI ≤ E from inf_le_left).trans ((le_centralizer E).trans
      (centralizer_le (show EI ≤ E from inf_le_left))))
  have h₁ : E₁ ≤ EI := inf_le_inf_left E (centralizer_le (show d.T₀ ≤ d.G₁ i from le_sup_right))
  have h₂ : E₂ ≤ EI := inf_le_inf_left E (centralizer_le (show d.T₀ ≤ d.G₂ j from le_sup_right))
  have hzdis : (E₁ ⊓ E₂) ⊓ d.Z = ⊥ := by
    apply le_bot_iff.mp
    rw [← heq]
    exact (le_inf inf_le_right (inf_le_left.trans hc)).trans_eq hZdis
  have hfdis : (E₁ ⊓ E₂) ⊓ F = ⊥ := by
    apply le_bot_iff.mp
    exact (inf_le_inf_right F (show E₁ ⊓ E₂ ≤ E₁ from inf_le_left)).trans_eq hdisF
  obtain ⟨h₀, _, hzmeet⟩ := central_intersection_of_two_hyperplanes h₁ h₂ hZi (le_inf hF inf_le_right)
    hhyper₁ hhyper₂ hlarge hZcard hzdis hFcard hfdis
  rw [← heq] at h₀ hzmeet
  refine ⟨h₀, hc, mem_H_of_nontrivial_fixed_subgroup (IsElementaryAbelian.isPGroup 2 E) hEI h₀, ?_⟩
  intro hbot
  apply hzmeet
  apply le_bot_iff.mp
  exact (inf_le_inf_left d.Z (sup_le_sup hc (show F ≤ d.V₁ i from inf_le_left))).trans_eq hbot

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
