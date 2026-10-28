module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent

/-!
# The actual relative normalizer quotient

The carrier embeds faithfully in the split matrices. Split Borel-normalizer
separation therefore identifies the original intersection B ∩ N with the
original descended torus. The folded Weyl words normalize that torus and form
a complement, giving N/(B ∩ N) ≃ DihedralGroup 6. The quotient cells are the
published carrier cells, whose proved coverage gives generation by B and N.
The arm and central images are distinct involutions generating the quotient.

Normality is stated inside N. These results do not yet assert the folded
exchange or nontriviality axioms of a Tits system.
Source: GLS3 2.3.4(a–b), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
open scoped Pointwise
namespace Triality.Standard.ConcreteBruhat.RelativeNormalizer
open Parabolics FixedDescent
open Theory.AlgebraicGroup

theorem descend_eq_comap (P : Parameters) (hp : P.prime = 2)
    (H : Subgroup (SplitGroup P)) :
    descendSubgroup P H = H.comap (carrierToSplit P hp) :=
  Subgroup.ext (mem_descend_iff P hp H)

theorem weylRepresentative_mem_normalizer (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) : weylRepresentative P hp w ∈ normalizerCandidate P hp :=
  Subgroup.mem_sup_right ((weylRepresentativeHom_range P hp).le ⟨w, rfl⟩)

theorem carrierToSplit_simple (P : Parameters) (hp : P.prime = 2) (a : Node) :
    carrierToSplit P hp (simpleRepresentative P hp a) = splitRepresentative P hp (relativeReflection a) :=
  (congrArg (carrierToSplit P hp) (weylRepresentative_simple P hp a)).symm.trans
    (carrierToSplit_representative P hp (relativeReflection a))

/-- The candidate normalizer embeds in the original split normalizer. -/
theorem normalizer_le_comap_splitNormalizer (P : Parameters) (hp : P.prime = 2) :
    normalizerCandidate P hp ≤ (splitNormalizer P).comap (carrierToSplit P hp) := by
  apply sup_le
  · intro t ht
    exact Subgroup.mem_sup_left ((mem_descend_iff P hp (splitTorus P) t).mp ht)
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨a, rfl⟩
    change carrierToSplit P hp (simpleRepresentative P hp a) ∈ splitNormalizer P
    exact (carrierToSplit_simple P hp a).symm ▸
      Subgroup.mem_sup_right (splitRepresentative_mem P hp (relativeReflection a))

/-- All folded Weyl words normalize the original descended torus. -/
theorem weylRepresentative_normalizes_torus (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) : weylRepresentative P hp w ∈ Subgroup.normalizer (torus P) := by
  have ht : torus P = (splitTorus P).comap (carrierToSplit P hp) := descend_eq_comap P hp _
  have hm : carrierToSplit P hp (weylRepresentative P hp w) ∈
      Subgroup.normalizer (splitTorus P) :=
    (carrierToSplit_representative P hp w).symm ▸
      splitRepresentative_mem_normalizer_splitTorus P hp w
  exact ht.symm ▸ (Subgroup.le_normalizer_comap (carrierToSplit P hp) hm)

theorem weylSubgroup_normalizes_torus (P : Parameters) (hp : P.prime = 2) :
    Subgroup.closure (Set.range (simpleRepresentative P hp)) ≤ Subgroup.normalizer (torus P) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a, rfl⟩
  exact (weylRepresentative_simple P hp a) ▸
    weylRepresentative_normalizes_torus P hp (relativeReflection a)

/-- A faithful homomorphic section of the relative normalizer quotient. -/
def normalizerLift (P : Parameters) (hp : P.prime = 2) :
    DihedralGroup 6 →* normalizerCandidate P hp :=
  (weylRepresentativeHom P hp).codRestrict (normalizerCandidate P hp)
    (weylRepresentative_mem_normalizer P hp)

section Binary
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

/-- The original Borel-normalizer intersection is precisely the descended torus. -/
theorem borel_inf_normalizer : borel P ⊓ normalizerCandidate P rfl = torus P := by
  apply le_antisymm
  · rintro g ⟨hb, hn'⟩
    apply (mem_descend_iff P rfl (splitTorus P) g).mpr
    have hg : carrierToSplit P rfl g ∈ splitBorel P ⊓ splitNormalizer P :=
      ⟨(mem_descend_iff P rfl (splitBorel P) g).mp hb,
        normalizer_le_comap_splitNormalizer P rfl hn'⟩
    exact (SplitNormalForm.CellSeparation.borel_inf_normalizer n hn
      (InputRealization.inputs P rfl)).le hg
  · exact le_inf (torus_le_borel P) le_sup_left

/-- Normality is relative to the candidate normalizer, as the quotient requires. -/
theorem normalizer_intersection_normal :
    ((borel P ⊓ normalizerCandidate P rfl).subgroupOf (normalizerCandidate P rfl)).Normal := by
  rw [borel_inf_normalizer n hn]
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le (torus P).le_normalizer (weylSubgroup_normalizes_torus P rfl))

theorem representative_mem_borel_iff (w : DihedralGroup 6) :
    weylRepresentative P rfl w ∈ borel P ↔ w = 1 := by
  constructor
  · intro hw
    have hc : weylRepresentative P rfl w ∈ cell P rfl w :=
      (mem_cell_iff P rfl w _).mpr ⟨1, (borel P).one_mem, 1, (borel P).one_mem, by simp⟩
    exact FixedDescent.cell_index_unique n hn hc ((cell_one P rfl).ge hw)
  · rintro rfl
    exact (weylRepresentative_one P rfl).symm ▸ (borel P).one_mem

/-- The actual Borel and normalizer generate the carrier by the proved cell coverage. -/
theorem borel_sup_normalizer : borel P ⊔ normalizerCandidate P rfl = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨w, hw⟩ := FixedDescent.exists_mem_cell n hn g
  obtain ⟨b, hb, c, hc, rfl⟩ := (mem_cell_iff P rfl w g).mp hw
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
      (Subgroup.mem_sup_right (weylRepresentative_mem_normalizer P rfl w)))
    (Subgroup.mem_sup_left hc)

end Binary

theorem relativeReflection_generate : Subgroup.closure (Set.range relativeReflection) = ⊤ := by
  let H := Subgroup.closure (Set.range relativeReflection)
  have ha : DihedralGroup.sr (0 : ZMod 6) ∈ H := Subgroup.subset_closure ⟨.arms, rfl⟩
  have hc : DihedralGroup.sr (1 : ZMod 6) ∈ H := Subgroup.subset_closure ⟨.central, rfl⟩
  have hr : DihedralGroup.r (1 : ZMod 6) ∈ H := by
    simpa only [DihedralGroup.sr_mul_sr, sub_zero] using H.mul_mem ha hc
  have hrot (i : ZMod 6) : DihedralGroup.r i ∈ H := by
    simpa only [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] using H.pow_mem hr i.val
  apply top_unique
  intro w _
  cases w with
  | r i => exact hrot i
  | sr i => simpa only [DihedralGroup.sr_mul_r, zero_add] using H.mul_mem ha (hrot i)

section Quotient
variable (P : Parameters) (hp : P.prime = 2)
variable [((borel P ⊓ normalizerCandidate P hp).subgroupOf (normalizerCandidate P hp)).Normal]

def quotientLift : DihedralGroup 6 →*
    (normalizerCandidate P hp ⧸ (borel P ⊓ normalizerCandidate P hp).subgroupOf
      (normalizerCandidate P hp)) :=
  (QuotientGroup.mk' _).comp (normalizerLift P hp)

private theorem surjective_quotient_of_factors {G W : Type*} [Group G] [Group W]
    (H : Subgroup G) [H.Normal] (f : W →* G)
    (hf : ∀ g, ∃ t ∈ H, ∃ w, t * f w = g) :
    Function.Surjective ((QuotientGroup.mk' H).comp f) := by
  intro q
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H q
  obtain ⟨t, ht, w, hw⟩ := hf g
  refine ⟨w, ?_⟩
  have htq : QuotientGroup.mk' H t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
  have hm : QuotientGroup.mk' H (t * f w) = QuotientGroup.mk' H (f w) := by
    rw [map_mul, htq, one_mul]
  exact hm.symm.trans ((congrArg (QuotientGroup.mk' H) hw).trans hg)

theorem quotientLift_surjective : Function.Surjective (quotientLift P hp) := by
  apply surjective_quotient_of_factors
  intro g
  have hg := g.property
  change g.val ∈ torus P ⊔ Subgroup.closure (Set.range (simpleRepresentative P hp)) at hg
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (weylSubgroup_normalizes_torus P hp)] at hg
  obtain ⟨t, ht, v, hv, htv⟩ := hg
  obtain ⟨w, hw⟩ := (weylRepresentativeHom_range P hp).ge hv
  let tN : normalizerCandidate P hp := ⟨t, Subgroup.mem_sup_left ht⟩
  exact ⟨tN, ⟨torus_le_borel P ht, tN.property⟩, w,
    Subtype.ext ((congrArg (fun z => t * z) hw).trans htv)⟩

end Quotient

section BinaryQuotient
variable (n : ℕ) (hn : 0 < n)
variable [((borel (binaryParameters n hn) ⊓ normalizerCandidate (binaryParameters n hn) rfl).subgroupOf (normalizerCandidate (binaryParameters n hn) rfl)).Normal]

theorem quotientLift_injective : Function.Injective (quotientLift (binaryParameters n hn) rfl) := by
  apply (injective_iff_map_eq_one _).mpr
  intro w hw
  exact (representative_mem_borel_iff n hn w).mp
    (((QuotientGroup.eq_one_iff (normalizerLift (binaryParameters n hn) rfl w)).mp hw).1)

/-- The normalizer quotient, with its actual Borel intersection, is dihedral of order twelve. -/
def quotientEquiv : DihedralGroup 6 ≃*
    (normalizerCandidate (binaryParameters n hn) rfl ⧸ (borel (binaryParameters n hn) ⊓ normalizerCandidate (binaryParameters n hn) rfl).subgroupOf
      (normalizerCandidate (binaryParameters n hn) rfl)) :=
  MulEquiv.ofBijective (quotientLift (binaryParameters n hn) rfl)
    ⟨quotientLift_injective n hn, quotientLift_surjective (binaryParameters n hn) rfl⟩

theorem quotient_card : Nat.card (normalizerCandidate (binaryParameters n hn) rfl ⧸
    (borel (binaryParameters n hn) ⊓ normalizerCandidate (binaryParameters n hn) rfl).subgroupOf (normalizerCandidate (binaryParameters n hn) rfl)) = 12 := by
  rw [← Nat.card_congr (quotientEquiv n hn).toEquiv, DihedralGroup.nat_card]

/-- The quotient cells are exactly the original carrier cells. -/
theorem cell_eq_quotient_cell (w : DihedralGroup 6) : cell (binaryParameters n hn) rfl w =
    (borel (binaryParameters n hn) : Set (Carrier (binaryParameters n hn))) * TitsSystem.representativeSet (borel (binaryParameters n hn))
      (normalizerCandidate (binaryParameters n hn) rfl) (quotientEquiv n hn w) * (borel (binaryParameters n hn) : Set (Carrier (binaryParameters n hn))) :=
  (TitsSystem.B_mul_representativeSet_mul_B (borel (binaryParameters n hn)) (normalizerCandidate (binaryParameters n hn) rfl)
    (quotientEquiv n hn w) (normalizerLift (binaryParameters n hn) rfl w) rfl).symm

/-- The two distinguished generators of the actual normalizer quotient. -/
def simpleReflection (a : Node) := quotientEquiv n hn (relativeReflection a)

theorem simpleReflection_ne (a b : Node) (hab : a ≠ b) :
    simpleReflection n hn a ≠ simpleReflection n hn b :=
  fun h => relativeReflection_ne a b hab ((quotientEquiv n hn).injective h)

theorem simpleReflection_involution (a : Node) :
    simpleReflection n hn a ≠ 1 ∧ simpleReflection n hn a ^ 2 = 1 := by
  have h := relativeReflection_involution a
  constructor
  · intro he
    exact h.1 ((quotientEquiv n hn).injective (he.trans (map_one _).symm))
  · exact (map_pow (quotientEquiv n hn) _ 2).symm.trans
      ((congrArg (quotientEquiv n hn) h.2).trans (map_one _))

theorem mem_simpleReflection_range (w) : w ∈ Set.range (simpleReflection n hn) ↔
    w = simpleReflection n hn .arms ∨ w = simpleReflection n hn .central := by
  constructor
  · rintro ⟨a, rfl⟩
    cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Set.mem_range_self _
    · exact Set.mem_range_self _

theorem simpleReflection_generate : Subgroup.closure (Set.range (simpleReflection n hn)) = ⊤ := by
  change Subgroup.closure (Set.range ((quotientEquiv n hn).toMonoidHom ∘ relativeReflection)) = ⊤
  rw [Set.range_comp, ← MonoidHom.map_closure, relativeReflection_generate]
  exact Subgroup.map_top_of_surjective _ (quotientEquiv n hn).surjective

end BinaryQuotient
end Triality.Standard.ConcreteBruhat.RelativeNormalizer
