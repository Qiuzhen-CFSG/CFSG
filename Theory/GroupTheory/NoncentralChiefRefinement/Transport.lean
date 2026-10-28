module

public import Theory.GroupTheory.NoncentralChiefRefinement.Actions

/-!
# Equivariant transport of normal chief sections

The diamond isomorphism identifies `(A ⊔ B)/A` with `B/(A ⊓ B)` using the
inclusion of B and its exact kernel. The representative formula shows that
this isomorphism intertwines ambient conjugation. Interpreting the generated
Jordan–Hölder interval relation this way gives a bijection of the actual
factors of any two chief series with equal endpoints, preserving their
actions and hence their noncentral two-chief counts.

For a normal subgroup Q, normal-subgroup correspondence preserves chief
intervals above Q. The map induced by `K → K/Q` identifies their literal
relative sections, with its representative and conjugation formulas.
Consequently, the absence of all two-chief factors in `K/Q` excludes every
two-chief interval above Q, including central intervals, and makes the
terminal part of any chief series contribute zero to the count.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.2.5(8), printed pp.335–336 (PDF pp.346–347). These are the series-independence
and terminal-quotient steps of the refinement argument; the terminal
`HasNoTwoChiefFactors` premise is supplied by the source assembly.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K]
private def diamondHom (A B : NormalNode K) : B.val →* Section A (A ⊔ B) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right)

private theorem diamondHom_ker (A B : NormalNode K) :
    (A ⊓ B).val.subgroupOf B.val = (diamondHom A B).ker := by
  ext b
  rw [MonoidHom.mem_ker]
  change ((b : K) ∈ A.val ∧ (b : K) ∈ B.val) ↔
    QuotientGroup.mk' _ (Subgroup.inclusion le_sup_right b) = 1
  have he := QuotientGroup.eq_one_iff
    (N := A.val.subgroupOf (A ⊔ B).val)
    (Subgroup.inclusion (show B.val ≤ (A ⊔ B).val from le_sup_right) b)
  exact ⟨fun h => he.mpr h.1, fun h => ⟨he.mp h, b.property⟩⟩

private theorem diamondHom_surjective (A B : NormalNode K) :
    Function.Surjective (diamondHom A B) := by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf (A ⊔ B).val) x
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.mp hx
  refine ⟨⟨b, hb⟩, ?_⟩
  change QuotientGroup.mk' _ (⟨b, _⟩ : (A ⊔ B).val) = QuotientGroup.mk' _ ⟨a * b, _⟩
  apply Eq.symm
  apply QuotientGroup.eq_iff_div_mem.mpr
  change a * b / b ∈ A.val
  simpa using ha

/-- The inclusion of B induces the inverse diamond isomorphism, preserving
ambient conjugation on the literal quotients. -/
noncomputable def diamondInverse (A B : NormalNode K) :
    SectionEquiv (A ⊓ B) B A (A ⊔ B) where
  equiv := QuotientGroup.liftEquiv _ (diamondHom_surjective A B) (diamondHom_ker A B)
  equivariant k x := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective ((A ⊓ B).val.subgroupOf B.val) x
    rfl

/-- The inverse diamond map is induced by the literal inclusion of B. -/
@[simp] theorem diamondInverse_mk (A B : NormalNode K) (b : B.val) :
    (diamondInverse A B).equiv (QuotientGroup.mk' _ b) =
      QuotientGroup.mk' _ (Subgroup.inclusion le_sup_right b : (A ⊔ B).val) := by
  exact QuotientGroup.liftEquiv_mk _ (diamondHom_surjective A B) (diamondHom_ker A B) b

/-- Equivariant second isomorphism theorem for ambient normal sections. -/
noncomputable def diamondEquiv (A B : NormalNode K) :
    SectionEquiv A (A ⊔ B) (A ⊓ B) B := (diamondInverse A B).symm

/-- A representative from B has the same representative in the lower
section. Every coset in the upper section has such a representative. -/
@[simp] theorem diamondEquiv_mk (A B : NormalNode K) (b : B.val) :
    (diamondEquiv A B).equiv
      (QuotientGroup.mk' _ (Subgroup.inclusion le_sup_right b : (A ⊔ B).val)) =
      QuotientGroup.mk' _ b :=
  (diamondInverse A B).equiv.symm_apply_apply (QuotientGroup.mk' _ b)

/-- The generated lattice interval relation gives actual multiplicative
isomorphisms intertwining ambient conjugation. -/
theorem sectionEquiv_of_iso {A B C D : NormalNode K}
    (h : JordanHolderLattice.Iso (A, B) (C, D)) : Nonempty (SectionEquiv A B C D) := by
  apply h.rel (fun x y => Nonempty (SectionEquiv x.1 x.2 y.1 y.2))
  · exact ⟨SectionEquiv.refl _ _⟩
  · exact fun ⟨e⟩ => ⟨e.symm⟩
  · exact fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩
  · exact fun _ => ⟨diamondEquiv _ _⟩

/-- Equivariant Jordan–Hölder: equal endpoints give a bijection of actual
chief factors together with equivariant isomorphism witnesses. -/
theorem ChiefSeries.exists_sectionEquiv_matching (s t : ChiefSeries K)
    (hhead : s.head = t.head) (hlast : s.last = t.last) :
    ∃ e : Fin s.length ≃ Fin t.length,
      ∀ i, Nonempty (SectionEquiv (s i.castSucc) (s i.succ)
        (t (e i).castSucc) (t (e i).succ)) := by
  obtain ⟨e, he⟩ := chiefSeries_jordanHolder s t hhead hlast
  exact ⟨e, fun i => sectionEquiv_of_iso (he i)⟩

/-- The noncentral two-chief count is independent of the chief series with
fixed endpoints, by the action-preserving factor matching. -/
theorem ChiefSeries.noncentralTwoCount_eq (s t : ChiefSeries K)
    (hhead : s.head = t.head) (hlast : s.last = t.last) :
    s.noncentralTwoCount = t.noncentralTwoCount := by
  obtain ⟨e, he⟩ := s.exists_sectionEquiv_matching t hhead hlast
  exact s.noncentralTwoCount_eq_of_matching t e he


/-- The literal image of an ambient normal subgroup under `K → K/Q`. -/
@[expose] def quotientImage (Q A : NormalNode K) : NormalNode (K ⧸ Q.val) :=
  ⟨A.val.map (QuotientGroup.mk' Q.val),
    inferInstanceAs (A.val.map (QuotientGroup.mk' Q.val)).Normal⟩

/-- The literal inverse image of a normal subgroup of `K/Q`. -/
@[expose] def quotientPreimage (Q : NormalNode K) (A : NormalNode (K ⧸ Q.val)) : NormalNode K :=
  ⟨A.val.comap (QuotientGroup.mk' Q.val),
    inferInstanceAs (A.val.comap (QuotientGroup.mk' Q.val)).Normal⟩

/-- Normal subgroups above Q are recovered from their quotient images. -/
@[simp] theorem quotientPreimage_image (Q A : NormalNode K) (hQA : Q ≤ A) :
    quotientPreimage Q (quotientImage Q A) = A := by
  apply Subtype.ext
  exact (QuotientGroup.comap_map_mk' Q.val A.val).trans (sup_eq_right.mpr hQA)

/-- Every normal subgroup of the quotient is the image of its preimage. -/
@[simp] theorem quotientImage_preimage (Q : NormalNode K) (A : NormalNode (K ⧸ Q.val)) :
    quotientImage Q (quotientPreimage Q A) = A := by
  apply Subtype.ext
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q.val) A.val

/-- Normal-subgroup correspondence, restricted to ambient normal subgroups. -/
@[expose] def quotientNormalOrderIso (Q : NormalNode K) :
    Set.Ici Q ≃o NormalNode (K ⧸ Q.val) where
  toFun A := quotientImage Q A.val
  invFun A := ⟨quotientPreimage Q A, QuotientGroup.le_comap_mk' Q.val A.val⟩
  left_inv A := Subtype.ext (quotientPreimage_image Q A.val A.property)
  right_inv A := quotientImage_preimage Q A
  map_rel_iff' := by
    intro A B
    change A.val.val.map (QuotientGroup.mk' Q.val) ≤
      B.val.val.map (QuotientGroup.mk' Q.val) ↔ A.val.val ≤ B.val.val
    constructor
    · intro h
      have hc := Subgroup.comap_mono (f := QuotientGroup.mk' Q.val) h
      simpa only [QuotientGroup.comap_map_mk', sup_eq_right.mpr (show Q.val ≤ A.val.val from A.property),
        sup_eq_right.mpr (show Q.val ≤ B.val.val from B.property)] using hc
    · exact Subgroup.map_mono

/-- The correspondence preserves and reflects actual chief intervals. -/
theorem quotientImage_covBy_iff (Q A B : NormalNode K) (hQA : Q ≤ A) (hQB : Q ≤ B) :
    quotientImage Q A ⋖ quotientImage Q B ↔ A ⋖ B := by
  have hc : (⟨A, hQA⟩ : Set.Ici Q) ⋖ ⟨B, hQB⟩ ↔ A ⋖ B := by
    constructor
    · rintro ⟨h, hm⟩
      refine ⟨h, fun C hAC hCB => ?_⟩
      exact hm (c := ⟨C, hQA.trans hAC.le⟩) hAC hCB
    · rintro ⟨h, hm⟩
      exact ⟨h, fun C hAC hCB => hm hAC hCB⟩
  exact (apply_covBy_apply_iff (quotientNormalOrderIso Q)).trans hc

private def quotientSectionHom (Q A B : NormalNode K) :
    B.val →* Section (quotientImage Q A) (quotientImage Q B) :=
  (QuotientGroup.mk' _).comp ((QuotientGroup.mk' Q.val).subgroupMap B.val)

private theorem quotientSectionHom_surjective (Q A B : NormalNode K) :
    Function.Surjective (quotientSectionHom Q A B) :=
  (QuotientGroup.mk'_surjective _).comp (MonoidHom.subgroupMap_surjective _ _)

private theorem quotientSectionHom_ker (Q A B : NormalNode K) (hQA : Q ≤ A) :
    A.val.subgroupOf B.val = (quotientSectionHom Q A B).ker := by
  ext b
  rw [MonoidHom.mem_ker]
  change (b : K) ∈ A.val ↔
    QuotientGroup.mk' ((quotientImage Q A).val.subgroupOf (quotientImage Q B).val)
      ((QuotientGroup.mk' Q.val).subgroupMap B.val b) = 1
  have he : (A.val.map (QuotientGroup.mk' Q.val)).comap (QuotientGroup.mk' Q.val) = A.val :=
    (QuotientGroup.comap_map_mk' Q.val A.val).trans (sup_eq_right.mpr hQA)
  exact (SetLike.ext_iff.mp he (b : K)).symm.trans (QuotientGroup.eq_one_iff
    (N := (quotientImage Q A).val.subgroupOf (quotientImage Q B).val)
    ((QuotientGroup.mk' Q.val).subgroupMap B.val b)).symm

/-- The quotient projection identifies relative sections whenever Q lies
in the lower endpoint. In particular this applies to every interval `Q ≤ A ≤ B`. -/
noncomputable def quotientSectionEquiv (Q A B : NormalNode K) (hQA : Q ≤ A) :
    Section A B ≃* Section (quotientImage Q A) (quotientImage Q B) :=
  QuotientGroup.liftEquiv _ (quotientSectionHom_surjective Q A B)
    (quotientSectionHom_ker Q A B hQA)

/-- The section isomorphism is induced by the literal quotient map on
representatives, restricted to B and its image. -/
@[simp] theorem quotientSectionEquiv_mk (Q A B : NormalNode K) (hQA : Q ≤ A) (b : B.val) :
    quotientSectionEquiv Q A B hQA (QuotientGroup.mk' _ b) =
      QuotientGroup.mk' ((quotientImage Q A).val.subgroupOf (quotientImage Q B).val)
      ((QuotientGroup.mk' Q.val).subgroupMap B.val b) := by
  exact QuotientGroup.liftEquiv_mk _ (quotientSectionHom_surjective Q A B)
    (quotientSectionHom_ker Q A B hQA) b

/-- Conjugation by k corresponds to conjugation by its image in `K/Q`. -/
theorem quotientSectionEquiv_equivariant (Q A B : NormalNode K) (hQA : Q ≤ A)
    (k : K) (x : Section A B) :
    quotientSectionEquiv Q A B hQA (sectionAction A B k x) =
      sectionAction (quotientImage Q A) (quotientImage Q B) (QuotientGroup.mk' Q.val k)
        (quotientSectionEquiv Q A B hQA x) := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
  rw [sectionAction_mk, quotientSectionEquiv_mk, quotientSectionEquiv_mk]
  change QuotientGroup.mk' ((quotientImage Q A).val.subgroupOf (quotientImage Q B).val)
    ((QuotientGroup.mk' Q.val).subgroupMap B.val (MulAut.conjNormal k b)) =
    QuotientGroup.mk' ((quotientImage Q A).val.subgroupOf (quotientImage Q B).val)
      (MulAut.conjNormal (QuotientGroup.mk' Q.val k)
      ((QuotientGroup.mk' Q.val).subgroupMap B.val b))
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  change QuotientGroup.mk' Q.val (k * (b : K) * k⁻¹) =
    QuotientGroup.mk' Q.val k * QuotientGroup.mk' Q.val b * (QuotientGroup.mk' Q.val k)⁻¹
  simp only [map_mul, map_inv]

/-- A terminal quotient without any two-chief factors excludes every
actual two-chief interval above Q. Central intervals are included. -/
theorem not_isPGroup_section_of_quotient (Q : NormalNode K)
    (h : HasNoTwoChiefFactors (K ⧸ Q.val)) {A B : NormalNode K}
    (hAB : A ⋖ B) (hQA : Q ≤ A) : ¬ IsPGroup 2 (Section A B) := by
  intro hp
  exact h (quotientImage Q A) (quotientImage Q B)
    ((quotientImage_covBy_iff Q A B hQA (hQA.trans hAB.le)).mpr hAB)
    (hp.of_equiv (quotientSectionEquiv Q A B hQA))

/-- Application to the terminal chief refinement: the genuine quotient
hypothesis forces its contribution to the noncentral two-chief count to vanish. -/
theorem ChiefSeries.noncentralTwoCount_eq_zero_of_quotient (s : ChiefSeries K)
    (Q : NormalNode K) (hQ : Q ≤ s.head)
    (h : HasNoTwoChiefFactors (K ⧸ Q.val)) : s.noncentralTwoCount = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  refine ⟨fun i => ?_⟩
  exact not_isPGroup_section_of_quotient Q h (s.step i.val)
    (hQ.trans (CompositionSeries.head_le i.val.castSucc)) i.property.1
end NoncentralChiefRefinement
