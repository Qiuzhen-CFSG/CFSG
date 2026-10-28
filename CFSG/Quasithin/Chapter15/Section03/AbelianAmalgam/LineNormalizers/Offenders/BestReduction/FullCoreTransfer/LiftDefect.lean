module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer

/-!
# Fixed-vector lifting through the actual paired section

The cokernel of the map from U-fixed vectors to the two quotient fixed spaces
measures exactly the obstruction to lifting fixed vectors through E. Maximum
elementary order bounds the quotient weights with this cokernel correction.
Failure of bestness forces a strict increase in that correction. These are
necessary comparisons, not a proof of first-summand bestness or generation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inequalities
in the proof of 15.3.67, printed pp.1153–1154, and Definition B.1.2, p.68.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
section General
variable {G H W : Type*} [Group G] [Group H] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {U E C Q : Subgroup G} [U.Normal] [IsElementaryAbelian 2 U] [Q.Normal]
  {f : G →* H} {hf : Function.Surjective f}
  {hker : f.ker = centralizer (U : Set G)}
  {σ : Representation (ZMod 2) (G ⧸ Q) W}
  (d : PairedSection U E C Q f hf hker σ)

/-- The literal paired projection restricted to fixed vectors of an actor R in C. -/
noncomputable def fixedProjection (R : Subgroup G) (hRC : R ≤ C) :
    fixedSpace (Representation.NormalElementaryQuotient.representation U f hf hker)
      (R.map f) →ₗ[ZMod 2]
        (fixedSpace σ (R.map (QuotientGroup.mk' Q))) ×
        (fixedSpace σ (R.map (QuotientGroup.mk' Q))) where
  toFun v :=
    (⟨(d.projection v).1, by
      rintro ⟨_, r, hr, rfl⟩
      have he := d.equivariant r (hRC hr) v
      rw [show Representation.NormalElementaryQuotient.representation U f hf hker
        (f r) v = v from v.property ⟨f r, mem_map_of_mem f hr⟩] at he
      exact (congrArg Prod.fst he).symm⟩,
     ⟨(d.projection v).2, by
      rintro ⟨_, r, hr, rfl⟩
      have he := d.equivariant r (hRC hr) v
      rw [show Representation.NormalElementaryQuotient.representation U f hf hker
        (f r) v = v from v.property ⟨f r, mem_map_of_mem f hr⟩] at he
      exact (congrArg Prod.snd he).symm⟩)
  map_add' v w := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (d.projection.map_add v w)
    · exact congrArg Prod.snd (d.projection.map_add v w)
  map_smul' a v := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (d.projection.map_smul a v)
    · exact congrArg Prod.snd (d.projection.map_smul a v)

/-- Dimension of the actual cokernel on fixed vectors; no fixed lift is chosen. -/
noncomputable def liftDefect (R : Subgroup G) (hRC : R ≤ C) : ℕ :=
  Module.finrank (ZMod 2)
    (((fixedSpace σ (R.map (QuotientGroup.mk' Q))) ×
      (fixedSpace σ (R.map (QuotientGroup.mk' Q)))) ⧸
        (fixedProjection d R hRC).range)

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
private theorem fixedProjection_kernel_equiv (hEC : C ≤ centralizer (E : Set G))
    (R : Subgroup G) (hRC : R ≤ C) :
    Nonempty ((fixedProjection d R hRC).ker ≃ₗ[ZMod 2] d.projection.ker) := by
  have hfix : d.projection.ker ≤ fixedSpace
      (Representation.NormalElementaryQuotient.representation U f hf hker) (R.map f) := by
    intro v hv
    rw [d.kernel_eq] at hv
    rintro ⟨_, r, hr, rfl⟩
    change Representation.NormalElementaryQuotient.representation U f hf hker (f r) v = v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [Representation.NormalElementaryQuotient.representation_apply,
      ← hEC (hRC hr) v.toMul hv, mul_inv_cancel_right]
  refine ⟨{
    toFun := fun v => ⟨v.val.val, ?_⟩
    invFun := fun v => ⟨⟨v, hfix v.property⟩, ?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }⟩
  · have hh := congrArg (fun x => ((x.1 : W), (x.2 : W))) v.property
    exact hh
  · apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst v.property
    · exact congrArg Prod.snd v.property

private theorem internal_fixed_finrank (R : Subgroup G) :
    Module.finrank (ZMod 2)
      (fixedSpace (Representation.NormalElementaryQuotient.representation U f hf hker)
        (R.map f)) = rank (U ⊓ centralizer (R : Set G)) := by
  rw [rank, ← Nat.card_congr
    (Representation.NormalElementaryQuotient.fixedSpaceEquiv U f hf hker R)]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow Nat.one_lt_two]

omit [FiniteDimensional (ZMod 2) W] in
/-- The kernel term is the rank of the actual line subgroup E. -/
theorem projection_kernel_finrank : Module.finrank (ZMod 2) d.projection.ker = rank E := by
  let e : d.projection.ker ≃ E := {
    toFun := fun v => ⟨v.val.toMul, d.kernel_eq.le v.property⟩
    invFun := fun v => ⟨Additive.ofMul ⟨v, d.line_le v.property⟩, by
      rw [d.kernel_eq]
      exact v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [rank, ← Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, Nat.log_pow Nat.one_lt_two]

/-- Rank-nullity for the actual fixed-vector projection, retaining its cokernel. -/
theorem fixed_rank_add_liftDefect (hEC : C ≤ centralizer (E : Set G))
    (R : Subgroup G) (hRC : R ≤ C) :
    rank (U ⊓ centralizer (R : Set G)) + liftDefect d R hRC =
      rank E +
        2 * Module.finrank (ZMod 2) (fixedSpace σ (R.map (QuotientGroup.mk' Q))) := by
  obtain ⟨e⟩ := fixedProjection_kernel_equiv d hEC R hRC
  have hp := (fixedProjection d R hRC).finrank_range_add_finrank_ker
  have hq := (fixedProjection d R hRC).range.finrank_quotient_add_finrank
  rw [e.finrank_eq, projection_kernel_finrank d, internal_fixed_finrank R] at hp
  rw [Module.finrank_prod] at hq
  change liftDefect d R hRC + _ = _ at hq
  omega

/-- In the literal order-four case the kernel contributes exactly two. -/
theorem fixed_rank_add_liftDefect_of_card_four
    (hEC : C ≤ centralizer (E : Set G)) (hE : Nat.card E = 4)
    (R : Subgroup G) (hRC : R ≤ C) :
    rank (U ⊓ centralizer (R : Set G)) + liftDefect d R hRC =
      2 + 2 * Module.finrank (ZMod 2) (fixedSpace σ (R.map (QuotientGroup.mk' Q))) := by
  have he : rank E = 2 := by rw [rank, hE]; decide
  simpa only [he] using fixed_rank_add_liftDefect d hEC R hRC

/-- The precise comparison available from maximum elementary order for EVERY
subgroup B of the quotient image. The two cokernels cannot be discarded. -/
theorem maximum_quotient_weight_comparison
    (hEC : C ≤ centralizer (E : Set G)) (hUQ : U ≤ Q)
    (S A : Subgroup G) (hUS : U ≤ S)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S) (hAC : A ≤ C)
    (B : Subgroup (G ⧸ Q)) (hBA : B ≤ A.map (QuotientGroup.mk' Q)) :
    2 * weight σ B + rank (A.map (QuotientGroup.mk' Q)) + liftDefect d A hAC ≤
      2 * weight σ (A.map (QuotientGroup.mk' Q)) + rank B +
        liftDefect d (A ⊓ B.comap (QuotientGroup.mk' Q)) (inf_le_left.trans hAC) := by
  let q := QuotientGroup.mk' Q
  let X := A ⊓ B.comap q
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_le (show X ≤ A from inf_le_left)
  have hXq : X.map q = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := hBA hb
      exact ⟨a, ⟨ha, hb⟩, rfl⟩
  have hkernel : X ⊓ q.ker = A ⊓ q.ker := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · intro a ha
      refine ⟨⟨ha.1, ?_⟩, ha.2⟩
      change q a ∈ B
      rw [ha.2]
      exact B.one_mem
  have hAX : A ⊓ U ≤ X := by
    intro a ha
    refine ⟨ha.1, ?_⟩
    change q a ∈ B
    have haQ : q a = 1 := (QuotientGroup.eq_one_iff a).mpr (hUQ ha.2)
    rw [haQ]
    exact B.one_mem
  have hm := maximum_fixed_weight_comparison S U A X hUS hA inf_le_left hAX
  have ha := rank_kernel_add_image A q
  have hx := rank_kernel_add_image X q
  rw [hkernel, hXq] at hx
  have hda := fixed_rank_add_liftDefect d hEC A hAC
  have hdx := fixed_rank_add_liftDefect d hEC X (inf_le_left.trans hAC)
  change rank (U ⊓ centralizer (X : Set G)) + _ = _ +
    2 * Module.finrank (ZMod 2) (fixedSpace σ (X.map q)) at hdx
  rw [hXq] at hdx
  change 2 * weight σ B + rank (A.map q) + liftDefect d A hAC ≤
    2 * weight σ (A.map q) + rank B + liftDefect d X (inf_le_left.trans hAC)
  dsimp only [q] at *
  unfold weight
  omega

/-- A failed best-offender comparison forces a quantified jump in the actual
fixed-lift cokernel. This is an obstruction, not an assumed bound on that jump. -/
theorem liftDefect_jump_of_weight_lt
    (hEC : C ≤ centralizer (E : Set G)) (hUQ : U ≤ Q)
    (S A : Subgroup G) (hUS : U ≤ S)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S) (hAC : A ≤ C)
    (B : Subgroup (G ⧸ Q)) (hBA : B ≤ A.map (QuotientGroup.mk' Q))
    (hweight : weight σ (A.map (QuotientGroup.mk' Q)) < weight σ B) :
    liftDefect d A hAC + rank (A.map (QuotientGroup.mk' Q)) + 2 ≤
      liftDefect d (A ⊓ B.comap (QuotientGroup.mk' Q)) (inf_le_left.trans hAC) + rank B := by
  have h := maximum_quotient_weight_comparison d hEC hUQ S A hUS hA hAC B hBA
  omega

/-- Failure of bestness has an actual witnessing subgroup and an actual cokernel jump. -/
theorem exists_liftDefect_jump_of_not_best
    (hEC : C ≤ centralizer (E : Set G)) (hUQ : U ≤ Q)
    (S A : Subgroup G) (hUS : U ≤ S)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S) (hAC : A ≤ C)
    (hne : A.map (QuotientGroup.mk' Q) ≠ ⊥)
    (hnot : ¬ IsBestOffender σ (A.map (QuotientGroup.mk' Q))) :
    ∃ B ≤ A.map (QuotientGroup.mk' Q),
      weight σ (A.map (QuotientGroup.mk' Q)) < weight σ B ∧
      liftDefect d A hAC + rank (A.map (QuotientGroup.mk' Q)) + 2 ≤
        liftDefect d (A ⊓ B.comap (QuotientGroup.mk' Q)) (inf_le_left.trans hAC) +
          rank B := by
  let : IsElementaryAbelian 2 A := hA.2.1
  have hw : ¬ ∀ B ≤ A.map (QuotientGroup.mk' Q),
      weight σ B ≤ weight σ (A.map (QuotientGroup.mk' Q)) := by
    intro h
    exact hnot ⟨⟨hne, IsElementaryAbelian.map _⟩, h⟩
  push Not at hw
  obtain ⟨B, hBA, hweight⟩ := hw
  exact ⟨B, hBA, hweight,
    liftDefect_jump_of_weight_lt d hEC hUQ S A hUS hA hAC B hBA hweight⟩

end General

section Temporary
open Replacement.Transvections
variable {G K W : Type*} [Group G] [Finite G] [Group K]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (Y T V E : Subgroup G) [IsMulCommutative V]
  [(Replacement.Transvections.localSpan T V E).Normal]
  [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
  (f : temporaryLineNormalizer T V E →* K) (hf : Function.Surjective f)
  (hker : f.ker = centralizer (Replacement.Transvections.localSpan T V E :
    Set (temporaryLineNormalizer T V E)))
  (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)

/-- Specialization to the original U, actual centralizer and FULL relative core.
Normal elementary U lies in O₂(H); no extra core-containment premise is imposed. -/
theorem temporary_quotient_weight_comparison
    (d : TemporaryData Y T V E)
    (p : PairedSection (Replacement.Transvections.localSpan T V E) (localLine T V E)
      (localCentralizer T V E) (localCore T V E) f hf hker σ)
    (A : Subgroup (temporaryLineNormalizer T V E))
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups
      ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)))
    (hAC : A ≤ localCentralizer T V E)
    (B : Subgroup ((temporaryLineNormalizer T V E) ⧸ localCore T V E))
    (hBA : B ≤ A.map (QuotientGroup.mk' (localCore T V E))) :
    2 * weight σ B + rank (A.map (QuotientGroup.mk' (localCore T V E))) +
        liftDefect p A hAC ≤
      2 * weight σ (A.map (QuotientGroup.mk' (localCore T V E))) + rank B +
        liftDefect p (A ⊓ B.comap (QuotientGroup.mk' (localCore T V E)))
          (inf_le_left.trans hAC) := by
  have hEC : localCentralizer T V E ≤
      centralizer (localLine T V E : Set (temporaryLineNormalizer T V E)) :=
    (localCentralizer_eq T V E (line_le_temporary T V E d.line_le d.span_le_sylow)).le
  have hUQ : Replacement.Transvections.localSpan T V E ≤ localCore T V E := by
    rw [localCore_eq_pCore]
    exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 _⟩
  exact maximum_quotient_weight_comparison p hEC hUQ _ A
    (comap_mono d.span_le_sylow) hA hAC B hBA

end Temporary

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
