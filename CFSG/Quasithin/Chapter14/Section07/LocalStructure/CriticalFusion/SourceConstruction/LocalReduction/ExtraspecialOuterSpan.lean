module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanModule
public import Theory.Representation.BinaryConjugationSection.ElementaryQuotient
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.Frattini.PGroup
public import Theory.Representation.BinaryConjugationSection.FixedMoving

/-!
# The generating plane in the original outer span quotient

For S = ⟨Uᴸ⟩ and R = ⟨[U,Q]ᴸ⟩, the Frattini identity Φ(S) = V ≤ R
makes the actual S/R elementary abelian. Its conjugation action is induced
by LT, and [S,Q] = R kills the literal Q. The intersection U ∩ R = E
and |U:E| = 4 give the generating plane U/E.

Transfer the point cubic's norm through the original quotient coordinates.
The resulting full movement makes U/E irreducible for L₁. A Sylow-fixed
nonzero vector is cyclic for the plane and then for S/R. These supply the
original inputs to H.6.5 in the central branch of 14.7.24. They also hold
before choosing a centralizer branch. No Core recognition is assumed.

Source: Aschbacher–Smith 14.7.24(1), printed p.1051, refs/quasithin.pdf.
Genuine earlier structural and faithful-classification inputs remain explicit;
their final source discharge stays with qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original LT preserves S = ⟨Uᴸ⟩. -/
theorem original_outer_span_normalized
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    L ⊔ (T : Subgroup G) ≤ normalizer (conjugateSpanBy F.U L : Set G) := by
  exact sup_le (le_normalizer_conjugateSpanBy _ _) (normalizes_conjugateSpanBy _ _ _
    ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
    (h.sylow_normalizes structural))

/-- The literal U-image in S/R has order four, since its full kernel is E. -/
theorem extraspecial_outer_plane_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (conjugateSpanBy ⁅F.U,Q T L⁆ L).relIndex F.U = 4 := by
  obtain ⟨c,hs,_,_,hEc,_,_,_,_,_,_,_,_,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hU := (extraspecial_source_reduction h hab structural previous he).2.1
  have hmul := relIndex_mul_card_of_le (hinter.symm.le.trans inf_le_left)
  rw [hEc,hU] at hmul
  rw [←inf_relIndex_left,hinter]
  omega

/-- Construct the literal S/R action, with Q in its kernel and U-image a plane. -/
theorem extraspecial_outer_span_binary_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let S := conjugateSpanBy F.U L
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) S R ρ),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      Module.finrank (ZMod 2) (s.imageSpace F.U) = 2 := by
  dsimp only
  let S := conjugateSpanBy F.U L
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let J := L ⊔ (T : Subgroup G)
  obtain ⟨c,hs,_,hE,hcard,hEV,hSQ,hRQ,hRS,hPhi,_,_,_,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hSJ : S ≤ J := (original_span_le_core h hab structural).2.trans (pCoreIn_le 2 _)
  have hRS' : R ≤ S := hRS.trans (map_subtype_le _)
  have hVR : V ≤ R := hRQ.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp
      ((pCoreIn_le 2 _).trans (original_commutator_span_normalized h structural).1))
  let : (R.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (hSJ.trans (original_commutator_span_normalized h structural).1)
  let : Fact (IsPGroup 2 S) := ⟨(isPGroup_pCoreIn 2 _).to_le
    (original_span_le_core h hab structural).2⟩
  let : IsElementaryAbelian 2 (S ⧸ frattini S) := isElementaryAbelian_quotient_frattini
  have hphi : frattini S ≤ (R.subgroupOf S).comap (MonoidHom.id S) := by
    intro x hx
    exact hVR (hPhi ▸ mem_map_of_mem S.subtype hx)
  let q := QuotientGroup.map (frattini S) (R.subgroupOf S) (MonoidHom.id S) hphi
  let : IsElementaryAbelian 2 (S ⧸ R.subgroupOf S) :=
    IsElementaryAbelian.of_surjective q
      (QuotientGroup.map_surjective_of_surjective (frattini S) (R.subgroupOf S)
        (MonoidHom.id S) (QuotientGroup.mk'_surjective _) hphi)
  obtain ⟨ρ,⟨s⟩⟩ := BinaryConjugationSection.exists_elementary_quotient_coordinates J S R
    hSJ (original_outer_span_normalized h structural) hRS'
    (original_commutator_span_normalized h structural).1
  have hi : R.relIndex F.U = 4 :=
    extraspecial_outer_plane_index h hab structural previous faithful he
  refine ⟨Additive (S ⧸ R.subgroupOf S),inferInstance,inferInstance,ρ,s,?_,
    s.imageSpace_finrank_of_index F.U (le_conjugateSpanBy _ _) 2 hi⟩
  intro a ha
  apply MonoidHom.mem_ker.mpr
  ext w
  obtain ⟨r,hr⟩ := s.onto (Multiplicative.ofAdd w)
  apply (show ρ a w = w ↔ ρ a (s.coordinates r).toAdd = (s.coordinates r).toAdd by rw [hr]; rfl).mpr
  apply (s.fixed_coordinate_iff_commutator_mem a r).mpr
  exact hSQ.le (commutator_mem_commutator r.property ha)

omit [Finite G] in
private theorem outerSpan_norm_transfer
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    {τ : Representation (ZMod 2) F.H X}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ)
    (s₀ : BinaryConjugationSection F.H F.U (F.Vi 1) τ)
    (hVR : V ≤ conjugateSpanBy ⁅F.U,Q T L⁆ L)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (ha : (a : G) ∈ F.H)
    (hn : ∀ x, x + τ ⟨a,ha⟩ x + τ ⟨a,ha⟩ (τ ⟨a,ha⟩ x) = 0)
    (w : W) (hw : w ∈ s.imageSpace F.U) :
    w + ρ a w + ρ a (ρ a w) = 0 := by
  let R := conjugateSpanBy F.U L
  obtain ⟨r,hr,rfl⟩ := (s.mem_imageSpace_iff _ w).mp hw
  let u : F.U := ⟨r,hr⟩
  let cR (x : R) : R := ⟨(a:G)*(x:G)*(a:G)⁻¹,
    (mem_normalizer_iff.mp (s.normalized a.property) x).mp x.property⟩
  let cU (x : F.U) : F.U := ⟨(a:G)*(x:G)*(a:G)⁻¹,
    (mem_normalizer_iff.mp (s₀.normalized ha) x).mp x.property⟩
  have hnU : ((u * cU u * cU (cU u) : F.U) : G) ∈ F.Vi 1 := by
    apply (s₀.coordinates_eq_one_iff _).mp
    apply Multiplicative.toAdd.injective
    change (s₀.coordinates _).toAdd = 0
    simp only [map_mul, toAdd_mul]
    rw [show (s₀.coordinates (cU u)).toAdd = τ ⟨a,ha⟩ (s₀.coordinates u).toAdd
      from s₀.equivariant ⟨a,ha⟩ u,
      show (s₀.coordinates (cU (cU u))).toAdd = τ ⟨a,ha⟩ (τ ⟨a,ha⟩ (s₀.coordinates u).toAdd) from
        (s₀.equivariant ⟨a,ha⟩ (cU u)).trans
          (congrArg (τ ⟨a,ha⟩) (s₀.equivariant ⟨a,ha⟩ u))]
    exact hn _
  have hnR : s.coordinates (r * cR r * cR (cR r)) = 1 :=
    (s.coordinates_eq_one_iff _).mpr (hVR (F.le_seed 1 hnU))
  have hh := congrArg Multiplicative.toAdd hnR
  simp only [map_mul, toAdd_mul] at hh
  rw [show (s.coordinates (cR r)).toAdd = ρ a (s.coordinates r).toAdd from s.equivariant a r,
    show (s.coordinates (cR (cR r))).toAdd = ρ a (ρ a (s.coordinates r).toAdd) from
      (s.equivariant a (cR r)).trans (congrArg (ρ a) (s.equivariant a r))] at hh
  exact hh

/-- The point cubic has zero norm on the original U/E plane in S/R. -/
theorem extraspecial_outer_plane_cubic_norm
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ) :
    ∃ a : (L ⊔ (T : Subgroup G) : Subgroup G), (a : G) ∈ F.Li L 1 ∧
      ∀ w ∈ s.imageSpace F.U, w + ρ a w + ρ a (ρ a w) = 0 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨e⟩ := he
  have he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3) := ⟨e⟩
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hnormal := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨τ,⟨s₀⟩⟩ := exists_section F
  obtain ⟨σ,hσ⟩ := exists_star_representation h s₀
  obtain ⟨z,hz,hzp,hfix⟩ := exists_fixedFree_cubic_of_point_normal h structural hnormal s₀ σ hσ
  have hzm : z ∈ star F (F.Li L 1) := hzp ▸ mem_zpowers z
  obtain ⟨a,ha,haz⟩ := hzm
  let aJ : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨a,(le_sup_left : L ≤ L ⊔ (T : Subgroup G)) (F.Li_le L 1 ha).1⟩
  have heq : τ a = σ z := by
    rw [←haz,←hσ]
    rfl
  have hz3 (x) : σ z (σ z (σ z x)) = x := by
    calc _ = σ (z ^ 3) x := by simp [pow_succ,map_mul,Module.End.mul_apply]
         _ = x := by rw [show z ^ 3 = 1 from orderOf_dvd_iff_pow_eq_one.mp (by rw [hz]),map_one]; rfl
  refine ⟨aJ,ha,?_⟩
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))
  have hVE : V ≤ ⁅F.U,Q T L⁆ := by
    obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hnormal
    exact (extraspecial_critical_commutator_eq_seed h hab structural previous faithful he c hs).symm.le.trans
      (commutator_mono le_rfl (critical_le_Q h structural c))
  apply outerSpan_norm_transfer s s₀ (hVE.trans (le_conjugateSpanBy _ _)) aJ a.property
  intro x
  change x + τ a x + τ a (τ a x) = 0
  rw [heq]
  apply hfix
  simp only [map_add,hz3]
  abel
private theorem outerSpan_binary_neg {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (w : W) : -w = w := by
  simpa only [CharTwo.neg_eq,one_smul] using (neg_smul (1 : ZMod 2) w).symm

/-- The original point residual acts irreducibly on U/E. The norm relation
supplies full movement, so a binary line quotient would be impossible. -/
theorem extraspecial_outer_plane_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ) :
    ∃ D : Subrepresentation (ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))),
      D.toSubmodule = s.imageSpace F.U ∧ IsIrreducible D.toRepresentation := by
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  let D : Subrepresentation (ρ.comp j) := {
    toSubmodule := s.imageSpace F.U
    apply_mem_toSubmodule a w hw := s.imageSpace_apply_mem _ (j a)
      ((le_normalizer_conjugateSpanBy V F.H) (F.Li_le L 1 a.property).2) w hw }
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hi := extraspecial_outer_plane_index h hab structural previous faithful he
  have hd : Module.finrank (ZMod 2) D.toSubmodule = 2 :=
    s.imageSpace_finrank_of_index _ (le_conjugateSpanBy _ _) 2 hi
  obtain ⟨a,ha,hn⟩ := extraspecial_outer_plane_cubic_norm h hab structural previous faithful he s
  let b : F.Li L 1 := ⟨a,ha⟩
  have hnorm (w : D.toSubmodule) :
      w + D.toRepresentation b w + D.toRepresentation b (D.toRepresentation b w) = 0 := by
    apply Subtype.ext
    exact hn w w.property
  have hm : Representation.BinaryOffender.subspaceCommutator D.toRepresentation ⊤ ⊤ = ⊤ := by
    apply top_unique
    intro w _
    have hmove : D.toRepresentation b (D.toRepresentation b w) - D.toRepresentation b w = w := by
      calc _ = -(D.toRepresentation b w + D.toRepresentation b (D.toRepresentation b w)) := by
             simp only [sub_eq_add_neg,outerSpan_binary_neg]
             exact add_comm _ _
           _ = w := (eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hnorm w)).symm
    exact Submodule.subset_span ⟨b,mem_top b,D.toRepresentation b w,Submodule.mem_top,hmove.symm⟩
  exact ⟨D,rfl,Representation.BinaryOffender.irreducible_of_rank_two_full_movement _ hd hm⟩

omit [Finite G] in
/-- The conjugates of the literal U/E plane generate the entire S/R section. -/
theorem extraspecial_outer_plane_generates
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ)
    (A : Submodule (ZMod 2) W) (hA : s.imageSpace F.U ≤ A)
    (hstable : ∀ l : L, ∀ w ∈ A, ρ (inclusion le_sup_left l) w ∈ A) : A = ⊤ := by
  let R := conjugateSpanBy F.U L
  let B : Subgroup R := A.toAddSubgroup.toSubgroup.comap s.coordinates
  have hRB : R ≤ B.map R.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨l,hl,e,he,rfl⟩
    let eR : R := ⟨e,le_conjugateSpanBy _ _ he⟩
    let lJ : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨l,(le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hl⟩
    refine ⟨⟨l*e*l⁻¹,(mem_normalizer_iff.mp (s.normalized lJ.property) e).mp eR.property⟩,?_,rfl⟩
    change (s.coordinates _).toAdd ∈ A
    rw [s.equivariant lJ eR]
    exact hstable ⟨l,hl⟩ _ (hA ((s.mem_imageSpace_iff _ _).mpr ⟨eR,he,rfl⟩))
  apply top_unique
  intro w _
  obtain ⟨r,hr⟩ := s.onto (Multiplicative.ofAdd w)
  obtain ⟨b,hb,hbr⟩ := hRB r.property
  have hbr' : b = r := Subtype.ext hbr
  subst b
  change (s.coordinates r).toAdd ∈ A at hb
  simpa only [hr,toAdd_ofAdd] using hb

open BinaryLinearThree.ParabolicCyclic in
/-- The original section has a Sylow-fixed cyclic seed whose point-parabolic
orbit spans exactly U/E. This supplies the geometric hypotheses of H.6.5
before choosing a matrix marking. -/
theorem extraspecial_outer_cyclic_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) ρ) :
    let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
    ∃ w ∈ s.imageSpace F.U, w ≠ 0 ∧
      (∀ t : L, (t : G) ∈ (T : Subgroup G) → τ t w = w) ∧
      orbitSpan τ ⊤ w = ⊤ ∧
      orbitSpan τ (F.H.subgroupOf L) w = s.imageSpace F.U ∧
      Module.finrank (ZMod 2) (orbitSpan τ (F.H.subgroupOf L) w) = 2 := by
  dsimp only
  let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
  let D := s.imageSpace F.U
  let S := (T : Subgroup G).subgroupOf L
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have stable (l : L) (hl : (l : G) ∈ F.H) (w : W) (hw : w ∈ D) : τ l w ∈ D :=
    s.imageSpace_apply_mem _ (inclusion le_sup_left l)
      ((le_normalizer_conjugateSpanBy V F.H) hl) w hw
  let : MulAction S D := {
    smul t w := ⟨τ t w,stable t (F.invariant 1 t.property) w w.property⟩
    one_smul w := by apply Subtype.ext; exact congrArg (fun f => f w.val) τ.map_one
    mul_smul t r w := by apply Subtype.ext; exact congrArg (fun f => f w.val) (τ.map_mul t r) }
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype
  have hi := extraspecial_outer_plane_index h hab structural previous faithful he
  have hcard : Nat.card D = 4 := (s.imageSpace_card_eq_relIndex _ (le_conjugateSpanBy _ _)).trans hi
  have hd : Module.finrank (ZMod 2) D = 2 :=
    s.imageSpace_finrank_of_index _ (le_conjugateSpanBy _ _) 2 hi
  obtain ⟨w,hw,hw0⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := D) (by rw [hcard]; decide)
    (show (0 : D) ∈ MulAction.fixedPoints S D from fun a => Subtype.ext (map_zero (τ a)))
  have hn : (w : W) ≠ 0 := fun hh => hw0 (Subtype.ext hh.symm)
  have hfix : ∀ t : L, (t : G) ∈ (T : Subgroup G) → τ t w = w :=
    fun t ht => congrArg Subtype.val (hw ⟨t,ht⟩)
  let A := orbitSpan τ (F.H.subgroupOf L) w
  have hAD : A ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l,hl,rfl⟩
    exact stable l hl w w.property
  obtain ⟨I,hI,hirr⟩ := extraspecial_outer_plane_irreducible h hab structural previous faithful he s
  let : IsIrreducible I.toRepresentation := hirr
  have hstable (a : F.Li L 1) (v : W) (hv : v ∈ A) :
      ρ (inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) a) v ∈ A :=
    orbitSpan_stable τ (F.H.subgroupOf L) w
      ⟨a,(F.Li_le L 1 a.property).1⟩ (F.Li_le L 1 a.property).2 v hv
  let B : Subrepresentation I.toRepresentation := {
    toSubmodule := A.comap I.toSubmodule.subtype
    apply_mem_toSubmodule a v hv := hstable a v hv }
  have hB : B = ⊤ := (eq_bot_or_eq_top B).resolve_left (by
    intro hb
    have hm : (⟨w,hI ▸ w.property⟩ : I.toSubmodule) ∈ B := mem_orbitSpan τ _ w
    rw [hb] at hm
    exact hn (congrArg Subtype.val hm))
  have hDA : D ≤ A := by
    intro v hv
    have hm : (⟨v,hI ▸ hv⟩ : I.toSubmodule) ∈ B := hB ▸ Submodule.mem_top
    exact hm
  have hplane : A = D := le_antisymm hAD hDA
  have hfull : orbitSpan τ ⊤ w = ⊤ := by
    apply extraspecial_outer_plane_generates s
    · apply hDA.trans
      apply Submodule.span_mono
      rintro v ⟨a,_,ha⟩
      exact ⟨a,mem_top a,ha⟩
    · intro l v hv
      exact orbitSpan_stable τ ⊤ w l (mem_top l) v hv
  exact ⟨w,w.property,hn,hfix,hfull,hplane,by change Module.finrank (ZMod 2) A = 2; rw [hplane]; exact hd⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
