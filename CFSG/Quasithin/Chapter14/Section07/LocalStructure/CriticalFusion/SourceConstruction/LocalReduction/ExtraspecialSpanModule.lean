module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanStructure
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.BinaryFullPlane
public import Theory.Representation.PSL3Two.ParabolicCyclic.Basic

/-!
# The original elementary commutator-span module

Let E = [U,Q] and R = ⟨Eᴸ⟩ in the Heisenberg residual branch. The proved
span identities make R elementary and give [R,Q] = V. Construct its literal
binary conjugation section R/V for LT, retaining the trivial Q-action.
The index |E:V| = 4 gives a plane. Transfer the point cubic's zero norm
from U/V₁ to this plane through the actual coordinate kernels; full movement
then makes the plane irreducible for L₁. A two-group fixed-point argument
constructs a nonzero (T ∩ L)-fixed vector in it. Irreducibility and the
conjugate-span definition make that vector cyclic for R/V, with point-parabolic
orbit exactly E/V. These are the original inputs to H.6.5.

Source: Aschbacher–Smith 14.7.19 and 14.7.22(1), printed pp.1048–1050,
refs/quasithin.pdf. The genuine Structural1222, Theorem12213 and earlier
faithful-classification inputs retain their producers and final discharge
with qt-d-14775-source. No later Data or recognition conclusion is assumed.
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

/-- The elementary commutator span in the original Heisenberg branch. -/
theorem extraspecial_commutator_span_elementary
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    IsElementaryAbelian 2 (conjugateSpanBy ⁅F.U,Q T L⁆ L) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))
  let : IsElementaryAbelian 2 (⁅F.U,Q T L⁆ : Subgroup G) := IsElementaryAbelian.of_le hEU
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,hR,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  let : IsMulCommutative (conjugateSpanBy ⁅F.U,Q T L⁆ L) := hR
  exact conjugateSpanBy_elementary_of_commutative _ _

omit [Finite G] in
private theorem spanModule_normalizes_span (A B N : Subgroup G)
    (hNA : N ≤ normalizer (A : Set G)) (hNB : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer (conjugateSpanBy A B : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq,map_conjugateSpanBy,
    mem_normalizer_iff_map_conj_eq.mp (hNA hn),mem_normalizer_iff_map_conj_eq.mp (hNB hn)]

omit [Finite G] in
private theorem spanModule_normalizes_commutator (A B N : Subgroup G)
    (hNA : N ≤ normalizer (A : Set G)) (hNB : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer ((⁅A,B⁆ : Subgroup G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hNA hn),mem_normalizer_iff_map_conj_eq.mp (hNB hn)]

/-- Both LT and its point parabolic preserve the original commutator construction. -/
theorem original_commutator_span_normalized
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (L ⊔ (T : Subgroup G)) ≤ normalizer (conjugateSpanBy ⁅F.U,Q T L⁆ L : Set G) ∧
      (L ⊓ F.H) ≤ normalizer ((⁅F.U,Q T L⁆ : Subgroup G) : Set G) := by
  have hQN : L ⊔ (T : Subgroup G) ≤ normalizer (Q T L : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hTN : (T : Subgroup G) ≤ normalizer ((⁅F.U,Q T L⁆ : Subgroup G) : Set G) :=
    spanModule_normalizes_commutator _ _ _ ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
      (le_sup_right.trans hQN)
  exact ⟨sup_le (le_normalizer_conjugateSpanBy _ _) (spanModule_normalizes_span _ _ _ hTN
    (h.sylow_normalizes structural)),spanModule_normalizes_commutator _ _ _
      (inf_le_right.trans (le_normalizer_conjugateSpanBy V F.H))
      ((inf_le_left.trans le_sup_left).trans hQN)⟩

/-- The actual R/V section, with its plane E/V and trivial Q-action. -/
theorem extraspecial_span_binary_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) R V ρ),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      Module.finrank (ZMod 2) (s.imageSpace ⁅F.U,Q T L⁆) = 2 ∧
      (∀ l : (L ⊔ (T : Subgroup G) : Subgroup G), (l : G) ∈ L ⊓ F.H →
        ∀ w ∈ s.imageSpace ⁅F.U,Q T L⁆, ρ l w ∈ s.imageSpace ⁅F.U,Q T L⁆) := by
  dsimp only
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let J := L ⊔ (T : Subgroup G)
  let : IsElementaryAbelian 2 R :=
    extraspecial_commutator_span_elementary h hab structural previous faithful he
  obtain ⟨c,hs,_,_,_,hEV,_,hRQ,_,_,_,_,hRC,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hEQ : ⁅F.U,Q T L⁆ ≤ conjugateSpanBy F.U L :=
    (le_normalizer_iff_commutator_le_left.mp
      ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))).trans
      (le_conjugateSpanBy _ _)
  have hRQle : R ≤ Q T L :=
    (conjugateSpanBy_mono (le_normalizer_iff_commutator_le_left.mp
      ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))) le_rfl).trans
      (original_span_le_core h hab structural).2
  have hVR : V ≤ R := hRQ.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp
      ((pCoreIn_le 2 _).trans (original_commutator_span_normalized h structural).1))
  obtain ⟨ρ,⟨s⟩⟩ := BinaryConjugationSection.exists_conjugation_coordinates J R V
    (hRQle.trans (pCoreIn_le 2 _)) (original_commutator_span_normalized h structural).1 hVR
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural))
  refine ⟨Additive (R ⧸ V.subgroupOf R),inferInstance,inferInstance,ρ,s,?_,?_,?_⟩
  · intro a ha
    apply MonoidHom.mem_ker.mpr
    ext w
    obtain ⟨r,hr⟩ := s.onto (Multiplicative.ofAdd w)
    have hh := s.equivariant a r
    have heq : s.coordinates
        ⟨(a : G)*(r : G)*(a : G)⁻¹,(mem_normalizer_iff.mp (s.normalized a.property) r).mp r.property⟩ =
        s.coordinates r := by
      apply div_eq_one.mp
      rw [←map_div]
      apply (s.coordinates_eq_one_iff _).mpr
      have hc : ⁅(a : G),(r : G)⁆ ∈ ⁅Q T L,R⁆ := commutator_mem_commutator ha r.property
      rw [commutator_comm (Q T L) R] at hc
      simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv] using hRQ.le hc
    change ρ a w = w
    simpa only [hr,toAdd_ofAdd] using hh.symm.trans (congrArg Multiplicative.toAdd heq)
  · exact s.imageSpace_finrank_of_index _ (le_conjugateSpanBy _ _) 2 hEV
  · intro l hl w hw
    exact s.imageSpace_apply_mem _ l ((original_commutator_span_normalized h structural).2 hl) w hw


omit [Finite G] in
private theorem spanModule_norm_transfer
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    {τ : Representation (ZMod 2) F.H X}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ)
    (s₀ : BinaryConjugationSection F.H F.U (F.Vi 1) τ)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (ha : (a : G) ∈ F.H)
    (hn : ∀ x, x + τ ⟨a,ha⟩ x + τ ⟨a,ha⟩ (τ ⟨a,ha⟩ x) = 0)
    (w : W) (hw : w ∈ s.imageSpace ⁅F.U,Q T L⁆) :
    w + ρ a w + ρ a (ρ a w) = 0 := by
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  obtain ⟨r,hr,rfl⟩ := (s.mem_imageSpace_iff _ w).mp hw
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_H F).trans (le_normalizer_conjugateSpanBy V F.H))
  let u : F.U := ⟨r,hEU hr⟩
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
    (s.coordinates_eq_one_iff _).mpr (F.le_seed 1 hnU)
  have hh := congrArg Multiplicative.toAdd hnR
  simp only [map_mul, toAdd_mul] at hh
  rw [show (s.coordinates (cR r)).toAdd = ρ a (s.coordinates r).toAdd from s.equivariant a r,
    show (s.coordinates (cR (cR r))).toAdd = ρ a (ρ a (s.coordinates r).toAdd) from
      (s.equivariant a (cR r)).trans (congrArg (ρ a) (s.equivariant a r))] at hh
  exact hh

/-- The point cubic has zero norm on the actual E/V plane, not merely on U/V₁. -/
theorem extraspecial_span_plane_cubic_norm
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ) :
    ∃ a : (L ⊔ (T : Subgroup G) : Subgroup G), (a : G) ∈ F.Li L 1 ∧
      ∀ w ∈ s.imageSpace ⁅F.U,Q T L⁆, w + ρ a w + ρ a (ρ a w) = 0 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨e⟩ := he
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
  apply spanModule_norm_transfer s s₀ aJ a.property
  intro x
  change x + τ a x + τ a (τ a x) = 0
  rw [heq]
  apply hfix
  simp only [map_add,hz3]
  abel


private theorem spanModule_binary_neg {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (w : W) : -w = w := by
  simpa only [CharTwo.neg_eq,one_smul] using (neg_smul (1 : ZMod 2) w).symm

/-- The original point residual acts irreducibly on E/V. The norm relation
supplies full movement, so a binary line quotient would be impossible. -/
theorem extraspecial_span_plane_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ) :
    ∃ D : Subrepresentation (ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))),
      D.toSubmodule = s.imageSpace ⁅F.U,Q T L⁆ ∧ IsIrreducible D.toRepresentation := by
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  let D : Subrepresentation (ρ.comp j) := {
    toSubmodule := s.imageSpace ⁅F.U,Q T L⁆
    apply_mem_toSubmodule a w hw := s.imageSpace_apply_mem _ (j a)
      ((original_commutator_span_normalized h structural).2 (F.Li_le L 1 a.property)) w hw }
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨c,hs,_,_,_,hi,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hd : Module.finrank (ZMod 2) D.toSubmodule = 2 :=
    s.imageSpace_finrank_of_index _ (le_conjugateSpanBy _ _) 2 hi
  obtain ⟨a,ha,hn⟩ := extraspecial_span_plane_cubic_norm h hab structural previous he s
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
             simp only [sub_eq_add_neg,spanModule_binary_neg]
             exact add_comm _ _
           _ = w := (eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hnorm w)).symm
    exact Submodule.subset_span ⟨b,mem_top b,D.toRepresentation b w,Submodule.mem_top,hmove.symm⟩
  exact ⟨D,rfl,Representation.BinaryOffender.irreducible_of_rank_two_full_movement _ hd hm⟩

omit [Finite G] in
/-- The conjugates of the literal E/V plane generate the entire R/V section. -/
theorem extraspecial_span_plane_generates
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ)
    (A : Submodule (ZMod 2) W) (hA : s.imageSpace ⁅F.U,Q T L⁆ ≤ A)
    (hstable : ∀ l : L, ∀ w ∈ A, ρ (inclusion le_sup_left l) w ∈ A) : A = ⊤ := by
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
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

/-- Original application: construct R/V and prove all elementary-section,
plane, and residual-irreducibility inputs to the parabolic module recognition. -/
theorem extraspecial_span_plane_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) R V ρ),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      Module.finrank (ZMod 2) (s.imageSpace ⁅F.U,Q T L⁆) = 2 ∧
      (∃ D : Subrepresentation (ρ.comp (inclusion
        (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))),
        D.toSubmodule = s.imageSpace ⁅F.U,Q T L⁆ ∧ IsIrreducible D.toRepresentation) ∧
      ∀ A : Submodule (ZMod 2) W, s.imageSpace ⁅F.U,Q T L⁆ ≤ A →
        (∀ l : L, ∀ w ∈ A, ρ (inclusion le_sup_left l) w ∈ A) → A = ⊤ := by
  obtain ⟨W,ha,hm,ρ,s,hker,hd,_⟩ :=
    extraspecial_span_binary_section h hab structural previous faithful he
  exact ⟨W,ha,hm,ρ,s,hker,hd,
    extraspecial_span_plane_irreducible h hab structural previous faithful he s,
    extraspecial_span_plane_generates s⟩


open BinaryLinearThree.ParabolicCyclic in
/-- The original section has a Sylow-fixed cyclic seed whose point-parabolic
orbit spans exactly E/V. This supplies the geometric hypotheses of H.6.5
before choosing a matrix marking. -/
theorem extraspecial_span_cyclic_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ) :
    let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
    ∃ w ∈ s.imageSpace ⁅F.U,Q T L⁆, w ≠ 0 ∧
      (∀ t : L, (t : G) ∈ (T : Subgroup G) → τ t w = w) ∧
      orbitSpan τ ⊤ w = ⊤ ∧
      orbitSpan τ (F.H.subgroupOf L) w = s.imageSpace ⁅F.U,Q T L⁆ ∧
      Module.finrank (ZMod 2) (orbitSpan τ (F.H.subgroupOf L) w) = 2 := by
  dsimp only
  let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
  let D := s.imageSpace ⁅F.U,Q T L⁆
  let S := (T : Subgroup G).subgroupOf L
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have stable (l : L) (hl : (l : G) ∈ F.H) (w : W) (hw : w ∈ D) : τ l w ∈ D :=
    s.imageSpace_apply_mem _ (inclusion le_sup_left l)
      ((original_commutator_span_normalized h structural).2 ⟨l.property,hl⟩) w hw
  let : MulAction S D := {
    smul t w := ⟨τ t w,stable t (F.invariant 1 t.property) w w.property⟩
    one_smul w := by apply Subtype.ext; exact congrArg (fun f => f w.val) τ.map_one
    mul_smul t r w := by apply Subtype.ext; exact congrArg (fun f => f w.val) (τ.map_mul t r) }
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype
  obtain ⟨c,hs,_,_,_,hi,_⟩ := extraspecial_span_source_reduction h hab structural previous faithful he
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
  obtain ⟨I,hI,hirr⟩ := extraspecial_span_plane_irreducible h hab structural previous faithful he s
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
    apply extraspecial_span_plane_generates s
    · apply hDA.trans
      apply Submodule.span_mono
      rintro v ⟨a,_,ha⟩
      exact ⟨a,mem_top a,ha⟩
    · intro l v hv
      exact orbitSpan_stable τ ⊤ w l (mem_top l) v hv
  exact ⟨w,w.property,hn,hfix,hfull,hplane,by change Module.finrank (ZMod 2) A = 2; rw [hplane]; exact hd⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
