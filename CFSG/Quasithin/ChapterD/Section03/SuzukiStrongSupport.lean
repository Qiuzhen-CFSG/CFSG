module
public import CFSG.Quasithin.ChapterD.Section03.SuzukiSeedCost
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzukiFive
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedEquivalence
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportStrong
public import Theory.Representation.NormalSimpleConstituent
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting

/-!
# Strong constituents of normal Suzuki-centralizing support

A fixed-free Suzuki component commuting with a starred actor forces a strong
FF inequality on an actual irreducible constituent for the support joined
with that actor. For normal, five-free quasisimple support, the complete
B.5.1 classification then leaves only a natural SL₃ module over a binary
field of odd degree. The support's central kernel is removed using the
perfect-central-cover theorem for SL₃ and its trivial two-core.

The constituent is constructed before it is classified; no invariant or
isotypic support constituent is assumed. The resulting action equivalence
marks the original support, rather than only its action image.

Source: Aschbacher--Smith, B.5.1 and D.3.9, applied to the remaining support
in the module analysis preceding 10.1.1 and 10.2.3, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Choose a genuine irreducible support--actor constituent. The commuting
Suzuki multiplicity bound makes its literal actor image a strong offender. -/
theorem suzuki_exists_strong_support_seed
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible)
    (K : Subgroup G) (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J A : Subgroup G) [J.Normal] [IsQuasisimple J]
    (hA : A ∈ QhatStar ρ) (hKJ : K ≤ centralizer (J : Set G))
    (hKA : K ≤ centralizer (A : Set G)) (hJA : ⁅J,A⁆ = J) :
    ∃ R : Submodule (ZMod 2) V, ∃ hR : J ⊔ A ≤ subspaceStabilizer ρ R,
      IsIrreducible (invariantSubspace ρ (J ⊔ A) R hR).toRepresentation ∧
      ¬ R ≤ fixedSpace ρ J ∧
      IsElementaryTwo (restrictedSubgroup ρ R A) ∧
      fixedCodim (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A) <
        rank (restrictedSubgroup ρ R A) := by
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
  have hJn : J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J).mp inferInstance
  have hJfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi J hJn
  let X := J ⊔ A
  let σ := ρ.comp X.subtype
  obtain ⟨U,hU,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation σ)).resolve_left top_ne_bot
  let R := U.toSubmodule
  have hR : X ≤ subspaceStabilizer ρ R :=
    le_subspaceStabilizer ρ R (fun x hx v hv => U.apply_mem_toSubmodule ⟨x,hx⟩ hv)
  have hir : IsIrreducible (invariantSubspace ρ X R hR).toRepresentation :=
    (Subrepresentation.irreducible_iff_isAtom U).mpr hU
  have hnot : ¬ R ≤ fixedSpace ρ J := by
    intro hh
    exact hU.ne_bot (Subrepresentation.toSubmodule_injective (bot_unique (hh.trans hJfix.le)))
  have hmove : ¬ R ≤ fixedSpace ρ A := by
    intro hh
    exact hnot (hJA ▸ le_fixedSpace_commutator_of_invariant ρ (le_sup_left.trans hR) hh)
  have hc : K ≤ centralizer (X : Set G) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hKJ) (le_centralizer_iff.mp hKA))
  exact ⟨R,hR,hir,hnot,hA.1.2.1.restrictedSubgroup ρ R (le_sup_right.trans hR) hmove,
    suzuki_commuting_seed_strong ρ K hfix m hm e X A hA hc le_sup_right R hR hir hmove⟩
end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
open scoped MatrixGroups
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem strong_actionEquiv {Q W : Type*} [Group Q]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) Q W}
    (e : ActionEquiv ρ σ) (hs : IsStrongFFModule ρ) : IsStrongFFModule σ := by
  obtain ⟨A,hA,hlt⟩ := hs
  have h := (show IsOffender ρ A from ⟨hA,hlt.le⟩).map_equivariant ρ σ
    e.groupEquiv.toMonoidHom e.groupEquiv.injective e.linearEquiv e.intertwines
  refine ⟨A.map e.groupEquiv.toMonoidHom,h.1,?_⟩
  rw [←fixedCodim_map_equivariant ρ σ e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines,
    rank_map_injective _ e.groupEquiv.injective]
  exact hlt

private theorem five_binaryHigher (n : ℕ) (hn : n = 4 ∨ n = 5) :
    5 ∣ Nat.card SL(n,ZMod 2) := by
  rw [BinaryLinear.card_SL]
  rcases hn with rfl | rfl <;> norm_num [BinaryLinear.order,Fin.prod_univ_succ]

private theorem five_symplectic (F : BinaryField) :
    5 ∣ Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp,F.card_eq]
  apply dvd_mul_of_dvd_right
  rw [←pow_mul,Nat.mul_comm F.degree 4]
  exact (by decide : 5 ∣ 2^4-1).trans
    (by apply Nat.pow_sub_one_dvd_pow_sub_one; exact dvd_mul_right 4 F.degree)

/-- The complete source classification leaves only odd-degree natural SL₃
when the action is strong and the ambient group has order prime to five. -/
theorem five_free_strong_source_linearThree
    (ρ : Representation (ZMod 2) G V) (J : Subgroup G)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ J)
    (hm : moved ρ J = ⊤) (hz : fixedSpace ρ J = ⊥)
    (hs : IsStrongFFModule ρ) (hfive : ¬ 5 ∣ Nat.card G) :
    ∃ F : BinaryField, Odd F.degree ∧ Nonempty (ActionEquiv (ρ.comp J.subtype) (linearNatural F 3)) := by
  let s := c.sectionData
  have hs' : IsStrongFFModule s.action := strong_actionEquiv (s.fullActionEquiv hm hz) hs
  have hlt := (isStrongFFModule_iff_quadraticRatio_lt_one s.action).mp hs'
  have hltρ := (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp hs
  have hJfive : ¬ 5 ∣ Nat.card J := fun h => hfive (h.trans J.card_subgroup_dvd_card)
  have hlinear (F : BinaryField) (a : ActionEquiv (s.action.comp J.subtype) (linearNatural F 3)) :
      ∃ F : BinaryField, Odd F.degree ∧ Nonempty (ActionEquiv (ρ.comp J.subtype) (linearNatural F 3)) := by
    let b := s.fullComponentActionEquiv hm hz
    let a' : ActionEquiv (ρ.comp J.subtype) (linearNatural F 3) :=
      ⟨b.groupEquiv.trans a.groupEquiv,b.linearEquiv.trans a.linearEquiv,
        fun g v => (congrArg a.linearEquiv (b.intertwines g v)).trans
          (a.intertwines (b.groupEquiv g) (b.linearEquiv v))⟩
    exact Chapter3.Section02.ChosenSource325.constituentModel_linearThree_of_five_free
      (ρ.comp J.subtype) (Or.inl ⟨F,⟨a'⟩⟩) hJfive
  cases c.clause_one with
  | irreducible _ _ _ hc _ =>
    cases hc with
    | linearThree F _ a _ => exact hlinear F a
    | linearTwo _ _ _ _ hr =>
      rw [hr] at hlt
      exact (lt_irrefl _ hlt).elim
    | g2 _ _ _ _ _ hr =>
      rw [hr] at hlt
      exact (lt_irrefl _ hlt).elim
    | g2Two _ _ hr =>
      rw [hr] at hlt
      exact (lt_irrefl _ hlt).elim
    | symmetric _ _ _ _ hr =>
      rw [hr] at hlt
      exact (lt_irrefl _ hlt).elim
    | alternatingSix _ _ _ hr =>
      rw [hr] at hlt
      exact (lt_irrefl _ hlt).elim
    | alternatingSeven _ _ _ _ _ hr =>
      rw [hr] at hlt
      exact (lt_irrefl _ hlt).elim
    | tripleSix _ _ hr =>
      rw [hr] at hlt
      exact (lt_irrefl _ hlt).elim
    | orthogonalSix _ _ _ _ hr =>
      rw [hr] at hlt
      exact (lt_irrefl _ hlt).elim
    | exteriorFive _ _ _ _ _ hr =>
      rw [hr] at hlt
      exact (lt_irrefl _ hlt).elim
    | symplectic F _ _ a _ =>
      apply (hJfive ?_).elim
      rw [Nat.card_congr a.groupEquiv.toEquiv]
      exact five_symplectic F
    | symplecticTwo a _ =>
      apply (hfive ?_).elim
      apply dvd_trans _ (offenderSubgroup s.action).card_subgroup_dvd_card
      rw [Nat.card_congr a.action.groupEquiv.toEquiv]
      exact five_symplectic BinaryField.two
    | symmetricEight _ a _ =>
      apply (hfive ?_).elim
      apply dvd_trans _ (offenderSubgroup s.action).card_subgroup_dvd_card
      rw [Nat.card_congr a.action.groupEquiv.toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_perm,Fintype.card_fin]
      norm_num
    | binaryLinear d hd _ a _ =>
      apply (hJfive ?_).elim
      rw [Nat.card_congr a.groupEquiv.toEquiv]
      exact five_binaryHigher d hd
  | doubleThree _ _ _ _ hr =>
    rw [hr] at hltρ
    exact (lt_irrefl _ hltρ).elim
  | naturalDual d hd _ a =>
    apply (hJfive ?_).elim
    rw [Nat.card_congr a.some.groupEquiv.toEquiv]
    exact five_binaryHigher d hd
  | repeatedNatural d r hd _ _ _ a =>
    apply (hJfive ?_).elim
    rw [Nat.card_congr a.some.groupEquiv.toEquiv]
    exact five_binaryHigher d hd
end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
/-- Apply B.5.1 on the actual offender-generated subgroup and transport the
natural coordinates back to the original normal quasisimple subgroup. -/
theorem five_free_strong_quasisimple_linearThree
    (ρ : Representation (ZMod 2) G V) (J : Subgroup G) [J.Normal] [IsQuasisimple J]
    (hquot : IsPGroup 2 (G ⧸ J)) (hcore : pCore 2 G = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple J)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hs : IsStrongFFModule ρ) (hfive : ¬ 5 ∣ Nat.card G) :
    ∃ F : BinaryField, Odd F.degree ∧ Nonempty (ActionEquiv (ρ.comp J.subtype) (linearNatural F 3)) := by
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
  have hJn : J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J).mp inferInstance
  have hm := subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf hi J hJn
  have hz := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi J hJn
  obtain ⟨hJO,⟨c⟩⟩ := SourceCompletion.ff_quasisimple_source_conclusion ρ J hquot hcore
    hsq hf (by obtain ⟨A,hA,ha⟩ := hs; exact ⟨A,hA,ha.le⟩)
  let O := offenderSubgroup ρ
  let N := J.subgroupOf O
  let α := ρ.comp O.subtype
  have hm' : moved α N = ⊤ := by
    change subspaceCommutator α ⊤ N = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hJO]
    exact hm
  have hz' : fixedSpace α N = ⊥ := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hJO]
    exact hz
  have hs' : IsStrongFFModule α := by
    by_contra hn
    exact not_strong_of_offenderSubgroup ρ hn hs
  obtain ⟨F,ho,⟨a⟩⟩ := five_free_strong_source_linearThree α N c hm' hz' hs'
    (fun h => hfive (h.trans O.card_subgroup_dvd_card))
  let e : J ≃* N := (subgroupOfEquivOfLe hJO).symm
  exact ⟨F,ho,⟨⟨e.trans a.groupEquiv,a.linearEquiv,
    fun j v => a.intertwines (e j) v⟩⟩⟩
end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
open scoped MatrixGroups
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The central kernel is removed only after identifying the actual image
as SL3 and applying its perfect-central-cover theorem. -/
theorem five_free_strong_invariant_support
    (ρ : Representation (ZMod 2) G V) (J A : Subgroup G) [J.Normal] [IsQuasisimple J]
    (hJ : IsSQTK KnownSimple.IsKnownSimple J) (hcore : pCore 2 J = ⊥)
    (hfive : ¬ 5 ∣ Nat.card J) (hA : IsPGroup 2 A)
    (R : Submodule (ZMod 2) V) (hR : J ⊔ A ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ (J ⊔ A) R hR).toRepresentation)
    (hn : ¬ R ≤ fixedSpace ρ J)
    (hE : IsElementaryTwo (restrictedSubgroup ρ R A))
    (hs : fixedCodim (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A) <
      rank (restrictedSubgroup ρ R A)) :
    ∃ F : BinaryField, Odd F.degree ∧ Nonempty
      (ActionEquiv (invariantSubspace ρ J R (le_sup_left.trans hR)).toRepresentation
        (linearNatural F 3)) := by
  let X := J ⊔ A
  let J₀ := J.subgroupOf X
  let A₀ := A.subgroupOf X
  let eJ : J₀ ≃* J := subgroupOfEquivOfLe (show J ≤ X from le_sup_left)
  let : IsQuasisimple J₀ := IsQuasisimple.of_mulEquiv eJ.symm
  let f := subgroupActionHom ρ R X hR
  let H := f.range
  let q : X →* H := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  let N := J₀.map q
  let C := A₀.map q
  let τ := (subspaceImageRepresentation ρ R).comp H.subtype
  have hτ : Function.Injective τ := (subspaceImageRepresentation_injective ρ R).comp H.subtype_injective
  have hir : IsIrreducible τ :=
    (irreducible_comp_surjective_iff q hq τ).mp hi
  let := hir
  let : N.Normal := Normal.map inferInstance q hq
  let g : J →* N := (q.subgroupMap J₀).comp eJ.symm.toMonoidHom
  have hg : Function.Surjective g := (q.subgroupMap_surjective J₀).comp eJ.symm.surjective
  have hNn : N ≠ ⊥ := by
    intro hz
    apply hn
    intro v hv j
    have hh : g j = 1 := Subtype.ext (hz.le (g j).property)
    exact congrArg Subtype.val (LinearMap.congr_fun
      (congrArg (fun x : N => τ x.val) hh) (⟨v,hv⟩ : R))
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNn
  let : IsQuasisimple N := IsQuasisimple.of_surjective g hg
  have hquotX : IsPGroup 2 (X ⧸ J₀) :=
    ChapterB.QuasisimpleSource.IrreducibleBranch.local_quotient_isTwoGroup J A hA
  have hquot : IsPGroup 2 (H ⧸ N) :=
    hquotX.of_surjective (QuotientGroup.map J₀ N q (fun _ h => mem_map_of_mem q h))
      (QuotientGroup.map_surjective_of_surjective _ _ q
        ((QuotientGroup.mk'_surjective _).comp hq) _)
  have hcoreH : pCore 2 H = ⊥ :=
    bot_unique ((normal_p_subgroup_le_ker τ (pCore 2 H) pCore_isPGroup).trans
      (τ.ker_eq_bot_iff.mpr hτ).le)
  let eg := QuotientGroup.quotientKerEquivOfSurjective g hg
  let : IsQuasisimple (J ⧸ g.ker) := IsQuasisimple.of_mulEquiv eg.symm
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple (J ⧸ g.ker) :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) hJ
      (ChapterA.Section02.IsSectionOf.of_surjective (QuotientGroup.mk' g.ker)
        (QuotientGroup.mk'_surjective g.ker))
  have hsqN := hsqQ.knownSimple_of_equiv eg
  have hfiveN : ¬ 5 ∣ Nat.card N := fun h =>
    hfive (h.trans (card_dvd_of_surjective g hg))
  have hfiveH : ¬ 5 ∣ Nat.card H := by
    rw [N.card_eq_card_quotient_mul_card_subgroup]
    intro h
    rcases (by decide : Nat.Prime 5).dvd_mul.mp h with h | h
    · obtain ⟨k,hk⟩ := hquot.exists_card_eq
      rw [hk] at h
      exact (by decide : ¬ 5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow h)
    · exact hfiveN h
  have hCmap : C.map H.subtype = restrictedSubgroup ρ R A := by
    rw [Subgroup.map_map]
    change A₀.map f = _
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,hR a.property⟩,ha,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a, (le_sup_right : A ≤ X) ha⟩, ⟨ha, rfl⟩⟩
  have hEC : IsElementaryTwo C := by
    refine ⟨fun hh => hE.1 (by rw [←hCmap,hh,Subgroup.map_bot]),?_⟩
    have hCab : IsElementaryAbelian 2 (C.map H.subtype) := by rw [hCmap]; exact hE.2
    let _ : IsElementaryAbelian 2 (C.map H.subtype) := hCab
    exact IsElementaryAbelian.of_injective (H.subtype.subgroupMap C)
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h)))
  have hsτ : IsStrongFFModule τ := by
    refine ⟨C,hEC,?_⟩
    have hc := fixedCodim_map_equivariant τ (subspaceImageRepresentation ρ R)
      H.subtype (LinearEquiv.refl _ _) (fun _ _ => rfl) C
    rw [hCmap] at hc
    have hr := rank_map_injective H.subtype H.subtype_injective C
    rw [hCmap] at hr
    omega
  obtain ⟨F,ho,⟨a⟩⟩ := five_free_strong_quasisimple_linearThree τ N hquot hcoreH hsqN hτ hir hsτ hfiveH
  have hgker : g.ker ≤ center J := by
    rcases IsQuasisimple.normal_le_center_or_eq_top g.ker with h | h
    · exact h
    · exfalso
      obtain ⟨z,hz⟩ := exists_ne (1 : N)
      obtain ⟨j,rfl⟩ := hg z
      have hj : j ∈ g.ker := h ▸ mem_top j
      exact hz (show g j = 1 from hj)
  let cover : PerfectCentralCovering.Cover J SL(3,F.Carrier) := {
    toMonoidHom := a.groupEquiv.toMonoidHom.comp g
    surjective := a.groupEquiv.surjective.comp hg
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ a.groupEquiv.injective]
      exact hgker }
  have hcov := Matrix.SL3.centralCover_injective cover hcore
  let mark := MulEquiv.ofBijective cover.toMonoidHom ⟨hcov,cover.surjective⟩
  exact ⟨F,ho,⟨⟨mark,a.linearEquiv,fun j v => a.intertwines (g j) v⟩⟩⟩
end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Normal five-free support of a Suzuki-centralizing starred actor has an
actual invariant natural SL3 constituent over a field of odd binary degree. -/
theorem suzuki_normal_support_natural_linearThree
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible)
    (K : Subgroup G) (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J A : Subgroup G) [J.Normal] [IsQuasisimple J]
    (hJ : IsSQTK KnownSimple.IsKnownSimple J) (hcore : pCore 2 J = ⊥)
    (hfive : ¬ 5 ∣ Nat.card J)
    (hA : A ∈ QhatStar ρ) (hKJ : K ≤ centralizer (J : Set G))
    (hKA : K ≤ centralizer (A : Set G)) (hJA : ⁅J,A⁆ = J) :
    ∃ F : BinaryField, Odd F.degree ∧ ∃ R : Submodule (ZMod 2) V,
      ∃ hJR : J ≤ subspaceStabilizer ρ R, A ≤ subspaceStabilizer ρ R ∧
        Nonempty (ActionEquiv (invariantSubspace ρ J R hJR).toRepresentation (linearNatural F 3)) := by
  obtain ⟨R,hR,hir,hn,hE,hs⟩ :=
    suzuki_exists_strong_support_seed ρ hf hi K hfix m hm e J A hA hKJ hKA hJA
  let := hA.1.2.1.2
  obtain ⟨F,ho,ha⟩ := five_free_strong_invariant_support ρ J A hJ hcore hfive
    (IsElementaryAbelian.isPGroup 2 A) R hR hir hn hE hs
  exact ⟨F,ho,R,le_sup_left.trans hR,le_sup_right.trans hR,ha⟩
end CFSG.Quasithin.ChapterD
