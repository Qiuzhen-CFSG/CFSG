module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives.SevenSplitting
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Natural coordinates for the full S₇ offender action

The proper normal offender actor would be A₇. The literal B.5 moved
space would then be four-dimensional and stable under S₇; its action is
faithful by the normal-subgroup structure of S₇. The self-normalizing A₇
four-space theorem excludes that possibility. Hence the offenders generate
the whole S₇ actor. The corrected B.5 clauses give its natural moved space
and a fixed complement, and retain one actor marking for both its embedding
and all fixed codimensions. The original 13.2.12 point-action consumer uses
these coordinates in the Baumann-image contradiction.
Source: Aschbacher--Smith B.4.2(5),(7), B.5.1(1),(2),(4), pp.86,99;
13.2.12, printed p.882.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.SourceSections.SevenNatural
open ClassificationComparison ClassificationComparison.FFAlternatives QuasisimpleComparison

private theorem perm_card {A : Type*} [Group A] (e : A ≃* Equiv.Perm (Fin 7)) :
    Nat.card A = 5040 := by
  rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  decide

/-- A normal quasisimple subgroup of S₇ is its actual alternating subgroup. -/
private theorem quasisimple_equiv_alternating {A : Type*} [Group A] [Finite A]
    (K : Subgroup A) [K.Normal] [IsQuasisimple K] (e : A ≃* Equiv.Perm (Fin 7)) :
    Nonempty (K ≃* alternatingGroup (Fin 7)) := by
  let M := K.map e.toMonoidHom
  let : M.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let : Group.IsPerfect M := Group.IsPerfect.map _
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  let : Nontrivial M := (e.subgroupMap K).symm.surjective.nontrivial
  have hm : M = alternatingGroup (Fin 7) := by
    apply le_antisymm ?_ (Equiv.Perm.alternatingGroup_le_of_normal (by simp) inferInstance)
    rw [←(commutator_eq_self (H := M)),←alternatingGroup.commutator_perm_eq (by simp)]
    exact commutator_mono le_top le_top
  exact ⟨(e.subgroupMap K).trans (MulEquiv.subgroupCongr hm)⟩

/-- In the S₇ offender branch, B.5 supplies an actual natural moved space
with a complement fixed by the full actor. -/
theorem source_natural_split {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (b : BoundedBranch ρ)
    (e : A ≃* Equiv.Perm (Fin 7)) :
    IsCompl b.source.sectionData.space.toSubmodule ρ.invariants ∧
      Nonempty (ActionEquiv b.source.sectionData.space.toRepresentation
        (BinaryPermutation.naturalRepresentation (Fin 7))) := by
  let K := generalizedFitting A
  let : IsQuasisimple K := b.quasisimple
  obtain ⟨eK⟩ := quasisimple_equiv_alternating K e
  have hsplit := Seven.source_split ρ K b.source eK
  let s := b.source.sectionData
  have hz : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact (disjoint_iff.mp hsplit.disjoint).le
      ⟨v.property,fun g => congrArg Subtype.val (hv g)⟩
  have hsplit' : IsCompl s.space.toSubmodule ρ.invariants := by
    by_contra hn
    rcases (b.source.clause_four hn).2 with h | ⟨_,h,_⟩
    · exact h hsplit
    · have bad {n : ℕ} (hn : n = 6 ∨ n = 8)
          (h : IsSymmetricNatural s.space.toRepresentation n) : False := by
        obtain ⟨a⟩ := h
        have hc := perm_card e
        rw [Nat.card_congr a.groupEquiv.toEquiv,Nat.card_eq_fintype_card,
          Fintype.card_perm,Fintype.card_fin] at hc
        rcases hn with rfl | rfl <;> norm_num [Nat.factorial] at hc
      exact h.elim (bad (Or.inl rfl)) (bad (Or.inr rfl))
  rcases Seven.source_natural_or_exceptional ρ b (.symmetricSeven e) eK with h | ⟨a⟩
  · have hc : Nat.card K = 2520 := by
      rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    change Nat.card (generalizedFitting A) = 2520 at hc
    rw [h.1,Nat.card_congr (topEquiv (G := A)).toEquiv,perm_card e] at hc
    omega
  · obtain ⟨a⟩ := a
    let H := offenderSubgroup s.action
    have hH : H = ⊤ := H.eq_top_of_card_eq
      ((perm_card a.action.groupEquiv).trans (perm_card e).symm)
    let eH : A ≃* H := ((MulEquiv.subgroupCongr hH).trans topEquiv).symm
    let l := (s.central.toSubmodule.quotEquivOfEqBot hz).symm
    refine ⟨hsplit',⟨{
      groupEquiv := eH.trans a.action.groupEquiv
      linearEquiv := l.trans a.action.linearEquiv
      intertwines := ?_ }⟩⟩
    intro g v
    change a.action.linearEquiv (l (s.space.toRepresentation g v)) =
      BinaryPermutation.naturalRepresentation (Fin 7) (a.action.groupEquiv (eH g))
        (a.action.linearEquiv (l v))
    have hh : (eH g : A) = g := rfl
    rw [←a.action.intertwines]
    change a.action.linearEquiv (l (s.space.toRepresentation g v)) =
      a.action.linearEquiv ((MovedSection.action ρ s) (eH g) (l v))
    rw [hh]
    congr 1


/-- An S₇ FF actor is generated by its offenders: the other normal
possibility A₇ would force a faithful four-space with a proper normal A₇. -/
theorem offender_eq_top_of_symmetric {E W : Type*} [Group E] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (hf : Function.Injective ρ) (hff : IsFFModule ρ)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (e : E ≃* Equiv.Perm (Fin 7)) : offenderSubgroup ρ = ⊤ := by
  let N := offenderSubgroup ρ
  let : N.Normal := offenderSubgroup_normal ρ
  let M := N.map e.toMonoidHom
  let : M.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr (offenderSubgroup_ne_bot_of_ff ρ hff)
  let : Nontrivial M := (e.subgroupMap N).symm.surjective.nontrivial
  have hAM := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 7))
    (inferInstance : Nontrivial M)
  have hi : M.index ∣ 2 := (alternatingGroup.index_eq_two (α := Fin 7)) ▸ index_dvd_of_le hAM
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
  · have hM : M = ⊤ := index_eq_one.mp hi
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact hM
  have hM : M = alternatingGroup (Fin 7) := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
  let eN : N ≃* alternatingGroup (Fin 7) :=
    (e.subgroupMap N).trans (MulEquiv.subgroupCongr hM)
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup N := eN.isSimpleGroup
  let K := generalizedFitting N
  let : IsQuasisimple K := b.quasisimple
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hK : K = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal K inferInstance).resolve_left
    ((nontrivial_iff_ne_bot K).mp inferInstance)
  let eK := ((MulEquiv.subgroupCongr hK).trans topEquiv).trans eN
  let σ := ρ.comp N.subtype
  let s := b.source.sectionData
  have hsplit := Seven.source_split σ K b.source eK
  have hz : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact (disjoint_iff.mp hsplit.disjoint).le
      ⟨v.property,fun g => congrArg Subtype.val (hv g)⟩
  have hspace : s.space.toSubmodule = subspaceCommutator ρ ⊤ N := by
    rw [s.space_eq]
    change subspaceCommutator σ ⊤ K = _
    rw [subspaceCommutator_comp_map,hK,←MonoidHom.range_eq_map,range_subtype]
  have hfix : fixedSpace σ K = fixedSpace ρ N := by
    rw [fixedSpace_comp_map,hK,←MonoidHom.range_eq_map,range_subtype]
  have hdim := (Seven.source_dimension σ b eN eK).2
  have hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ N) = 4 := by
    rw [←hspace]
    exact (s.central.toSubmodule.quotEquivOfEqBot hz).finrank_eq.symm.trans hdim
  rw [hspace,hfix] at hsplit
  have hstable : (⊤ : Subgroup E) ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ N) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_normalizer_of_normal
  let U : Subrepresentation ρ :=
    ⟨subspaceCommutator ρ ⊤ N,fun g v hv => (hstable (mem_top g) v).2 hv⟩
  let α := U.toRepresentation
  have hkerN : N ⊓ α.ker = ⊥ := by
    apply bot_unique
    rintro g ⟨hg,hgα⟩
    change g = 1
    apply hf
    apply LinearMap.ext
    intro v
    obtain ⟨a,ha,c,hc,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ subspaceCommutator ρ ⊤ N ⊔ fixedSpace ρ N from
        hsplit.sup_eq_top.symm ▸ Submodule.mem_top)
    have ha' : ρ g a = a := congrArg Subtype.val (LinearMap.congr_fun hgα ⟨a,ha⟩)
    change ρ g (a+c) = ρ 1 (a+c)
    rw [map_add,ha',show ρ g c = c from hc ⟨g,hg⟩,map_one]
    rfl
  have hα : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    by_contra hn
    let D := α.ker.map e.toMonoidHom
    let : D.Normal := Subgroup.Normal.map inferInstance _ e.surjective
    let : Nontrivial α.ker := (nontrivial_iff_ne_bot _).mpr hn
    let : Nontrivial D := (e.subgroupMap α.ker).symm.surjective.nontrivial
    have hAD := Equiv.Perm.alternatingGroup_le_of_normal
      (by simp : 5 ≤ Nat.card (Fin 7)) (inferInstance : Nontrivial D)
    have hNker : N ≤ α.ker := (map_le_map_iff_of_injective e.injective).mp (hM ▸ hAD)
    have hNbot : N = ⊥ := by simpa only [inf_eq_left.mpr hNker] using hkerN
    exact (offenderSubgroup_ne_bot_of_ff ρ hff) hNbot
  have hNtop := BinaryAlternatingSevenControl.normal_alternatingSeven_eq_top α hα hd N eN
  exact hNtop


/-- The literal full FF module has a natural submodule and identical fixed
codimensions, with one group marking for both conclusions. -/
theorem natural_coordinates {E W : Type*} [Group E] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (hf : Function.Injective ρ) (hff : IsFFModule ρ)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (e : E ≃* Equiv.Perm (Fin 7)) :
    ∃ a : E ≃* Equiv.Perm (Fin 7),
      (∀ A, fixedCodim ρ A = fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7))
        (A.map a.toMonoidHom)) ∧
      ∃ f : BinaryPermutation.natural (Fin 7) →ₗ[ZMod 2] W,
        Function.Injective f ∧ ∀ g v,
          f (BinaryPermutation.naturalRepresentation (Fin 7) (a g) v) = ρ g (f v) := by
  let N := offenderSubgroup ρ
  have hN : N = ⊤ := offender_eq_top_of_symmetric ρ hf hff b e
  let eN : N ≃* E := (MulEquiv.subgroupCongr hN).trans topEquiv
  let σ := ρ.comp N.subtype
  obtain ⟨hc,⟨a⟩⟩ := source_natural_split σ b (eN.trans e)
  let s := b.source.sectionData
  let a' := eN.symm.trans a.groupEquiv
  let f := s.space.toSubmodule.subtype.comp a.linearEquiv.symm.toLinearMap
  refine ⟨a',?_,f,s.space.toSubmodule.subtype_injective.comp a.linearEquiv.symm.injective,?_⟩
  · intro A
    have hAN : A ≤ N := hN.symm ▸ le_top
    have hcod := (fixedCodim_subrepresentation_eq_iff σ s.space (A.subgroupOf N)).mpr
      (top_unique (hc.sup_eq_top.symm.le.trans
        (sup_le_sup_left (fun v hv g => hv g.val) _)))
    have heq := fixedCodim_map_equivariant s.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7)) a.groupEquiv.toMonoidHom
      a.linearEquiv a.intertwines (A.subgroupOf N)
    have hm : (A.subgroupOf N).map a.groupEquiv.toMonoidHom = A.map a'.toMonoidHom := by
      conv_rhs => rw [←map_subgroupOf_eq_of_le hAN]
      rw [map_map]
      congr 1
    rw [hcod,fixedCodim_subgroupOf ρ hAN,hm] at heq
    exact heq
  · intro g v
    have hh := a.intertwines (eN.symm g) (a.linearEquiv.symm v)
    rw [a.linearEquiv.apply_symm_apply] at hh
    have hh' := congrArg (fun w => (a.linearEquiv.symm w : W)) hh
    have hg : (eN.symm g : E) = g := eN.apply_symm_apply g
    change (a.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 7) (a' g) v) : W) = ρ g (a.linearEquiv.symm v)
    have hh'' : (a.linearEquiv.symm
        (BinaryPermutation.naturalRepresentation (Fin 7) (a' g) v) : W) =
        ρ (eN.symm g : E) (a.linearEquiv.symm v) := by
      simp only [a.linearEquiv.symm_apply_apply] at hh'
      change ρ (eN.symm g : E) (a.linearEquiv.symm v) =
        (a.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 7) (a' g) v) : W) at hh'
      exact hh'.symm
    rwa [hg] at hh''
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.SourceSections.SevenNatural
