module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SourceSmallParabolic
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralMovement
public import Theory.Representation.BinarySymmetricThreeNormalizer
public import Theory.Representation.SmallBinaryFiveOvergroup

/-!
# The whole action of the small chosen module

A marked symmetric-three starred core splits off its centralizer. The faithful
four-dimensional normalizer bound makes that centralizer have order dividing
six; the starred-core movement theorem excludes its involutions. It therefore
has order one or three, giving the first two literal whole-action rows.

For a marked dihedral-ten core, conjugation on its normal five embeds every
two-subgroup in a cyclic four-group. The original Sylow image is nontrivial,
and the Fitting subgroup is the embedded Fitting subgroup of the marked core
or is actually cyclic of order fifteen. The natural Omega row retains its
original coordinates. No whole-action classification premise is used.

Source: Aschbacher--Smith 15.1.7 and 15.2.1, printed pp.1087--1088 and 1104.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

universe u

private theorem cubic_whole_action
    {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hq : quadraticRatio ρ = 2)
    (l : LocalGeneration (ρ.comp (Jhat ρ).subtype)) (hd : DihedralMarking l 3 2) :
    (Jhat ρ = ⊤ ∧ Nonempty (D ≃* Equiv.Perm (Fin 3))) ∨
      (Nonempty (Jhat ρ ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty (D ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 3)))) := by
  let K := Jhat ρ
  let : K.Normal := Jhat_normal ρ
  let j : K ≃* Equiv.Perm (Fin 3) :=
    hd.dihedral.some.trans nonempty_dihedralThreeEquivPerm.some
  let σ := (ρ.comp K.subtype).comp j.symm.toMonoidHom
  have hfull : subspaceCommutator (ρ.comp K.subtype) ⊤ ⊤ = ⊤ := by
    apply top_unique
    calc
      ⊤ = subspaceCommutator (ρ.comp K.subtype) ⊤ l.kernel := l.moved.symm
      _ ≤ subspaceCommutator (ρ.comp K.subtype) ⊤ ⊤ := by
        apply Submodule.span_mono
        rintro _ ⟨g,hg,v,hv,rfl⟩
        exact ⟨g,mem_top _,v,hv,rfl⟩
  have hσ : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    rw [subspaceCommutator_comp_map,map_top_of_surjective _ j.symm.surjective]
    exact hfull
  let C := centralizer (K : Set D)
  have hC : Nat.card C ∣ 6 :=
    BinarySymmetricThreeNormalizer.centralizer_card_dvd_six ρ hf hd.dimension K j
      (BinarySymmetricThreeNormalizer.fixedFree_of_full σ hσ)
  have hodd : ¬ 2 ∣ Nat.card C := by
    intro heven
    obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 heven
    have hto : orderOf (t : D) = 2 := (Subgroup.orderOf_coe t).trans ht
    have hp : PrimeDimensionOptions 3 2 :=
      (primeDimensionOptions_iff 3 2).mpr (Or.inl ⟨rfl,Or.inr rfl⟩)
    apply dihedral_prime_moves_twoGroup ρ hf hq l hp hd (zpowers (t : D))
      (IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using hto))
      (by intro hb; have hh := Nat.card_zpowers (t : D); rw [hb,card_bot,hto] at hh; omega)
    exact (zpowers_le.mpr t.property).trans (centralizer_le (map_subtype_le l.kernel))
  have hc : Nat.card C = 1 ∨ Nat.card C = 3 := by
    have hm := Nat.mem_divisors.mpr ⟨hC,by decide⟩
    rw [show Nat.divisors 6 = {1,2,3,6} by decide] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    omega
  rcases hc with hc | hc
  · left
    have hCb : C = ⊥ := (eq_bot_iff_card C).mpr hc
    have hKt : K = ⊤ := by
      have hh := NormalSymmetricThree.sup_centralizer_eq_top K j
      change K ⊔ C = ⊤ at hh
      simpa only [hCb,sup_bot_eq] using hh
    exact ⟨hKt,⟨((MulEquiv.subgroupCongr hKt).trans topEquiv).symm.trans j⟩⟩
  · right
    obtain ⟨e,_⟩ := NormalSymmetricThree.exists_product_equiv K j
    let c : C ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hc (by simp)
    exact ⟨⟨j⟩,⟨e.symm.trans (j.prodCongr c)⟩⟩

private theorem five_fitting_kernel
    {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (l : LocalGeneration ρ) (hd : DihedralMarking l 5 2) :
    fittingSubgroup D = l.kernel := by
  let := l.normal
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic l.kernel := isCyclic_of_prime_card hd.card_kernel
  apply le_antisymm
  · have hcore := SmallBinaryFiveOvergroup.twoCore_eq_bot ρ hf hd.dimension l.kernel hd.card_kernel
    exact (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore).trans
      (pPrimeCore_le_pResidual.trans_eq l.kernel_eq_twoResidual.symm)
  · exact le_sSup ⟨inferInstance,inferInstance⟩

variable {G : Type*} [Group G] [Finite G]

/-- Original 15.2.1 on the actual chosen action image, with all four rows. -/
theorem ChosenSmallSource.action_alternatives
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    letI := h.prepared.elementary
    SmallActionAlternatives T M V h.prepared.normalized := by
  let := h.prepared.elementary
  let ρ := imageRepresentation M V h.prepared.normalized
  let D := internalActionImage M V h.prepared.normalized
  let K := Jhat ρ
  let : K.Normal := Jhat_normal ρ
  have hf : Function.Injective ρ := imageRepresentation_injective _ _ _
  rcases h.small with ⟨l,p,m,hpm,hd⟩ | ho
  · have hm := h.marking_dimension l p m hd
    subst m
    rcases (primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · rcases cubic_whole_action ρ hf h.prepared.quadratic_ratio l hd with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      refine ⟨hd.dihedral,?_,?_⟩
      · let P := l.kernel.map K.subtype
        have hmks := hd.ambient_marks K hpm
        let : P.Normal := hmks.2.2.2.1
        let Q : Sylow 2 D := (T.subtype h.maximal.1.2).mapSurjective
          (actionHom M V h.prepared.normalized).rangeRestrict_surjective
        have hQ : IsCyclic Q ∧ Nat.card Q ∣ 4 :=
          SmallBinaryFiveOvergroup.two_subgroup ρ hf h.finrank_eq_four P hmks.2.2.1
            (Q : Subgroup D) Q.isPGroup'
        have htwo : 2 ∣ Nat.card D := by
          have hh := K.card_subgroup_dvd_card
          rw [hmks.1] at hh
          exact (by decide : 2 ∣ 2*5).trans hh
        have hdiv := Q.dvd_card_of_dvd_card htwo
        have hc : Nat.card Q = 2 ∨ Nat.card Q = 4 := by
          have hh := Nat.mem_divisors.mpr ⟨hQ.2,by decide⟩
          rw [show Nat.divisors 4 = {1,2,4} by decide] at hh
          simp only [Finset.mem_insert,Finset.mem_singleton] at hh
          omega
        let := hQ.1
        change Nonempty (Q ≃* Multiplicative (ZMod 2)) ∨
          Nonempty (Q ≃* Multiplicative (ZMod 4))
        rcases hc with hc | hc
        · exact Or.inl ⟨mulEquivOfCyclicCardEq (by simpa using hc)⟩
        · exact Or.inr ⟨mulEquivOfCyclicCardEq (by simpa using hc)⟩
      · let P := l.kernel.map K.subtype
        have hmks := hd.ambient_marks K hpm
        let : P.Normal := hmks.2.2.2.1
        have hh := SmallBinaryFiveOvergroup.fitting_alternatives ρ hf
          h.finrank_eq_four P hmks.2.2.1
        have hk : fittingSubgroup K = l.kernel :=
          five_fitting_kernel (ρ.comp K.subtype) (hf.comp K.subtype_injective) l hd
        change fittingSubgroup D = (fittingSubgroup K).map K.subtype ∨ _
        rw [hk]
        exact hh
  · exact Or.inr (Or.inr (Or.inl ho))

end CFSG.Quasithin.Chapter15.Section02
