module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.NaturalConstituents
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness
public import Theory.SpecificGroups.LinearHigher.PresentationFaithfulness
public import Theory.SpecificGroups.PSL5Two.UniversalCover

/-!
# Removing the selected natural chief-factor kernel

The actual SL3 and SL4 matrix presentations map onto any perfect cover with
odd center. Surjections in both directions prove that the original covering
map is injective. The completed PSL5(2) universal-cover calculation supplies
the binary degree-five case directly. All maps and their kernels are retained.

A natural constituent identifies the faithful component image. The proved
covering injection then removes its kernel in the original F*, making the
entire original chief-section action faithful. Applied to the smallest-ratio
factor, this identifies the original B.5.1 component L with SL3(F), SL4(2) or
SL5(2). A.3.6 supplies center oddness, not a covering assumption.

Source: Aschbacher--Smith B.5.1, pp.100–101, (**) and the covering step;
A.3.6(2); Steinberg, Lectures, §6; I.1.3 for PSL5(2).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

omit [Finite L] [IsQuasisimple L] in
private theorem injective_of_surjections {C : Type*} [Group C] [Finite C]
    (f : L →* C) (hf : Function.Surjective f) (s : C →* L) (hs : Function.Surjective s) :
    Function.Injective f := by
  have hi : Function.Injective (f.comp s) := (Finite.injective_iff_surjective).mpr (hf.comp hs)
  intro x y hxy
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  exact congrArg s (hi hxy)

omit [Finite L] in
private theorem injective_linear_of_matrix_faithful
    (F : Type v) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 2 ≤ n)
    (hm : Function.Injective (Theory.SpecificGroups.LinearHigher.matrixMap (n := n) (F := F)))
    (f : L →* SL(n,F)) (hf : Function.Surjective f) (hk : f.ker ≤ center L)
    (ho : Odd (Nat.card (center L))) : Function.Injective f := by
  let c : PerfectCentralCovering.Cover L SL(n,F) := ⟨f, hf, inferInstance, hk⟩
  let q := (QuotientGroup.mk' (center SL(n,F))).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have hker : q.ker = center L := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact c.comap_center
  have hcentral : q.ker ≤ center L := hker.le
  have hcop : (Nat.card q.ker).Coprime 2 := by
    rw [hker]
    exact Nat.coprime_two_right.mpr ho
  obtain ⟨s, hs, _, _⟩ := Theory.SpecificGroups.LinearHigher.exists_covering_of_matrixMap_injective
    q hq hcentral hcop hn hm
  exact injective_of_surjections f hf s hs

omit [Finite L] in
/-- Natural SL3 has no additional odd perfect central covering. The actual
finite-field presentation is faithful also at the two small field orders. -/
theorem natural_three_cover_injective (F : BinaryField)
    (f : L →* SL(3,F.Carrier)) (hf : Function.Surjective f) (hk : f.ker ≤ center L)
    (ho : Odd (Nat.card (center L))) : Function.Injective f := by
  apply injective_linear_of_matrix_faithful F.Carrier 3 (by decide) _ f hf hk ho
  exact Matrix.PSL3.UniversalProjection.matrixMap_injective_of_kernel_torus
    (Matrix.PSL3.UniversalProjection.Faithfulness.kernelTorusReduction_of_torusMultiplicative
      (Matrix.PSL3.UniversalProjection.Faithfulness.torusMultiplicative (F := F.Carrier)))

omit [Finite L] in
/-- The binary degree-four source family has no additional odd central cover. -/
theorem natural_four_cover_injective
    (f : L →* SL(4,ZMod 2)) (hf : Function.Surjective f) (hk : f.ker ≤ center L)
    (ho : Odd (Nat.card (center L))) : Function.Injective f :=
  injective_linear_of_matrix_faithful (ZMod 2) 4 (by decide)
    Theory.SpecificGroups.LinearHigher.matrixMap_four_injective f hf hk ho

/-- The actual PSL5(2) universal cover has trivial kernel, so every
quasisimple cover of the binary natural degree-five actor is injective. -/
theorem natural_five_cover_injective
    (f : L →* SL(5,ZMod 2)) (hf : Function.Surjective f) : Function.Injective f := by
  let P := PSL(5,ZMod 2)
  let : IsQuasisimple P := Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple (ZMod 2)
  let q : Covering L P := ⟨(QuotientGroup.mk' (center SL(5,ZMod 2))).comp f,
    (QuotientGroup.mk'_surjective _).comp hf⟩
  have hu : Covering.IsUniversal (Covering.id : Covering P P) :=
    Theory.SpecificGroups.PSL5Two.UniversalCover.field_identity_isUniversal (ZMod 2) (by norm_num)
  let s := hu.lift q
  have hfac := hu.lift_fac q
  have hi : Function.Injective q := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := s.surjective x
    obtain ⟨b, rfl⟩ := s.surjective y
    have ha : q (s a) = a := congrArg (fun k : Covering P P => k a) hfac
    have hb : q (s b) = b := congrArg (fun k : Covering P P => k b) hfac
    exact congrArg s (ha.symm.trans (hxy.trans hb))
  intro x y hxy
  apply hi
  exact congrArg (QuotientGroup.mk' (center SL(5,ZMod 2))) hxy

/-- The natural group alternatives on an actual faithful chief component. -/
def NaturalActor (C : Type*) [Group C] : Prop :=
  (∃ F : BinaryField, Nonempty (C ≃* SL(3,F.Carrier))) ∨
    ∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (C ≃* SL(d,ZMod 2))

/-- Removing a further central kernel in any of the selected natural rows.
The center oddness is discharged by the source A.3.6 order alternatives. -/
theorem natural_cover_injective {C : Type*} [Group C]
    (hn : NaturalActor C) (f : L →* C) (hf : Function.Surjective f)
    (hk : f.ker ≤ center L) (ho : Odd (Nat.card (center L))) : Function.Injective f := by
  rcases hn with ⟨F, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · have hker : (e.toMonoidHom.comp f).ker ≤ center L := by
      rwa [MonoidHom.ker_comp_of_injective _ _ e.injective]
    intro x y heq
    exact natural_three_cover_injective F (e.toMonoidHom.comp f)
      (e.surjective.comp hf) hker ho (congrArg e heq)
  · rcases hd with rfl | rfl
    · have hker : (e.toMonoidHom.comp f).ker ≤ center L := by
        rwa [MonoidHom.ker_comp_of_injective _ _ e.injective]
      intro x y heq
      exact natural_four_cover_injective (e.toMonoidHom.comp f)
        (e.surjective.comp hf) hker ho (congrArg e heq)
    · intro x y heq
      exact natural_five_cover_injective (e.toMonoidHom.comp f) (e.surjective.comp hf) (congrArg e heq)

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A natural constituent of the literal component/offender overgroup
identifies its original component, using the proved generalized Fitting equality. -/
theorem naturalActor_of_constituent [Finite G] (C : Subgroup G) [IsQuasisimple C]
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : IsBestOffender ρ B)
    (W : Subrepresentation (ρ.comp C.subtype)) (hs : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule)
    (hn : SmallNaturalConstituent (invariantSubspace ρ (C ⊔ B) W.toSubmodule hs).toRepresentation
      (generalizedFitting ↥(C ⊔ B))) : NaturalActor C := by
  let : C.Normal := hfit ▸ generalizedFitting_normal (G := G)
  have hcenter : center G ≤ C := by
    rw [← hfit]
    exact le_trans (show center G ≤ fittingSubgroup G from
      le_sSup ⟨inferInstance, inferInstance⟩) le_sup_left
  have hfit' : generalizedFitting G = C ⊔ center G := by rw [hfit, sup_of_le_left hcenter]
  have hlocal : generalizedFitting ↥(C ⊔ B) = C.subgroupOf (C ⊔ B) :=
    IrreducibleBranch.local_generalizedFitting C B hfit' hcore (hB.1.2.isPGroup 2 B)
  let e : C ≃* generalizedFitting ↥(C ⊔ B) :=
    (subgroupOfEquivOfLe (show C ≤ C ⊔ B from le_sup_left)).symm.trans
      (MulEquiv.subgroupCongr hlocal.symm)
  rcases hn with ⟨F, ⟨a⟩⟩ | ⟨d, hd, ⟨a⟩⟩
  · exact Or.inl ⟨F, ⟨e.trans a.groupEquiv⟩⟩
  · exact Or.inr ⟨d, hd, ⟨e.trans a.groupEquiv⟩⟩

/-- Existence of a nonzero irreducible constituent lets the full natural
decomposition identify its actual component group. -/
theorem naturalActor_of_decomposition [Finite G]
    [Nontrivial V] (C : Subgroup G) [IsQuasisimple C]
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hn : NaturalConstituentDecomposition ρ C) : NaturalActor C := by
  obtain ⟨B, hB, n, W, hd, hW⟩ := hn
  have hnonempty : Nonempty (Fin n) := by
    by_contra! he
    let := he
    have hz := hd.submodule_iSup_eq_top
    simp only [iSup_of_empty] at hz
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    let a := (Representation.asModuleEquiv (ρ.comp C.subtype)).symm v
    have ha : a ∈ (⊥ : Submodule (MonoidAlgebra (ZMod 2) C)
      (Representation.asModule (ρ.comp C.subtype))) := hz.symm ▸ Submodule.mem_top
    have he : a = 0 := ha
    apply hv
    have heq := congrArg (Representation.asModuleEquiv (ρ.comp C.subtype)) he
    simpa only [a, LinearEquiv.apply_symm_apply, map_zero] using heq
  obtain ⟨i⟩ := hnonempty
  obtain ⟨hs, hn⟩ := (hW i).2.2
  exact naturalActor_of_constituent ρ C hfit hcore hB.1 (W i) hs hn

/-- Naturality of the faithful image eliminates the original section
kernel on the quasisimple component, using its actual projection map. -/
theorem ChiefImage.component_projection_injective [Finite G]
    (C : Subgroup G) [IsQuasisimple C]
    (ho : Odd (Nat.card (center C))) (hn : subspaceCommutator ρ ⊤ C ≠ ⊥)
    (hnatural : NaturalActor (ChiefImage.component ρ C)) :
    Function.Injective ((KernelQuotient.projection ρ).subgroupMap C) := by
  let : IsQuasisimple (ChiefImage.component ρ C) := ChiefImage.component_quasisimple ρ C hn
  let c : Covering C (ChiefImage.component ρ C) :=
    ⟨(KernelQuotient.projection ρ).subgroupMap C,
      (KernelQuotient.projection ρ).subgroupMap_surjective C⟩
  exact natural_cover_injective hnatural c.toMonoidHom c.surjective c.ker_le_center ho

/-- Once the natural covering kernel is removed, the original F* is faithful
on the literal section, and so is the entire original section actor. -/
theorem ChiefImage.faithful_of_natural_component [Finite G]
    [IsQuasisimple (generalizedFitting G)]
    (ho : Odd (Nat.card (center (generalizedFitting G))))
    (hn : subspaceCommutator ρ ⊤ (generalizedFitting G) ≠ ⊥)
    (hnatural : NaturalActor (ChiefImage.component ρ (generalizedFitting G))) :
    Function.Injective ρ := by
  apply IrreducibleBranch.faithful_of_fitting_restriction
  intro x y hxy
  apply ChiefImage.component_projection_injective ρ (generalizedFitting G) ho hn hnatural
  apply Subtype.ext
  apply (KernelQuotient.equiv ρ).injective
  change KernelQuotient.equiv ρ (KernelQuotient.projection ρ x.val) =
    KernelQuotient.equiv ρ (KernelQuotient.projection ρ y.val)
  rw [KernelQuotient.equiv_projection, KernelQuotient.equiv_projection]
  apply Subtype.ext
  exact Units.ext hxy

/-- Naturality transports along an actual component isomorphism. -/
theorem NaturalActor.of_equiv {C D : Type*} [Group C] [Group D]
    (e : C ≃* D) (h : NaturalActor D) : NaturalActor C := by
  rcases h with ⟨F, ⟨a⟩⟩ | ⟨d, hd, ⟨a⟩⟩
  · exact Or.inl ⟨F, ⟨e.trans a⟩⟩
  · exact Or.inr ⟨d, hd, ⟨e.trans a⟩⟩

/-- The original covering component is the actual natural group after the
kernel has been proved trivial. -/
theorem ChiefImage.original_naturalActor [Finite G]
    (C : Subgroup G) [IsQuasisimple C]
    (ho : Odd (Nat.card (center C))) (hn : subspaceCommutator ρ ⊤ C ≠ ⊥)
    (hnatural : NaturalActor (ChiefImage.component ρ C)) : NaturalActor C := by
  let e := MulEquiv.ofBijective ((KernelQuotient.projection ρ).subgroupMap C)
    ⟨ChiefImage.component_projection_injective ρ C ho hn hnatural,
      (KernelQuotient.projection ρ).subgroupMap_surjective C⟩
  exact NaturalActor.of_equiv e hnatural

/-- The selected natural chief factor is faithful for the original actor,
not merely for its quotient image. A.3.6 supplies the required odd center. -/
theorem half_flag_factor_reconstruction [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hcore : pCore 2 G = ⊥) (hq : IsPGroup 2 (G ⧸ generalizedFitting G))
    (f : ReducibleChiefFlag ρ (generalizedFitting G)) {i : ℕ} (hi : i ∈ f.noncentral)
    (hhalf : quadraticRatio (imageRepresentation
      (sectionRepresentation ρ (f.chain i) (f.chain (i + 1)))) ≤ 1 / 2) :
    Function.Injective (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) ∧ NaturalActor (generalizedFitting G) := by
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
  let L := generalizedFitting G
  have hirr : IsIrreducible τ := f.irreducible ρ ((f.mem_noncentral i).mp hi).1
  have hn : subspaceCommutator τ ⊤ L ≠ ⊥ := ((f.mem_noncentral i).mp hi).2
  let C := ChiefImage.component τ L
  let : IsQuasisimple C := ChiefImage.component_quasisimple τ L hn
  let := hirr
  let : Nontrivial (↥(f.chain (i + 1)).toSubmodule ⧸
    (sectionLower ρ (f.chain i) (f.chain (i + 1))).toSubmodule) :=
    Subrepresentation.irreducible_module_nontrivial τ
  have hnat := half_flag_factor_natural ρ hK hsemisimple h36 earlier hsq hq f hi hhalf
  have hactor : NaturalActor C := naturalActor_of_decomposition (KernelQuotient.action τ) C
    (ChiefImage.fitting_eq_component τ L hirr hn hq) (ChiefImage.twoCore_eq_bot τ hirr) hnat
  have hcoreL : pCore 2 L = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp
    apply bot_unique
    have hm : (pCore 2 L).map L.subtype ≤ pCore 2 G :=
      le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, pCore_isPGroup.map L.subtype⟩
    exact hm.trans_eq hcore
  have ho : Odd (Nat.card (center L)) := by
    rcases center_order_of_a36 h36 hsq hcoreL with hz | hz <;> rw [hz] <;> decide
  exact ⟨ChiefImage.faithful_of_natural_component τ ho hn hactor,
    ChiefImage.original_naturalActor τ L ho hn hactor⟩

/-- The original reducible B.5.1 hypotheses identify L itself with one of
the three natural source families and give a faithful actual LA-chief factor.
The projection kernel is eliminated by the proved covering calculations. -/
theorem reducible_naturalActor [Finite G]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) :
    NaturalActor L ∧ ∃ A : Subgroup G, IsMinimalBestOffender ρ A ∧
      ∃ f : ReducibleChiefFlag (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A)),
        ∃ i ∈ f.noncentral,
          Function.Injective (sectionRepresentation (ρ.comp (L ⊔ A).subtype)
            (f.chain i) (f.chain (i + 1))) ∧
          ChiefFactorNatural (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A))
            (f.chain i) (f.chain (i + 1)) := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨A, hA, f, hred⟩ := reducible_source_reduction ρ h hnot
  obtain ⟨k, hk, _, hkq, hqhalf⟩ := hred.2.2.2.2
  let H := L ⊔ A
  let σ := ρ.comp H.subtype
  have hp : IsPGroup 2 A := hA.1.1.2.isPGroup 2 A
  have hfit : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  let : IsQuasisimple (L.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hsq : IsSQTK K (generalizedFitting H) := by
    rw [hfit]
    exact (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))).mpr h.sqtk
  have hq : IsPGroup 2 (H ⧸ generalizedFitting H) :=
    (IrreducibleBranch.local_quotient_isTwoGroup L A hp).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hfit.symm)
  have hcore : pCore 2 H = ⊥ :=
    IrreducibleBranch.local_twoCore_eq_bot L H h.fitting h.twoCore le_sup_left
  have hrec := half_flag_factor_reconstruction σ hK hsemisimple h36 earlier hsq hcore hq f hk
    (hkq.trans hqhalf)
  have hn : NaturalActor L := NaturalActor.of_equiv
    ((subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm.trans
      (MulEquiv.subgroupCongr hfit.symm)) hrec.2
  exact ⟨hn, A, hA, f, k, hk, hrec.1,
    half_flag_factor_natural σ hK hsemisimple h36 earlier hsq hq f hk (hkq.trans hqhalf)⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
