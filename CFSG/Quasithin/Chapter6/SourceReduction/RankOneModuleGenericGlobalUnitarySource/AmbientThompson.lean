module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Thompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySecondParabolic
public import CFSG.Quasithin.ChapterD.Section03.HermitianMultiplicity
public import CFSG.Quasithin.Chapter7.NormalizedSource.Automizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.GroupTheory.ElementaryThompsonElementaryCore
public import Theory.GroupTheory.ElementaryThompsonFusion

/-!
# Ambient Thompson and fusion control in the prepared unitary-four rows

The genuine plane-residual comparison transports the conjugation action on
O₂(L), with its original quotient kernel, to the Hermitian four-space.
The full binary normalizer of this action has no FF-offenders when m>1.
Its SQTK premise follows from the original proper-K hypotheses, so every
largest elementary subgroup of the ambient Sylow T centralizes O₂(L).
The completed normalizer local conditions make O₂(L) self-centralizing in G;
maximal elementary order then gives J(T)=O₂(L).

Consequently the core is weakly closed in the original T, its full normalizer
controls fusion there, and centralizers of its elements have Sylow subgroups
inside N_G(L). Both ordinary and degree-two comparisons and both orientations
are retained. The argument does not identify T with the reduced common Sylow.

Source: Aschbacher–Smith F.4.29(6) and the unitary step of F.4.35,
printed pp.289–292, using B.4.2 and A.1.35 (`refs/quasithin.pdf`).
Separation of the two native involution classes, the concrete full-normalizer
realization, outer transfer and F.4.42–43 remain further source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
local instance unitaryFourFixedFieldAlgebra (m : ℕ) : Algebra (ZMod 2) (fixedField m) :=
  ZMod.algebra _ 2
local instance unitaryFourSpaceModule (m : ℕ) [NeZero m] : Module (ZMod 2) (Space m) :=
  Module.compHom (Space m) (algebraMap (ZMod 2) (fixedField m))

omit [Finite G] in
private theorem core_model (m : ℕ) (hm : 1 ≤ m) [NeZero m] (e : L ≃* L2 m hm) :
    IsConjugationModel L (L.pCoreIn 2) (SL2.BinarySmall.hermitian m) := by
  let targetGroup : Group (L2 m hm) := inferInstance
  let eq := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans (L2QuotientEquivSL2 m hm)
  let ec := (e.subgroupMap (pCore 2 L)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let ei : pCore 2 L ≃* L.pCoreIn 2 :=
    (pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective
  let f := ei.symm.trans (ec.trans (L2TwoCoreEquiv m hm).symm)
  refine ⟨eq,f,?_⟩
  intro l v
  have hconj : ec (MulAut.conjNormal l (ei.symm v)) =
      MulAut.conjNormal (e l) (ec (ei.symm v)) := by
    apply Subtype.ext
    change e (l * (ei.symm v : L) * l⁻¹) =
      e l * e (ei.symm v : L) * (e l)⁻¹
    exact (e.map_mul _ _).trans (congrArg₂ (· * ·) (e.map_mul _ _)
      (@MulEquiv.map_inv L (L2 m hm) inferInstance (@Group.toDivisionMonoid _ targetGroup) e l))
  have he := L2TwoCoreEquiv_symm_conj m hm (e l) (ec (ei.symm v))
  rw [←hconj] at he
  have hf : f (ei (MulAut.conjNormal l (ei.symm v))) =
      Multiplicative.ofAdd (SL2.BinarySmall.hermitian m
        (eq (QuotientGroup.mk' (pCore 2 L) l)) (f v).toAdd) := by
    change (L2TwoCoreEquiv m hm).symm (ec (ei.symm (ei _))) = _
    rw [ei.symm_apply_apply]
    exact he
  rw [←hf,f.symm_apply_apply]
  have hv : ((ei.symm v : pCore 2 L) : G) = (v : G) :=
    congrArg Subtype.val (ei.apply_symm_apply v)
  change (l : G) * ((ei.symm v : pCore 2 L) : G) * (l : G)⁻¹ = _
  rw [hv]

/-- The actual left-core action has Hermitian coordinates with its literal two-core quotient. -/
theorem Preparation.unitary_core_hermitian_model
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m) [NeZero m]
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    IsConjugationModel L (L.pCoreIn 2) (SL2.BinarySmall.hermitian m) := by
  obtain ⟨_,_,⟨e⟩,_⟩ := hc.elim
    (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  exact core_model m hm e

/-- The original left core is self-centralizing in the whole ambient group. -/
theorem Preparation.unitary_core_centralizer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    centralizer (L.pCoreIn 2 : Set G) = L.pCoreIn 2 := by
  have hloc := d.unitary_normalizer_local_conditions h hH hp m hm hc
  have hnorm : normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G) := by
    rw [←d.unitary_inner_thompson h hH hp m hm hc]
    exact d.unitary_inner_thompson_normalizer h hH hp m hm hc
  have hself := (inf_centralizer_pCoreIn_le_iff 2 (normalizer (L : Set G))).mpr
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hloc.fitting_left)
  have hcore : (normalizer (L : Set G)).pCoreIn 2 = L.pCoreIn 2 := hloc.twoCore_left
  rw [hcore] at hself
  apply le_antisymm
  · exact (le_inf (hnorm ▸ centralizer_le_normalizer (L.pCoreIn 2 : Set G)) le_rfl).trans hself
  · let : IsElementaryAbelian 2 (pCore 2 L) :=
      (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.1
    let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
    exact (L.pCoreIn 2).le_centralizer

/-- The full ambient Sylow has J(T)=O₂(L), including all possible outer actors. -/
theorem Preparation.unitary_thompson
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    elementaryAbelianMaxJ (T : Subgroup G) = L.pCoreIn 2 := by
  obtain ⟨hm',_,_,_⟩ := hc.elim
    (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  let : NeZero m := ⟨by omega⟩
  let Q := L.pCoreIn 2
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.1
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map L.subtype
  have hnorm : normalizer (Q : Set G) = normalizer (L : Set G) := by
    dsimp only [Q]
    rw [←d.unitary_inner_thompson h hH hp m hm hc]
    exact d.unitary_inner_thompson_normalizer h hH hp m hm hc
  have hLN : L ≤ normalizer (Q : Set G) := hnorm.symm ▸ L.le_normalizer
  have hQT : Q ≤ (T : Subgroup G) := by
    dsimp only [Q]
    rw [←d.unitary_inner_thompson h hH hp m hm hc]
    exact (sSup_le fun _ hE => hE.1).trans inf_le_left
  have hQne : Q ≠ ⊥ := by
    intro he
    have hz : pCore 2 L = ⊥ :=
      (map_eq_bot_iff_of_injective _ L.subtype_injective).mp he
    have hcard := (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.2.1
    rw [hz,Nat.card_unique] at hcard
    have hgt : 1 < (2^m)^4 :=
      Nat.one_lt_pow (by decide) (Nat.one_lt_pow (by omega) (by decide))
    omega
  obtain ⟨e,f,hf⟩ := d.unitary_core_hermitian_model h hH hp m hm hc
  let : IsQuasisimple (L2 m hm ⧸ pCore 2 (L2 m hm)) := L2_quotient_quasisimple m hm
  let : IsQuasisimple SL(2,Field m) := IsQuasisimple.of_mulEquiv (L2QuotientEquivSL2 m hm)
  have hL : IsSQTK KnownSimple.IsKnownSimple L :=
    ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup
      (L.subgroupOf (normalizer (L : Set G)))).knownSimple_of_equiv
      (subgroupOfEquivOfLe L.le_normalizer)
  have hmodel : IsSQTK KnownSimple.IsKnownSimple SL(2,Field m) :=
    (ChapterE.Structure.sqtk_two_quotient hL (pCore 2 L) pCore_isPGroup).knownSimple_of_equiv e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let b : Additive Q ≃ₗ[ZMod 2] Space m :=
    { __ := f.toAdditiveLeft
      map_smul' := ZMod.map_smul f.toAdditiveLeft }
  have hn : ¬ IsFFModule (ChapterE.automizerRepresentation Q) := by
    apply Chapter7.NormalizedSource.automizer_nonFF Q L hLN hnorm.le
      (SL2.BinarySmall.hermitian m) q (e.surjective.comp (QuotientGroup.mk'_surjective _)) b.symm
    · intro l v
      apply Additive.toMul.injective
      apply Subtype.ext
      change (f.symm (Multiplicative.ofAdd
        (SL2.BinarySmall.hermitian m (q l) v)) : G) =
          (l : G) * (f.symm (Multiplicative.ofAdd v) : G) * (l : G)⁻¹
      have he := hf l (b.symm v).toMul
      change (f.symm (Multiplicative.ofAdd
        (SL2.BinarySmall.hermitian m (q l) (f (f.symm (Multiplicative.ofAdd v))).toAdd)) : G) = _ at he
      simp only [f.apply_symm_apply] at he
      exact he
    · exact ChapterD.hermitian_normalizer_not_ff m hmodel hm'
  have hJ := Chapter7.NormalizedSource.thompson_centralizes
    ⟨hQne,hQT,hnorm.symm ▸ h.sylow_normalizes⟩ hn
  rw [d.unitary_core_centralizer h hH hp m hm hc] at hJ
  exact elementaryAbelianMaxJ_eq_of_elementary_overgroup _ _ hJ hQT inferInstance


/-- Every maximum elementary subgroup of the original T is the actual O₂(L). -/
theorem Preparation.unitary_unique_maximum
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    E = L.pCoreIn 2 := by
  have hJ := d.unitary_thompson h hH hp m hm hc
  have hEQ : E ≤ L.pCoreIn 2 := hJ ▸ le_sSup hE
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [←hJ]
    exact sSup_le fun _ hF => hF.1
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.1
  have hQ : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
  exact eq_of_le_of_card_ge hEQ (hE.2.2 _ hQT hQ)

/-- The original left core is weakly closed in T under conjugation by G. -/
theorem Preparation.unitary_core_weakly_closed
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (g : G) (hg : (L.pCoreIn 2).conjBy g ≤ (T : Subgroup G)) :
    (L.pCoreIn 2).conjBy g = L.pCoreIn 2 := by
  have hJ := d.unitary_thompson h hH hp m hm hc
  have he := elementaryAbelianMaxJ_map_eq_of_le (T : Subgroup G)
    (MulAut.conj g) (by rwa [hJ])
  simpa only [hJ, Subgroup.conjBy] using he

/-- The ambient Thompson subgroup recovers the full normalizer of L. -/
theorem Preparation.unitary_thompson_normalizer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) =
      normalizer (L : Set G) := by
  rw [d.unitary_thompson h hH hp m hm hc,
    ←d.unitary_inner_thompson h hH hp m hm hc]
  exact d.unitary_inner_thompson_normalizer h hH hp m hm hc

/-- Burnside fusion in the actual core is controlled by the full normalizer N_G(L). -/
theorem Preparation.unitary_core_fusion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    {x y : G} (hx : x ∈ L.pCoreIn 2) (hy : y ∈ L.pCoreIn 2)
    (hxy : IsConj x y) :
    ∃ g ∈ normalizer (L : Set G), g*x*g⁻¹ = y := by
  have hcen : centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) = L.pCoreIn 2 := by
    rw [d.unitary_thompson h hH hp m hm hc,d.unitary_core_centralizer h hH hp m hm hc]
  have he := maxJ_controls_centralizer_fusion T (hcen.symm ▸ hx) (hcen.symm ▸ hy) hxy
  rwa [d.unitary_thompson_normalizer h hH hp m hm hc] at he

/-- Each core element has an ambient centralizer Sylow contained in N_G(L). -/
theorem Preparation.unitary_core_centralizer_sylow
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (x : G) (hx : x ∈ L.pCoreIn 2) :
    ∃ P : Sylow 2 (centralizer ({x} : Set G)),
      (P : Subgroup (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ≤
        normalizer (L : Set G) := by
  have hcen : centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) = L.pCoreIn 2 := by
    rw [d.unitary_thompson h hH hp m hm hc,d.unitary_core_centralizer h hH hp m hm hc]
  have he := exists_centralizer_sylow_le_maxJ_normalizer T x (hcen.symm ▸ hx)
  rwa [d.unitary_thompson_normalizer h hH hp m hm hc] at he

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

