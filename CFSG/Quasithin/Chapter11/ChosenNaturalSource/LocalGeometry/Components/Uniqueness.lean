module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.Representation.BinaryOffender.PerfectCentralizer
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The noncentral component of the second flag normalizer

Distinct C-components commute modulo their two-cores. If the two-core of
the distinguished component fixes an Irr⁺ module, the other component acts
inside its cyclic linear centralizer. Perfectness makes this action trivial.
The original conjugation action identifies its kernel with the literal
ambient centralizer, giving exactly the noncentralizing convention of
11.1.3. The preceding local Irr⁺ action and core kernel are explicit inputs;
11.1.2 supplies component membership, not uniqueness.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.3, printed p.765, using 1.2.1(2) and A.1.41.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.CentralizerField Representation.BinaryOffender.CentralizerField
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

private theorem perfect_fixes_of_commuting_actions
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) {A B : Subgroup H} [Group.IsPerfect B]
    (hirr : IsIrrPlus ρ A ⊤) (hcomm : ⁅B,A⁆ ≤ ρ.ker) :
    (⊤ : Submodule (ZMod 2) W) ≤ fixedSpace ρ B := by
  let σ := (invariantSubspace ρ A ⊤ hirr.choose).toRepresentation
  let C := linearCentralizer σ
  have hstab : B ≤ subspaceStabilizer ρ ⊤ := le_subspaceStabilizer ρ ⊤ (by simp)
  let a := (stabilizerRepresentation ρ ⊤).asGroupHom.comp (inclusion hstab)
  have ha (b : B) : a b ∈ C := by
    apply (mem_linearCentralizer_iff σ _).mpr
    intro l v
    apply Subtype.ext
    change ρ b (ρ l v) = ρ l (ρ b v)
    have hk : ρ.asGroupHom ⁅(b : H), (l : H)⁆ = 1 := by
      apply Units.ext
      exact hcomm (commutator_mem_commutator b.property l.property)
    rw [map_commutatorElement] at hk
    have hc := congrArg Units.val (commutatorElement_eq_one_iff_mul_comm.mp hk)
    exact LinearMap.congr_fun hc v
  let f : B →* C := a.codRestrict C ha
  let : IsCyclic C :=
    (centralizer_cyclic_odd ρ A ⊤ hirr.choose hirr.choose_spec.1 hirr.choose_spec.2).1
  let : Group.IsSolvable C :=
    Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := C)).comm a b
  have hf (b : B) : f b = 1 := by
    have hm := map_solvableResidual_le f
    rw [solvableResidual_eq_top, solvableResidual_eq_bot, ← MonoidHom.range_eq_map] at hm
    exact mem_bot.mp (hm (MonoidHom.mem_range.mpr ⟨b,rfl⟩))
  intro v hv b
  exact congrArg Subtype.val
    (congrArg (fun c : C => c.val.val (⟨v,hv⟩ : (⊤ : Submodule (ZMod 2) W))) (hf b))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : ChapterB.QuasisimpleSource.BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)

instance flag_elementary (i : Fin 3) : IsElementaryAbelian 2 (f.Vi i) :=
  D.centralQuotientPreimage_elementary _

/-- The actual normalizer action on the original flag preimage, in binary coordinates. -/
@[expose] def flagAction (i : Fin 3) :
    Representation (ZMod 2) (normalizer (f.Vi i : Set G)) (Additive (f.Vi i)) where
  toFun g := ((f.Vi i).normalizerMonoidHom g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    exact DFunLike.congr_fun (map_one (f.Vi i).normalizerMonoidHom) v.toMul
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    exact DFunLike.congr_fun (map_mul (f.Vi i).normalizerMonoidHom g h) v.toMul

/-- The kernel is C_G(V_i) restricted to its actual normalizer. -/
theorem flagAction_ker (i : Fin 3) :
    (flagAction f i).ker =
      (centralizer (f.Vi i : Set G)).subgroupOf (normalizer (f.Vi i : Set G)) := by
  ext g
  constructor
  · intro hg v hv
    have he := congrArg (fun w : Additive (f.Vi i) => (w.toMul : G))
      (LinearMap.congr_fun hg (Additive.ofMul ⟨v,hv⟩))
    change (g : G) * v * (g : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hg
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g : G) * (v.toMul : G) * (g : G)⁻¹ = v.toMul
    exact mul_inv_eq_iff_eq_mul.mpr (hg _ v.toMul.property).symm

/-- The full deduction of 11.1.3 from its preceding component and local-action
conclusions. In particular the distinguished component does not centralize V₂. -/
theorem uniqueNoncentral_second (S : D.NonbinaryNaturalInput)
    (hL : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1))
    (hirr : IsIrrPlus (flagAction f 1)
      ((f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))) ⊤)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  let H := normalizer (f.Vi 1 : Set G)
  let A := (f.Li 1).subgroupOf H
  let ρ := flagAction f 1
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 1)) (pCore 2 H) pCore_isPGroup
  have hcore' : A.pCoreIn 2 ≤ ρ.ker := by
    rw [pCoreIn_subgroupOf 2 _ _ hL.1, flagAction_ker]
    exact comap_mono hcore
  have hn : ¬ f.Li 1 ≤ centralizer (f.Vi 1 : Set G) := by
    intro hc
    apply hirr.not_le_fixedSpace ρ
    intro v _ a
    have hk : (a : H) ∈ ρ.ker := by
      rw [flagAction_ker]
      exact hc a.property
    exact LinearMap.congr_fun hk v
  refine ⟨⟨hL, hn⟩, ?_⟩
  intro K hK
  by_contra hne
  have hne' : K.subgroupOf H ≠ A := by
    intro he
    apply hne
    calc
      K = (K.subgroupOf H).map H.subtype := (map_subgroupOf_eq_of_le hK.1.1).symm
      _ = A.map H.subtype := congrArg (map H.subtype) he
      _ = f.Li 1 := map_subgroupOf_eq_of_le hL.1
  have hcomm := (ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
    hQ hK.1.2 hL.2 hne').1
  let := hK.1.2.perfect
  have hfix := perfect_fixes_of_commuting_actions ρ hirr
    (hcomm.trans (inf_le_right.trans hcore'))
  apply hK.2
  intro k hk v hv
  have hkH := hK.1.1 hk
  have he := hfix (show Additive.ofMul (⟨v,hv⟩ : f.Vi 1) ∈
    (⊤ : Submodule (ZMod 2) (Additive (f.Vi 1))) from trivial)
      (⟨⟨k,hkH⟩,hk⟩ : K.subgroupOf H)
  have he' := congrArg (fun w : Additive (f.Vi 1) => (w.toMul : G)) he
  change k * v * k⁻¹ = v at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

/-- The literal 11.1.2-to-11.1.3 consumer; the field-four triangle is allowed
at the first normalizer and cannot appear at the second. -/
theorem uniqueNoncentral_second_of_refinement (S : D.NonbinaryNaturalInput)
    (K X : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (href : RefinementAlternative T L (f.Li 0) (f.Li 1) K X 1 S.field.degree)
    (hirr : IsIrrPlus (flagAction f 1)
      ((f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))) ⊤)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) :=
  uniqueNoncentral_second f S (second_normal_component hK href).1 hirr hcore

/-- Uniqueness is already available from the sieve's second-normalizer branch,
without waiting for the independent triangle construction at the first one. -/
theorem uniqueNoncentral_second_of_reduction (S : D.NonbinaryNaturalInput)
    (K X : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (href : RefinementReduction L (f.Li 0) (f.Li 1) K X 1 S.field.degree)
    (hirr : IsIrrPlus (flagAction f 1)
      ((f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))) ⊤)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  apply uniqueNoncentral_second f S _ hirr hcore
  rw [href.second_eq]
  exact hK.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
