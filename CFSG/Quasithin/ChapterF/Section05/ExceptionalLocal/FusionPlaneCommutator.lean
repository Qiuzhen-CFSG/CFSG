module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionRoots
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ModelClasses

/-!
# The marked short involution in the exceptional doubled-unitary completion

On the binary Hermitian plane radical, conjugation by the graph involution is
entrywise Frobenius. The image of `X ↦ X + Frobenius(X)` is the line generated
by the short-root parameter `[[0,1],[1,0]]`. Transport through the literal plane
embedding therefore gives the marked source element `t`, with `[Q₂,f] = ⟨t⟩`.

These are the short-root marking, order, placement and commutation inputs to
`FusionFacts`, used by the exceptional normalizer construction in F.5.4.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, F.4.33–37
and F.5.3. No ambient fusion assertion is assumed in this construction.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory Matrix
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
open UnitaryTwo.ModelClasses UnitaryTwo.ShortRootFusion UnitaryTwo.ShortRootQuotient
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2Matrix 1 hn
local notation "W" => hermitianMatrices F σ

def graphParameter (X : W) : W :=
  ⟨fun i j => σ (X.val i j), by
    ext i j
    change σ (σ (X.val j i)) = σ (X.val i j)
    exact congrArg σ (congrFun (congrFun X.property i) j)⟩

private theorem binary_fixed_cases (a : F) (ha : σ a = a) : a = 0 ∨ a = 1 := by
  let x : PointLocal.FixedField 1 := ⟨a,ha⟩
  have hc : Nat.card (PointLocal.FixedField 1) = 2 := PointLocal.fixedField_card 1 hn
  obtain ⟨y,hy,hu⟩ := (Nat.card_eq_two_iff' (0 : PointLocal.FixedField 1)).mp hc
  have hy1 : (1 : PointLocal.FixedField 1) = y := hu 1 one_ne_zero
  by_cases hx : x = 0
  · exact Or.inl (congrArg Subtype.val hx)
  · exact Or.inr (congrArg Subtype.val ((hu x hx).trans hy1.symm))

theorem graphParameter_trace_cases (X : W) : X + graphParameter X = 0 ∨
    X + graphParameter X = shortParameter F σ := by
  have hx (i j : Fin 2) : σ (X.val j i) = X.val i j := congrFun (congrFun X.property i) j
  have ht : σ (X.val 0 1 + σ (X.val 0 1)) = X.val 0 1 + σ (X.val 0 1) := by
    rw [map_add,hσ]; exact add_comm _ _
  have hb := binary_fixed_cases _ ht
  have hsame : X.val 1 0 + σ (X.val 1 0) = X.val 0 1 + σ (X.val 0 1) := by
    rw [hx 0 1,hx 1 0]; exact add_comm _ _
  rcases hb with hb | hb
  · left
    apply Subtype.ext
    ext i j
    change X.val i j + σ (X.val i j) = 0
    fin_cases i <;> fin_cases j
    · exact (congrArg (X.val 0 0 + ·) (hx 0 0)).trans (CharTwo.add_self_eq_zero _)
    · exact hb
    · exact hsame.trans hb
    · exact (congrArg (X.val 1 1 + ·) (hx 1 1)).trans (CharTwo.add_self_eq_zero _)
  · right
    apply Subtype.ext
    ext i j
    change X.val i j + σ (X.val i j) = (shortParameter F σ).val i j
    fin_cases i <;> fin_cases j
    · exact (congrArg (X.val 0 0 + ·) (hx 0 0)).trans (CharTwo.add_self_eq_zero _)
    · exact hb
    · exact hsame.trans hb
    · exact (congrArg (X.val 1 1 + ·) (hx 1 1)).trans (CharTwo.add_self_eq_zero _)

def planeParameterMap : Multiplicative W →* planeParabolic 1 hn :=
  matrixPlaneEquiv.toMonoidHom.comp
    ((radical F σ hσ).subtype.comp (radicalEquiv F σ hσ).toMonoidHom)

theorem planeParameterMap_range : planeParameterMap.range = pCore 2 (planeParabolic 1 hn) := by
  rw [← pCore_map_iso 2 matrixPlaneEquiv]
  ext y
  constructor
  · rintro ⟨X,rfl⟩
    refine ⟨(radicalEquiv F σ hσ X).val, ?_, rfl⟩
    exact (radical_eq_twoCore F σ hσ) ▸ (radicalEquiv F σ hσ X).property
  · rintro ⟨a,ha,rfl⟩
    have ha' : a ∈ radical F σ hσ := (radical_eq_twoCore F σ hσ).symm ▸ ha
    obtain ⟨X,hX⟩ := (radicalEquiv F σ hσ).surjective ⟨a,ha'⟩
    exact ⟨X, congrArg (fun u : radical F σ hσ => matrixPlaneEquiv u.val) hX⟩

theorem planeParameterMap_injective : Function.Injective planeParameterMap :=
  matrixPlaneEquiv.injective.comp (Subtype.val_injective.comp (radicalEquiv F σ hσ).injective)

theorem graph_planeParameter (X : W) :
    (Extension.amalgam 1 hn).right UnitaryTwo.GraphCentralizer.graphInvolution *
      Source.planeInclusion (planeParameterMap (Multiplicative.ofAdd X)) *
      ((Extension.amalgam 1 hn).right UnitaryTwo.GraphCentralizer.graphInvolution)⁻¹ =
        Source.planeInclusion (planeParameterMap (Multiplicative.ofAdd (graphParameter X))) := by
  apply Subtype.ext
  change SemidirectProduct.inr UnitaryFourOuter.generator * SemidirectProduct.inl _ *
    (SemidirectProduct.inr UnitaryFourOuter.generator)⁻¹ = SemidirectProduct.inl _
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  apply congrArg SemidirectProduct.inl
  rw [Extension.projectiveAction_generator]
  change Extension.projectiveAut 1 hn (Extension.projectEquiv 1 hn (unipotentSU F σ hσ X)) =
    Extension.projectEquiv 1 hn (unipotentSU F σ hσ (graphParameter X))
  refine (Extension.projectiveAut_project 1 hn (unipotentSU F σ hσ X)).trans ?_
  apply congrArg (Extension.projectEquiv 1 hn)
  apply Subtype.ext
  apply Units.ext
  ext i j
  change σ ((unipotentMatrix F X.val) i j) = (unipotentMatrix F (graphParameter X).val) i j
  fin_cases i <;> fin_cases j <;> simp [unipotentMatrix, graphParameter]

theorem exists_graphParameter_trace_short :
    ∃ X : W, X + graphParameter X = shortParameter F σ := by
  obtain ⟨b,hb⟩ := PointLocal.fieldConj_nontrivial 1 hn
  let X := fixedParameter F σ hσ b
  rcases graphParameter_trace_cases X with he | he
  · exfalso
    have hh := congrArg (fun Y : W => Y.val 0 1) he
    change b + σ b = 0 at hh
    apply hb
    have hc := congrArg (fun a : F => b + a) hh
    simpa only [CharTwo.add_cancel_left, add_zero] using hc
  · exact ⟨X,he⟩

theorem graphParameter_short : graphParameter (shortParameter F σ) = shortParameter F σ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [graphParameter,shortParameter]

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

def sourcePlaneParameter : Multiplicative W →* G :=
  (ordinaryMap c i true).comp planeParameterMap

def sourceMarkedShort : G :=
  sourcePlaneParameter c i (Multiplicative.ofAdd (shortParameter F σ))

theorem sourcePlaneParameter_range : (sourcePlaneParameter c i).range = Q c i true := by
  rw [Q_eq_map_pCore]
  change (((i.comp c.right).comp Source.planeInclusion).comp planeParameterMap).range =
    (pCore 2 (planeParabolic 1 hn)).map ((i.comp c.right).comp Source.planeInclusion)
  rw [MonoidHom.range_comp,planeParameterMap_range]

theorem sourcePlaneParameter_injective (hi : Function.Injective i) :
    Function.Injective (sourcePlaneParameter c i) :=
  (ordinaryMap_injective c i hi true).comp planeParameterMap_injective

theorem graph_sourcePlaneParameter (X : W) :
    Source.graphElement c i * sourcePlaneParameter c i (Multiplicative.ofAdd X) *
      (Source.graphElement c i)⁻¹ =
        sourcePlaneParameter c i (Multiplicative.ofAdd (graphParameter X)) := by
  have he := congrArg (i.comp c.right) (graph_planeParameter X)
  simp only [map_mul,map_inv] at he
  have hf : (i.comp c.right) ((Extension.amalgam 1 hn).right
      UnitaryTwo.GraphCentralizer.graphInvolution) = Source.graphElement c i :=
    endpointMap_graph c i true
  rw [hf] at he
  exact he

open scoped commutatorElement IsMulCommutative

theorem sourcePlaneParameter_commutator (X : W) :
    ⁅sourcePlaneParameter c i (Multiplicative.ofAdd X), Source.graphElement c i⁆ =
      sourcePlaneParameter c i (Multiplicative.ofAdd (X + graphParameter X)) := by
  have hf := graph_sourcePlaneParameter c i X
  have hq : (sourcePlaneParameter c i (Multiplicative.ofAdd X))⁻¹ =
      sourcePlaneParameter c i (Multiplicative.ofAdd X) := by
    rw [← map_inv]
    apply congrArg (sourcePlaneParameter c i)
    change -X = X
    apply Subtype.ext
    ext a b
    exact CharTwo.neg_eq (X.val a b)
  calc
    _ = sourcePlaneParameter c i (Multiplicative.ofAdd X) *
        (Source.graphElement c i * sourcePlaneParameter c i (Multiplicative.ofAdd X) *
          (Source.graphElement c i)⁻¹) := by rw [commutatorElement_def,hq]; group
    _ = sourcePlaneParameter c i (Multiplicative.ofAdd X) *
        sourcePlaneParameter c i (Multiplicative.ofAdd (graphParameter X)) := by rw [hf]
    _ = _ := (map_mul (sourcePlaneParameter c i) _ _).symm

theorem source_graph_order (hi : Function.Injective i) : orderOf (Source.graphElement c i) = 2 := by
  have hg : orderOf UnitaryTwo.GraphCentralizer.graphInvolution = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨Subtype.ext (Extension.sigma_sq 1 hn), ?_⟩
    intro he
    exact Extension.sigma_ne_one 1 hn (congrArg Subtype.val he)
  exact (orderOf_injective (i.comp c.middle) (hi.comp c.middle_injective) _).trans hg

theorem source_short_mem_Q : sourceMarkedShort c i ∈ Q c i true :=
  sourcePlaneParameter_range c i ▸ ⟨_,rfl⟩

theorem source_short_order (hi : Function.Injective i) : orderOf (sourceMarkedShort c i) = 2 := by
  have ht : orderOf (Multiplicative.ofAdd (shortParameter F σ)) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · rw [pow_two]
      change shortParameter F σ + shortParameter F σ = 0
      apply Subtype.ext
      ext a b
      exact CharTwo.add_self_eq_zero _
    · intro he
      have hh := congrArg (fun X : Multiplicative W => X.toAdd.val 0 1) he
      exact one_ne_zero hh
  exact (orderOf_injective _ (sourcePlaneParameter_injective c i hi) _).trans ht

theorem source_short_commutes_graph : Commute (sourceMarkedShort c i) (Source.graphElement c i) := by
  have hh := graph_sourcePlaneParameter c i (shortParameter F σ)
  rw [graphParameter_short] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem source_short_commutator [Finite G] (hi : Function.Injective i) :
    ⁅Q c i true,zpowers (Source.graphElement c i)⁆ = zpowers (sourceMarkedShort c i) := by
  classical
  apply le_antisymm
  · apply commutator_le.mpr
    intro x hx y hy
    obtain ⟨X,rfl⟩ := (sourcePlaneParameter_range c i).symm ▸ hx
    rw [mem_zpowers_iff_mem_range_orderOf,source_graph_order c i hi] at hy
    obtain ⟨n,hnBound,rfl⟩ := Finset.mem_image.mp hy
    have hn2 := Finset.mem_range.mp hnBound
    interval_cases n
    · simp
    · rw [pow_one]
      change ⁅sourcePlaneParameter c i (Multiplicative.ofAdd X.toAdd),Source.graphElement c i⁆ ∈ _
      rw [sourcePlaneParameter_commutator]
      rcases graphParameter_trace_cases X.toAdd with he | he
      · rw [he]
        change sourcePlaneParameter c i 1 ∈ _
        rw [map_one]
        exact (zpowers (sourceMarkedShort c i)).one_mem
      · rw [he]; exact mem_zpowers _
  · apply zpowers_le.mpr
    obtain ⟨X,hX⟩ := exists_graphParameter_trace_short
    have hh := commutator_mem_commutator
      (show sourcePlaneParameter c i (Multiplicative.ofAdd X) ∈ Q c i true from
        sourcePlaneParameter_range c i ▸ ⟨_,rfl⟩) (mem_zpowers (Source.graphElement c i))
    rwa [sourcePlaneParameter_commutator,hX] at hh

theorem source_root_eq_planeParameter (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    rootElement c i z = sourcePlaneParameter c i (Multiplicative.ofAdd (longParameter F σ)) := by
  have hz := UnitaryTwo.ShortRootFixedFour.root_eq_longPoint z h.root_order
    (sourceRoot_le_pointCoreCenter h.root_mem)
  rw [hz]
  let b : Extension.overlap 1 hn := ⟨(Source.pointInclusion UnitaryTwo.ShortRootFixedFour.longPoint).val,
    by
      rw [← Extension.exact_overlap]
      exact ⟨(Source.pointInclusion UnitaryTwo.ShortRootFixedFour.longPoint).property,
        (Source.planeInclusion (planeParameterMap (Multiplicative.ofAdd (longParameter F σ)))).property⟩⟩
  exact congrArg i (DFunLike.congr_fun c.compatible b)

theorem source_root_mem_Q_plane (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    rootElement c i z ∈ Q c i true := by
  rw [source_root_eq_planeParameter c i z h]
  exact sourcePlaneParameter_range c i ▸ ⟨_,rfl⟩

theorem source_short_commutes_root (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    Commute (sourceMarkedShort c i) (rootElement c i z) := by
  let : IsElementaryAbelian 2 (Q c i true) := source_Q_plane_elementary c i
  exact congrArg Subtype.val (mul_comm
    (⟨sourceMarkedShort c i,source_short_mem_Q c i⟩ : Q c i true)
    ⟨rootElement c i z,source_root_mem_Q_plane c i z h⟩)

theorem planeParameter_mem_extendedUpper (X : Multiplicative W) :
    (Source.planeInclusion (planeParameterMap X)).val ∈ Extension.extendedUpper 1 hn := by
  refine ⟨SemidirectProduct.inl (unipotentSU F σ hσ X.toAdd), ?_, rfl⟩
  change unipotentSU F σ hσ X.toAdd ∈ UnitaryFourSylow.upper F σ hσ
  rw [UnitaryFourSylow.mem_upper_iff_entries]
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [unipotentSU,unipotentMatrix]
  · intro a
    fin_cases a <;> rfl

theorem source_Q_plane_le_sylowImage : Q c i true ≤ Source.sylowImage c i := by
  intro x hx
  obtain ⟨X,rfl⟩ := (sourcePlaneParameter_range c i).symm ▸ hx
  have hX := planeParameter_mem_extendedUpper X
  let b : Extension.overlap 1 hn := ⟨(Source.planeInclusion (planeParameterMap X)).val, by
    obtain ⟨a,ha,he⟩ := hX
    refine ⟨a,?_,he⟩
    change a.left ∈ UnitaryFourFlag.borelSU F (UnitaryFourFlag.form F σ hσ)
    exact UnitaryFourSylow.upper_le_borel F σ hσ ha⟩
  refine ⟨b,hX,?_⟩
  exact congrArg i (DFunLike.congr_fun c.compatible b)

theorem source_short_mem_sylowImage : sourceMarkedShort c i ∈ Source.sylowImage c i :=
  source_Q_plane_le_sylowImage c i (source_short_mem_Q c i)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
