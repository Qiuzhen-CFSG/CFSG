module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation
public import Theory.AtlasPort.LinearGroups.G2.PSL3TwoComponents

/-!
# Marked realization of the fourth-case commutator core

The intrinsic carrier is J = K join R, with L and T the restrictions of K
and R to J. The source product J = LT is an explicit additional premise:
`LinearThreeMSPair` records join generation and subnormality, which do not
by themselves supply it. Under the binary hypotheses the product is
proved equivalent to R normalizing K; neither is asserted unconditionally.

The exceptional MS2 alternative is excluded using the actual image of L
in the claimed G₂(2) quotient: it would be an ordinary PSL₃(2) component.
Thus the product is the only extra premise of `ofProduct`. Restriction
preserves MS3, odd-index radicality, and the original quotient marking e.
The native characteristic replacement and MS93 construction then provide
LocalSource, Geometry and CommonFacts. Nonabelianness of the core is
proved from CaseFour, and the core equivalence uses the actual amalgam,
replacement and join inclusions.

There is also a separate source-specialized route R = T_v. Membership in
Y_z supplies the Sylow condition, so R itself witnesses MS2(a), irrespective
of the input disjunct. Its required normalization is precisely the earlier
13.6.14 conclusion. The general realization from `LinearThreeMSPair` and
CaseFour alone remains unresolved. The final consumer keeps the independent
endpoint factorization explicit; it does not prove the source theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.1.31--34,
printed pp.135--137, 13.6.14, p.929, and 13.6.22, pp.932--933;
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
Sections 2--4 and the Section 7 reduction, printed pp.932--933.
The G₂ exclusion reuses the licensed ATLAS port through
`Theory.AtlasPort.LinearGroups.G2.PSL3TwoComponents`; see LICENSES/ATLAS.txt.
-/

@[expose] public section

open Subgroup
open scoped Pointwise IsMulCommutative
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization

universe u
variable {G : Type u} [Group G]
variable {κ : GroupClass.{u}} {K R S : Subgroup G}

/-- The literal product assertion omitted by the join-based interface. -/
def JoinProduct (K R : Subgroup G) : Prop :=
  ∀ j ∈ K ⊔ R, ∃ k ∈ K, ∃ r ∈ R, k * r = j

/-- Normalization supplies the actual product, not just join generation. -/
theorem joinProduct_of_normalizes (hn : R ≤ normalizer (K : Set G)) :
    JoinProduct K R := by
  intro j hj
  exact Set.mem_mul.mp ((coe_mul_of_right_le_normalizer_left K R hn).symm ▸ hj)

/-- Restriction to the join retains the specified component quotient marking. -/
noncomputable def joinQuotientEquiv
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ((K.subgroupOf (K ⊔ R)) ⧸ pCore 2 (K.subgroupOf (K ⊔ R))) ≃*
      BinaryLinearThree.Group :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left))
    (pCore_map_iso 2 _)).trans e

@[simp] theorem joinQuotientEquiv_mk
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (k : K.subgroupOf (K ⊔ R)) :
    joinQuotientEquiv (R := R) e (QuotientGroup.mk' _ k) =
      e (QuotientGroup.mk' _ ⟨k, k.property⟩) := rfl

private theorem characteristic_map_equivalence {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply (a (e y))

/-- MS3 is transported with characteristicity inside R and normality inside the join. -/
theorem join_characteristic (hMS : LinearThreeMSPair κ K R 1 (ZMod 2)) :
    MSCharacteristicCondition (R.subgroupOf (K ⊔ R)) := by
  let J := K ⊔ R
  let T := R.subgroupOf J
  let e : T ≃* R := subgroupOfEquivOfLe le_sup_right
  intro C hC hne hn
  let := hC
  have he : R.subtype.comp e.toMonoidHom = J.subtype.comp T.subtype := rfl
  have hmap : ((C.map e.toMonoidHom).map R.subtype).subgroupOf J =
      C.map T.subtype := by
    rw [map_map, he, ← map_map]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hz := hMS.characteristic (C.map e.toMonoidHom)
    (characteristic_map_equivalence e C) (hmap.symm ▸ hn)
  exact hne ((map_eq_bot_iff_of_injective _ e.injective).mp hz)

/-- The ordinary MS2 witness is transported by the literal subgroup inclusion. -/
theorem join_oddIndex (hodd : MSOddIndex K R) :
    MSOddIndexRadical (R.subgroupOf (K ⊔ R)) := by
  obtain ⟨A, hA, hindex, hcore⟩ := hodd
  refine ⟨A.subgroupOf (K ⊔ R), ?_, hindex, ?_⟩
  · apply lt_top_iff_ne_top.mpr
    intro he
    apply hA.ne
    have hh := congrArg (map (K ⊔ R).subtype) he
    simpa only [map_subgroupOf_eq_of_le hA.le, ← MonoidHom.range_eq_map,
      range_subtype] using hh
  · apply map_injective (K ⊔ R).subtype_injective
    change ((A.subgroupOf (K ⊔ R)).pCoreIn 2).map (K ⊔ R).subtype = _
    rw [map_pCoreIn_of_injective 2 _ _ (K ⊔ R).subtype_injective,
      map_subgroupOf_eq_of_le hA.le,
      map_subgroupOf_eq_of_le (show R ≤ K ⊔ R from le_sup_right)]
    exact hcore

/-- Construction of the intrinsic MS input, with the two missing source clauses explicit. -/
noncomputable def inputOfProductOddIndex
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hprod : JoinProduct K R) (hodd : MSOddIndex K R) :
    BinaryMS.Input κ (K.subgroupOf (K ⊔ R)) (R.subgroupOf (K ⊔ R)) where
  sqtk := hMS.sqtk
  fitting := hMS.fitting
  product := by
    intro j
    obtain ⟨k, hk, r, hr, he⟩ := hprod j j.property
    exact ⟨⟨k, mem_sup_left hk⟩, hk, ⟨r, mem_sup_right hr⟩, hr, Subtype.ext he⟩
  component := hMS.component.2
  radical := join_oddIndex hodd
  characteristic := join_characteristic hMS
  quotientEquiv := joinQuotientEquiv e

variable [Finite G]

/-- A binary linear-three C-component cannot have the exceptional G₂(2)
ambient quotient. Its actual image there is an ordinary PSL₃(2) component,
contradicting the proved binary G₂ component calculation. -/
theorem not_msExceptional
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) : ¬ MSExceptional K R := by
  rintro ⟨_, f, _⟩
  let J := K ⊔ R
  let L := K.subgroupOf J
  let π := QuotientGroup.mk' (pCore 2 J)
  let B := L.map π
  let D := B.map f.toMonoidHom
  let q : (L ⧸ pCore 2 L) ≃* B := cComponentTwoCoreQuotientEquiv hMS.component.2
  let d : D ≃* BinaryLinearThree.Group :=
    (f.subgroupMap B).symm.trans (q.symm.trans (joinQuotientEquiv e))
  have hs : D.IsSubnormal :=
    (hMS.component.2.subnormal.map (QuotientGroup.mk'_surjective _)).map f.surjective
  let : Theory.GroupTheory.IsQuasisimple BinaryLinearThree.Group :=
    { toIsPerfect := BinaryMS.binary_perfect, simple := Atlas.psl_simple_high_rank 3 (by decide) }
  exact Atlas.G2.PSL3TwoObstructions.no_binary_component D
    ⟨hs, Theory.GroupTheory.IsQuasisimple.of_mulEquiv d.symm⟩
    ⟨d.trans Matrix.PSL3Two.equiv⟩

/-- MS2(a) follows in the binary linear-three branch, including when the
input is presented as a disjunction with MS2(b). -/
theorem oddIndex_of_pair
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) : MSOddIndex K R :=
  hMS.radical.resolve_right (not_msExceptional hMS e)

/-- In the binary branch, obtaining the product is equivalent to proving
R normalizes K; subnormality alone is not substituted for this conclusion. -/
theorem joinProduct_iff_normalizes
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    JoinProduct K R ↔ R ≤ normalizer (K : Set G) := by
  refine ⟨?_, joinProduct_of_normalizes⟩
  intro hp
  have hn := (inputOfProductOddIndex hMS e hp (oddIndex_of_pair hMS e)).component_normal
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    (show K ≤ K ⊔ R from le_sup_left)).mp hn)

omit [Finite G] in
/-- The join's commutator core maps to the original msQ, by its literal inclusion. -/
theorem join_core_map :
    (BinaryMS.commutatorCore (K.subgroupOf (K ⊔ R))).map (K ⊔ R).subtype =
      msQ K R := by
  rw [map_commutator, map_subgroupOf_eq_of_le (show K ≤ K ⊔ R from le_sup_left)]
  rfl

/-- Actual core comparison, induced by the inclusion of the join in G. -/
noncomputable def joinCoreEquiv :
    BinaryMS.commutatorCore (K.subgroupOf (K ⊔ R)) ≃* msQ K R :=
  ((BinaryMS.commutatorCore (K.subgroupOf (K ⊔ R))).equivMapOfInjective
    (K ⊔ R).subtype (K ⊔ R).subtype_injective).trans
      (MulEquiv.subgroupCongr join_core_map)

omit [Finite G] in
@[simp] theorem joinCoreEquiv_apply
    (x : BinaryMS.commutatorCore (K.subgroupOf (K ⊔ R))) :
    (joinCoreEquiv x : G) = ((x : (K ⊔ R : Subgroup G)) : G) := rfl

/-- A constructed setup, including the genuine common reduction and its original marking. -/
structure Data (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) where
  input : BinaryMS.Input κ (K.subgroupOf (K ⊔ R)) (R.subgroupOf (K ⊔ R))
  marking : input.quotientEquiv = joinQuotientEquiv e
  setup : BinaryMS.MS93.InputSetup input
  common : BinaryMS.MS93.CommonFacts setup.reduction.radical setup.source setup.geometry

namespace Data
open BinaryMS.MS93
variable {hMS : LinearThreeMSPair κ K R 1 (ZMod 2)}
    {e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group} (d : Data hMS e)

/-- The original core is recovered through embedM, the replacement inclusion,
and the join inclusion, with no comparison by cardinality. -/
theorem core_pullback :
    (((core d.setup.reduction.radical (alpha d.setup.reduction.radical)).comap
      (Stellmacher.PushingUp.AmalgamGraph.embedM d.setup.reduction.radical)).map
        d.setup.reduction.overgroup.subtype).map (K ⊔ R).subtype = msQ K R := by
  rw [d.setup.core_pullback, join_core_map]

/-- The actual reduced amalgam core is isomorphic to the original msQ. -/
noncomputable def coreEquiv :
    core d.setup.reduction.radical (alpha d.setup.reduction.radical) ≃* msQ K R :=
  d.setup.coreEquiv.trans joinCoreEquiv

/-- The source projection on each original component representative still uses e. -/
theorem projection_component (k : K.subgroupOf (K ⊔ R)) :
    d.setup.source.projection
      ⟨k, (show K.subgroupOf (K ⊔ R) ≤ d.setup.reduction.overgroup from le_sup_left)
        k.property⟩ = e (QuotientGroup.mk' _ ⟨k, k.property⟩) := by
  rw [d.setup.projection_component, d.marking, joinQuotientEquiv_mk]

/-- Consumer of the original-core comparison: endpoint factorization now
suffices to prove nonabelianness of the literal Frattini centralizer. -/
theorem frattiniCentralizer_derived_ne_bot
    (factors : RadiusFourFactors d.setup.reduction.radical d.setup.geometry) :
    let D := msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)
    ⁅D,D⁆ ≠ ⊥ :=
  frattiniCentralizer_derived_ne_bot_of_radiusFactors d.common factors d.coreEquiv

end Data

/-- Construct every setup and common-fact field from the two explicit source
clauses. Nonabelianness is derived from the given fourth alternative. -/
noncomputable def ofProductOddIndex
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hprod : JoinProduct K R) (hodd : MSOddIndex K R) : Data hMS e := by
  let i := inputOfProductOddIndex hMS e hprod hodd
  have hn : ¬ IsMulCommutative (BinaryMS.commutatorCore (K.subgroupOf (K ⊔ R))) := by
    intro hc
    apply caseFour_core_nonabelian e h
    apply isMulCommutative_iff.mpr
    intro x y
    apply joinCoreEquiv.symm.injective
    simpa only [map_mul] using
      isMulCommutative_iff.mp hc (joinCoreEquiv.symm x) (joinCoreEquiv.symm y)
  have hne : BinaryMS.commutatorCore (K.subgroupOf (K ⊔ R)) ≠ ⊥ := by
    intro hz
    apply hn
    rw [hz]
    infer_instance
  let s := BinaryMS.MS93.from_Input i hne
  exact ⟨i, rfl, s, Classical.choice (s.commonFacts hn)⟩

/-- All MS2 alternatives are handled. Only the omitted source product
remains as an extra premise for the general join-based input. -/
noncomputable def ofProduct
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hprod : JoinProduct K R) : Data hMS e :=
  ofProductOddIndex hMS e h hprod (oddIndex_of_pair hMS e)

/-- Equivalent normalizing form of the remaining general product premise. -/
noncomputable def ofNormalizes
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hn : R ≤ normalizer (K : Set G)) : Data hMS e :=
  ofProduct hMS e h (joinProduct_of_normalizes hn)

/-- If the radical itself is Sylow, it is a proper odd-index witness for MS2(a).
This works irrespective of which disjunct was supplied in hMS.radical. -/
theorem oddIndex_of_sylow
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (hS : Chapter1.IsSylowIn 2 R (K ⊔ R)) : MSOddIndex K R := by
  have hp := (Chapter1.isSylowIn_iff.mp hS).1
  have hproper : R < K ⊔ R := by
    apply lt_of_le_not_ge le_sup_right
    intro hle
    have hKR : K ≤ R := le_sup_left.trans hle
    have hk : IsPGroup 2 (K.subgroupOf (K ⊔ R)) :=
      (hp.to_le hKR).comap_subtype
    let := hk.isNilpotent
    exact hMS.component.2.not_isSolvable inferInstance
  refine ⟨R, hproper, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := hS
    have he : R.subgroupOf (K ⊔ R) = (P : Subgroup (K ⊔ R : Subgroup G)) := by
      calc
        R.subgroupOf (K ⊔ R) = ((P : Subgroup (K ⊔ R : Subgroup G)).map
            (K ⊔ R).subtype).subgroupOf (K ⊔ R) := congrArg (fun A => A.subgroupOf (K ⊔ R)) hP.symm
        _ = _ := comap_map_eq_self_of_injective (K ⊔ R).subtype_injective _
    rw [he]
    exact Nat.not_even_iff_odd.mp (fun he => P.not_dvd_index he.two_dvd)
  · have hcore : pCore 2 R = ⊤ :=
      top_unique (le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩)
    rw [pCoreIn, hcore, ← MonoidHom.range_eq_map, range_subtype]

/-- With the genuine Sylow and normalization clauses the realization is complete;
MS2(a) is proved, rather than selected by dropping the exceptional disjunct. -/
noncomputable def ofNormalizesSylow
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hn : R ≤ normalizer (K : Set G)) (hS : Chapter1.IsSylowIn 2 R (K ⊔ R)) :
    Data hMS e :=
  ofProductOddIndex hMS e h (joinProduct_of_normalizes hn) (oddIndex_of_sylow hMS hS)

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection

/-- Source-specialized route for 13.6.22: Yz supplies the literal Sylow
condition, while the earlier-source 13.6.14 normalization remains explicit.
It is not derived here from LinearThreeMSPair. -/
noncomputable def ofSourceSpecialized (L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : CaseFour K (Tv T v) S e) : Data hMS e :=
  ofNormalizesSylow hMS e h hn hK.1.2.2.1

/-- Application to the original fourth-case centralizer in the source-specialized
route. The endpoint factors are the independent remaining MS93 premise. -/
theorem sourceSpecialized_frattiniCentralizer_derived_ne_bot
    (L T : Subgroup G) (z v : G) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : CaseFour K (Tv T v) S e) :
    let d := ofSourceSpecialized L T z v hK hn hMS e h
    RadiusFourFactors d.setup.reduction.radical d.setup.geometry →
      let D := msQ K (Tv T v) ⊓ centralizer (frattiniIn (msQ K (Tv T v)) : Set G)
      ⁅D,D⁆ ≠ ⊥ := by
  dsimp only
  intro factors
  exact (ofSourceSpecialized L T z v hK hn hMS e h).frattiniCentralizer_derived_ne_bot factors

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization
