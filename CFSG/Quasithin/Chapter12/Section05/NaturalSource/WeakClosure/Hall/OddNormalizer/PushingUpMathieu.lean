module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicIdentification
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpCubic
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.MathieuObstruction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicFusion

/-!
# The M₂₂ component at the prescribed exterior cubic

The identified normal C-component of a model-chosen cubic centralizer has
M₂₂ triple cover as its quotient by the two-core. Cubic fusion in the full
original J₄ cover transports it to the cubic lying in the literal intersection
residual. That cubic still fixes sixteen vectors of the original exterior
module and now belongs to the transported component itself.

Its radical quotient is M₂₂, so the marked-normalizer obstruction forces its
ambient image outside M. Normality here is relative to C_K(x). Neither normality
in C_G(x) nor the terminal p.612 commutator contradiction follows merely from
this placement. The separate p.623 odd-local comparison remains required.
OddNormalizer applies the construction to the literal Hall counterexample.
Source: Aschbacher--Smith, 4.2.13, printed p.612, with 12.2.11(a), pp.798--799.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open scoped IsMulCommutative
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter7.NormalizedSource.MathieuGeneration
open Chapter1.Section02.LocalModels

variable {G : Type*} [Group G] [Finite G]

private theorem m22_cover_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsM22Cover X) : IsM22Cover Y := by
  let := h.1
  exact ⟨IsQuasisimple.of_mulEquiv e,
    ⟨(centerCongr e).symm.trans h.2.1.some⟩,
    ⟨(centerQuotientCongr e.symm).trans h.2.2.some⟩⟩

/-- The M₂₂ component is constructed at any prescribed cubic of the full
original pushing-up component, including the one in the exterior residual. -/
theorem exterior_pushingUp_prescribed_cubic_component
    {L V A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hn : K.Normal) (e : (K ⧸ center K) ≃* Janko4.Model)
    (k : K) (hk : orderOf k = 3) :
    ∃ Q : Subgroup (centralizer ({k} : Set K)),
      Q.IsCComponent ∧ Q.Normal ∧ IsM22Cover (Q ⧸ pCore 2 Q) ∧
      (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ Q := by
  obtain ⟨x,hx,hqx,hres,hs,es,Q,hQ,hu⟩ := pushingUp_cubic_component_m22 hw K hn e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
  let C := centralizer ({(x : K)} : Set K)
  have hker : q.ker = center K :=
    (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have hthree : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [hker]
    exact pushingUp_component_center_three_coprime hw K
  obtain ⟨g,hg⟩ := Janko4.LocalStructure.cubic_cyclic_fusion q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hthree (x : K) k
    ((orderOf_coe x).trans hx) hk
  let α := MulAut.conj g
  have hC : C.map α.toMonoidHom = centralizer ({k} : Set K) := by
    change (centralizer ({(x : K)} : Set K)).map α.toMonoidHom = _
    rw [←centralizer_closure,←zpowers_eq_closure,map_centralizer_equiv]
    change centralizer ((zpowers (x : K)).map α.toMonoidHom : Set K) = _
    rw [hg,zpowers_eq_closure,centralizer_closure]
  let c : C ≃* centralizer ({k} : Set K) :=
    (α.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  let B := Q.map c.toMonoidHom
  let b : Q ≃* B := c.subgroupMap Q
  let bq := QuotientGroup.congr (pCore 2 Q) (pCore 2 B) b (pCore_map_iso 2 b)
  let := hQ.2.2.1
  have hmap : B.map (centralizer ({k} : Set K)).subtype =
      (Q.map C.subtype).map α.toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have hxQ : (x : K) ∈ Q.map C.subtype :=
    mem_map_of_mem _ (hQ.2.1
      (mem_map_of_mem (R.subtype.elementCentralizerMap x) hres))
  have hZ := map_mono (f := α.toMonoidHom) (zpowers_le.mpr hxQ)
  rw [hg,←hmap] at hZ
  have hkB : (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ B :=
    (mem_map_iff_mem (centralizer ({k} : Set K)).subtype_injective).mp (hZ (mem_zpowers k))
  exact ⟨B,hQ.1.map_equiv c,
    (inferInstance : Q.Normal).map _ c.surjective,
    m22_cover_transport bq hQ.2.2.2.2.2.1,hkB⟩


private def radical_equiv_of_core_m22 {U : Type*} [Group U] [Finite U]
    (h : IsM22Cover (U ⧸ pCore 2 U)) :
    (U ⧸ solvableRadical U) ≃* Sporadic.Mathieu.M22 := by
  let := h.1
  let := pCore_isNilpotent (p := 2) (G := U)
  let π := QuotientGroup.mk' (pCore 2 U)
  let : Group.IsSolvable π.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hr : solvableRadical (U ⧸ pCore 2 U) = center (U ⧸ pCore 2 U) :=
    le_antisymm IsQuasisimple.solvableRadical_le_center
      (le_solvableRadical _ inferInstance inferInstance)
  exact (solvableRadicalQuotientEquiv π (QuotientGroup.mk'_surjective _)).trans
    ((QuotientGroup.quotientMulEquivOfEq hr).trans h.2.2.some)

variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The actual cubic component escapes the exterior normalizer. Its radical
quotient is M₂₂, while its two-core quotient retains the central triple cover. -/
theorem exterior_pushingUp_cubic_component_escape (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hn : K.Normal) (e : (K ⧸ center K) ≃* Janko4.Model)
    (k : K) (hk : orderOf k = 3) :
    ∃ Q : Subgroup (centralizer ({k} : Set K)),
      Q.IsCComponent ∧ Q.Normal ∧ IsM22Cover (Q ⧸ pCore 2 Q) ∧
      (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ Q ∧
      Nonempty ((Q ⧸ solvableRadical Q) ≃* Sporadic.Mathieu.M22) ∧
      ¬ Q.map (H.subtype.comp (K.subtype.comp
        (centralizer ({k} : Set K)).subtype)) ≤ s.marking.M := by
  obtain ⟨Q,hQ,hnQ,hm,hkQ⟩ := exterior_pushingUp_prescribed_cubic_component hw K hn e k hk
  let := hQ.perfect
  let eq := radical_equiv_of_core_m22 hm
  exact ⟨Q,hQ,hnQ,hm,hkQ,⟨eq⟩,s.marking.mathieu_radical_seed_not_le h Q hQ eq _
    (H.subtype_injective.comp (K.subtype_injective.comp
      (centralizer ({k} : Set K)).subtype_injective))⟩

/-- The p.612 component at the same cubic in the literal intersection residual.
The original full covering component, exterior fixed space and full module are
retained, and the cubic belongs to the new normal C-component. -/
@[expose] def ExteriorPushingUpCubicComponentCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ s.marking.M.subgroupOf H ∧
    1024 ≤ Nat.card W ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Nonempty ((F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      V ≤ K.map H.subtype ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (x : F) (k : K), ((k : H) : G) = (x : G) ∧ orderOf x = 3 ∧ orderOf k = 3 ∧
        16 ≤ Nat.card (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ∧
        ∃ Q : Subgroup (centralizer ({k} : Set K)),
          Q.IsCComponent ∧ Q.Normal ∧ IsM22Cover (Q ⧸ pCore 2 Q) ∧
          (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ Q ∧
          Nonempty ((Q ⧸ solvableRadical Q) ≃* Sporadic.Mathieu.M22) ∧
          ¬ Q.map (H.subtype.comp (K.subtype.comp
            (centralizer ({k} : Set K)).subtype)) ≤ s.marking.M

/-- Construct the M₂₂ component at the original fixed cubic; no additional
placement, quotient identification or escape premise is supplied. -/
theorem exterior_pushingUp_cubic_component_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpCubicCase s A) :
    ExteriorPushingUpCubicComponentCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,_⟩ := hj
  exact ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,exterior_pushingUp_cubic_component_escape s h hw K hn e k hk⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
