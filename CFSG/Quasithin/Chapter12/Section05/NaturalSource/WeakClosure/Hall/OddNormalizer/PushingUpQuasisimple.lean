module
public import Theory.GroupTheory.GeneralizedFitting.FixedSeedQuasisimple
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpResidual

/-!
# The full ordinary Mathieu component at the exterior cubic

The simultaneous-centralizer residual is an ordinary component in the
centralizer of the full inverse image of the marked involution subgroup.
That inverse image is a two-group because the original J₄ covering
component has two-group center. Thompson's A × B lemma centralizes the
full cubic residual's two-core, proving quasisimplicity. Cubic fusion
transports this result to the original exterior marking, where the residual
was already identified and shown to escape M. Its central quotient is M₂₂,
and its literal image is an ordinary component of C_H(x).

The construction preserves the full exterior module of order at least 1024,
the actual PSL₅(2) section, sixteen fixed vectors, the full J₄ central cover,
and the M₂₂ triple-cover two-core quotient. Promotion from C_H(x) still
requires the source's involution and overgroup selection; it does not follow
from the relative normality proved here. The separate p.623 odd-local
comparison and the terminal commutator contradiction remain required.

Source: Aschbacher--Smith 4.2.13, printed p.612. OddNormalizer supplies the
literal Hall-counterexample application of 12.2.11(a), pp.798--799.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter7.NormalizedSource.MathieuGeneration
open Chapter1.Section02.LocalModels
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The full residual at the prescribed exterior cubic is quasisimple.
The proof retains the original full J₄ cover and its two-group center. -/
theorem exterior_pushingUp_cubic_residual_quasisimple (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (hn : K.Normal)
    (e : (K ⧸ center K) ≃* Janko4.Model) (k : K) (hk : orderOf k = 3) :
    IsQuasisimple (solvableResidual (centralizer ({k} : Set K))) := by
  let := hn
  let := hK.2
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center K :=
    (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have hker2 : IsPGroup 2 q.ker := by
    rw [hker,IsQuasisimple.center_eq_pCore
      (hK.1.pPrimeCore_eq_bot hw.2.2.2.2.2.2.2.2.2.2.2.2.1 K)]
    exact pCore_isPGroup
  have hthree : Nat.Coprime 3 (Nat.card q.ker) :=
    hker.symm ▸ pushingUp_component_center_three_coprime hw K
  obtain ⟨x,hx,hqx,hres,hs,es⟩ :=
    Janko4.InvolutionCentralizers.First.CubicResidual.exists_cubic_residual_containing_lift_of_central_cover
      q hq hker.le hthree
  let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
  let C := centralizer ({(x : K)} : Set K)
  let Q := solvableResidual C
  have hxK : orderOf (x : K) = 3 := (orderOf_coe x).trans hx
  have hfull := exterior_pushingUp_full_cubic_residual s h hw K hK hn e (x : K) hxK
  obtain ⟨B,hB,hseed⟩ := central_cover_residual_fixed_seed q hq hker.le hker2
    Janko4.a (IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,Janko4.orderOf_a,pow_one])) x hres hs
  let : IsQuasisimple (Q ⧸ pCore 2 Q) := hfull.2.1.1
  let : IsQuasisimple Q := hfull.1.quasisimple_of_fixed_component hseed hB
    (map_solvableResidual_le (R.subtype.elementCentralizerMap x))
  obtain ⟨g,hg⟩ := Janko4.LocalStructure.cubic_cyclic_fusion q hq hthree (x : K) k hxK hk
  let α := MulAut.conj g
  have hC : C.map α.toMonoidHom = centralizer ({k} : Set K) := by
    change (centralizer ({(x : K)} : Set K)).map α.toMonoidHom = _
    rw [←centralizer_closure,←zpowers_eq_closure,map_centralizer_equiv]
    change centralizer ((zpowers (x : K)).map α.toMonoidHom : Set K) = _
    rw [hg,zpowers_eq_closure,centralizer_closure]
  let c : C ≃* centralizer ({k} : Set K) :=
    (α.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  let r : Q ≃* solvableResidual (centralizer ({k} : Set K)) :=
    (c.subgroupMap Q).trans (MulEquiv.subgroupCongr
      (map_solvableResidual_eq c.toMonoidHom c.surjective))
  exact IsQuasisimple.of_mulEquiv r

/-- The central quotient of the full cubic residual is the native M₂₂. -/
theorem exterior_pushingUp_cubic_residual_center_quotient (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (hn : K.Normal)
    (e : (K ⧸ center K) ≃* Janko4.Model) (k : K) (hk : orderOf k = 3) :
    let Q := solvableResidual (centralizer ({k} : Set K))
    Nonempty ((Q ⧸ center Q) ≃* Sporadic.Mathieu.M22) := by
  let Q := solvableResidual (centralizer ({k} : Set K))
  let := exterior_pushingUp_cubic_residual_quasisimple s h hw K hK hn e k hk
  have hz : solvableRadical Q = center Q := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm))
  obtain ⟨hQ,hm,hnQ,hkQ,⟨eq⟩,hout⟩ :=
    exterior_pushingUp_full_cubic_residual s h hw K hK hn e k hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hz.symm).trans eq⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The full residual is an ordinary component of the centralizer in H,
with the original inclusion of K into H. -/
theorem exterior_pushingUp_cubic_residual_component (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (hn : K.Normal)
    (e : (K ⧸ center K) ≃* Janko4.Model) (k : K) (hk : orderOf k = 3) :
    IsComponent (centralizer ({(k : H)} : Set H))
      ((solvableResidual (centralizer ({k} : Set K))).map
        (K.subtype.elementCentralizerMap k)) := by
  let := hn
  let Q := solvableResidual (centralizer ({k} : Set K))
  let f := K.subtype.elementCentralizerMap k
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg
      (fun c : centralizer ({(k : H)} : Set H) => (c : H)) he))
  let := exterior_pushingUp_cubic_residual_quasisimple s h hw K hK hn e k hk
  exact ⟨(exterior_pushingUp_cubic_residual_normal K k).isSubnormal,
    IsQuasisimple.of_mulEquiv (Q.equivMapOfInjective f hf)⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
/-- The original exterior witnesses with the full quasisimple cubic residual
and its ordinary component image in C_H(x). -/
@[expose] def ExteriorPushingUpOrdinaryResidualCase (s : SylowExteriorMarking D)
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
        let R := solvableResidual (centralizer ({k} : Set K))
        IsQuasisimple R ∧ Nonempty ((R ⧸ center R) ≃* Sporadic.Mathieu.M22) ∧
          IsComponent (centralizer ({(k : H)} : Set H))
            (R.map (K.subtype.elementCentralizerMap k)) ∧
          R.IsCComponent ∧ IsM22Cover (R ⧸ pCore 2 R) ∧
          (R.map (K.subtype.elementCentralizerMap k)).Normal ∧
          (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ R ∧
          Nonempty ((R ⧸ solvableRadical R) ≃* Sporadic.Mathieu.M22) ∧
          ¬ R.map (H.subtype.comp (K.subtype.comp
            (centralizer ({k} : Set K)).subtype)) ≤ s.marking.M

/-- Promote the already identified full cubic residual to a quasisimple
ordinary component, retaining the full original exterior configuration. -/
theorem exterior_pushingUp_ordinary_residual_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpFullResidualCase s A) :
    ExteriorPushingUpOrdinaryResidualCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres⟩ := hj
  exact ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,
    exterior_pushingUp_cubic_residual_quasisimple s h hw K hK hn e k hk,
    exterior_pushingUp_cubic_residual_center_quotient s h hw K hK hn e k hk,
    exterior_pushingUp_cubic_residual_component s h hw K hK hn e k hk,hres⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
