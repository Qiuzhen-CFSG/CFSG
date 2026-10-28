module
public import Stellmacher.SectionEight.EightSixSelectedResidualDecomposition
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreIntersection
public import Stellmacher.SectionEight.EightSixSelectedActorCostCases
/-!
Every predecessor actor has the same literal displacement cost on Vnext/Znext,
Y/Znext and Vnext/C, where Y=[Qnext,O²(E)] and C=Vnext intersect C_G(O²(E)).
The theorem retains the actual source-(12) configuration and the previously
proved fixed-core containment V0≤Qa, rather than assuming any quotient model.

The selected residual decomposition gives Vnext=Y C and Y intersect C=Znext.
Source (11) and V0≤Qa give [C,A]≤Znext. Expanding a commutator of a product
from Y C therefore identifies the joined displacement subgroups modulo Znext.
All displacement lies in Y, so its intersections with C and Znext agree.
The exact relative-index identities then change the denominator from Znext
to C. These are the literal cost transfers used in the cost-four paragraph
and assertion (17), printed pp.44–45 of Stellmacher (8.6).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement Pointwise
universe u
public theorem eight_six_selected_cost_residual_transfer
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hV0Qa : QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (twoResidualIn E : Set G) ≤ QAt ctx.Γ ctx.criticalPath.a)
    (mover : G) (hmover : mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) :
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    let Y := ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆
    let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
    eightSixCommutatorCost ctx.Γ ctx.criticalPath mover =
      Z.relIndex (⁅Y,Subgroup.zpowers mover⁆ ⊔ Z) ∧
      eightSixCommutatorCost ctx.Γ ctx.criticalPath mover =
        C.relIndex (⁅V,Subgroup.zpowers mover⁆ ⊔ C) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlen : cp.length = 2 := hlength
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let P := GAt Γ cp.firstStep
  let B := twoResidualIn E
  let Y := ⁅R,B⁆
  let C := V ⊓ Subgroup.centralizer (B : Set G)
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let T := Subgroup.zpowers mover
  let J := ⁅V,T⁆
  let K := ⁅Y,T⁆
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hTE : T ≤ E := Subgroup.zpowers_le.mpr (hAE hmover)
  have hBE : B ≤ E := SevenSix.twoResidualIn_le E
  have hER : E ≤ Subgroup.normalizer (R : Set G) :=
    geom.group_le.trans (SevenSix.stabilizer_le_normalizer_q Γ _)
  have hEB : E ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mp (SevenSix.twoResidualIn_normal E)
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    intro e he
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (⁅R,B⁆).map (MulAut.conj e).toMonoidHom = ⁅R,B⁆
    rw [Subgroup.map_commutator]
    exact congrArg₂ (fun K J : Subgroup G => ⁅K,J⁆)
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hER he))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEB he))
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) _
  have hRP : R ≤ P := by
    change Γ.twoCoreAt _ ≤ Γ.vertexStabilizer _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hsplit : V = Y ⊔ C := hpacket.2.2
  have hinter : Y ⊓ C = Z := hpacket.2.1
  have hYV : Y ≤ V := hsplit ▸ le_sup_left
  have hZY : Z ≤ Y := hinter ▸ inf_le_left
  have hZC : Z ≤ C := hinter ▸ inf_le_right
  have hZV : Z ≤ V := hZY.trans hYV
  have hCY : C ≤ Subgroup.normalizer (Y : Set G) :=
    (inf_le_left.trans hVR).trans (Subgroup.normalizer_commutator_ge_left R B)
  have hCZ : ⁅C,T⁆ ≤ Z := by
    have hc := (eight_six_selected_fixed_core_commutator_bounds ctx hcenter hquot hlength hcard
      previous D L Q hprev hD hL data E A0 actor geom hedge).1
    have hC0 : C ≤ R ⊓ Subgroup.centralizer (B : Set G) := inf_le_inf hVR le_rfl
    exact (Subgroup.commutator_mono (le_inf hC0 (hC0.trans hV0Qa))
      (Subgroup.zpowers_le.mpr hmover)).trans hc
  have hZN : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ _
  have hJle : J ≤ K ⊔ Z := by
    apply Subgroup.commutator_le.mpr
    intro v hv t ht
    have hvprod : v ∈ (Y : Set G) * (C : Set G) := by
      rw [←Subgroup.coe_mul_of_right_le_normalizer_left Y C hCY]
      exact hsplit ▸ hv
    obtain ⟨y,hy,c,hc,rfl⟩ := hvprod
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact (K ⊔ Z).mul_mem (Subgroup.mem_sup_right
      ((Subgroup.mem_normalizer_iff.mp (hZN (hRP (hVR (hYV hy)))) _).mp
        (hCZ (Subgroup.commutator_mem_commutator hc ht))))
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hy ht))
  have hKeY : K ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp (hTE.trans hEY)
  have hJY : J ≤ Y := hJle.trans (sup_le hKeY hZY)
  have hjoin : J ⊔ Z = K ⊔ Z := le_antisymm (sup_le hJle le_sup_right)
    (sup_le_sup (Subgroup.commutator_mono hYV le_rfl) le_rfl)
  have hJV : J ≤ V := hJY.trans hYV
  have hVNC : V ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      (((Subgroup.commutator_mono le_rfl (inf_le_left.trans hVR)).trans_eq
        data.first_commutator).trans hZC)
  let _ : (C.subgroupOf V).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hVNC
  let _ : (Z.subgroupOf V).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    ((hVR.trans hRP).trans hZN)
  have hCindex := Subgroup.relIndex_sup_right (J.subgroupOf V) (C.subgroupOf V)
  rw [←Subgroup.subgroupOf_sup hJV (show C ≤ V from inf_le_left),
    Subgroup.relIndex_subgroupOf (sup_le hJV inf_le_left),
    Subgroup.relIndex_subgroupOf hJV] at hCindex
  have hZindex := Subgroup.relIndex_sup_right (J.subgroupOf V) (Z.subgroupOf V)
  rw [←Subgroup.subgroupOf_sup hJV hZV,
    Subgroup.relIndex_subgroupOf (sup_le hJV hZV),Subgroup.relIndex_subgroupOf hJV] at hZindex
  have hCJ : C.subgroupOf J = Z.subgroupOf J := by
    ext j
    change (j:G) ∈ C ↔ (j:G) ∈ Z
    rw [←hinter]
    exact ⟨fun hj => ⟨hJY j.property,hj⟩,fun hj => hj.2⟩
  change Z.relIndex (J ⊔ Z) = Z.relIndex (K ⊔ Z) ∧
    Z.relIndex (J ⊔ Z) = C.relIndex (J ⊔ C)
  refine ⟨congrArg (Subgroup.relIndex Z) hjoin,?_⟩
  rw [hZindex,hCindex]
  change (Z.subgroupOf J).index = (C.subgroupOf J).index
  rw [hCJ]

end Stellmacher.SectionEight
