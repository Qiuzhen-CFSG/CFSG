module
public import Stellmacher.SectionNine.NineTenActorQuotientKernel
public import Stellmacher.SectionNine.NineTenNormalNeighborhoodGeneration
public import Stellmacher.SectionNine.NineTenNeighborhoodResidualCommutator
public import Stellmacher.SectionNine.NineSevenCentralizerCore
public import Stellmacher.ResidualCommutatorIdempotence
/-!
# The excluded terminal center collapses the residual neighborhood layer

Retain the actual first stabilizer and a supplied good neighbor and center
actor. Let W be its literal distance-two neighborhood, C the commutator
preimage of the first residual modulo first V, and M=[W,O₂(E_first)]C.
If the terminal center of order two is absent from M, the source (9)
displacement bound forces [W,O₂(E_first)] into C.

The subgroup K=(W_lambda∩M)C is normalized by the generating edge and
the supplied center, since its displacement loses the excluded terminal
line. The actual PSet normal-kernel criterion and the retained outside-core
two-actor give [K,E_first]≤C. Residual commutator idempotence improves this
to first V, so maximality puts K in C. The residual core normalizes W_lambda;
hence [W_lambda,Q]≤C. Normal generation of the literal distance-two join
then gives [W,Q]≤C. The geometric containments and support bound are explicit
inputs, all supplied by the earlier results on the same normalized path.

This proves the final excluded-center branch of Stellmacher (9.10), printed
p.59, in the precise form needed by the source (11) and (12) contradiction.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise
universe u

private theorem joined_line_intersection_le
    {G : Type u} [Group G] [Finite G]
    (R Z W : Subgroup G) (hRW : R ≤ W)
    (hRZ : R ≤ Subgroup.normalizer (Z : Set G))
    (hZcard : Nat.card Z = 2) (hZnot : ¬ Z ≤ W) :
    (R ⊔ Z) ⊓ W ≤ R := by
  have hWZ : W ⊓ Z = ⊥ := by
    by_contra hnonzero
    have heq : W ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by
      rw [hZcard]
      exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hnonzero)
    exact hZnot (heq ▸ inf_le_left)
  intro x hx
  have hm : x ∈ (R : Set G) * (Z : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R Z hRZ]
    exact hx.1
  obtain ⟨r, hr, z, hz, rfl⟩ := hm
  have hzW : z ∈ W := by
    simpa only [inv_mul_cancel_left] using W.mul_mem (W.inv_mem (hRW hr)) hx.2
  have hzOne : z = 1 := by
    have hh : z ∈ W ⊓ Z := ⟨hzW, hz⟩
    rwa [hWZ, Subgroup.mem_bot] at hh
  change r ∈ R at hr
  simpa only [hzOne, mul_one] using hr

public theorem nine_ten_excluded_center_residual_le_normal_layer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (lambda mu : ctx.Γ.Vertex)
    (hlambda : lambda ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hjoin : GeneratedNeighborhoodV ctx.Γ lambda ≤
      DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep)
    (hfirst : VAt ctx.Γ ctx.criticalPath.firstStep ≤
      DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep)
    (hgeneration : (GAt ctx.Γ lambda ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) ⊔
      ZAt ctx.Γ mu = GAt ctx.Γ ctx.criticalPath.firstStep)
    (actor : GAt ctx.Γ ctx.criticalPath.firstStep)
    (hactor : (actor:G) ∈ ZAt ctx.Γ mu)
    (hactorNot : (actor:G) ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hactorTwo : IsPGroup 2 (Subgroup.zpowers (actor:G)))
    (R C M : Subgroup G)
    (hCdef : C = Subgroup.commutatorPreimage
      (DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep)
      (EAt ctx.Γ ctx.criticalPath.firstStep) (VAt ctx.Γ ctx.criticalPath.firstStep))
    (hMdef : M = ⁅DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep,
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ⊔ C)
    (hRfirst : R ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hRcenter : R ≤ Subgroup.normalizer (ZAt ctx.Γ ctx.criticalPath.a' : Set G))
    (hbound : ⁅GeneratedNeighborhoodV ctx.Γ lambda,ZAt ctx.Γ mu⁆ ≤
      R ⊔ ZAt ctx.Γ ctx.criticalPath.a')
    (hcenterCard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a') = 2)
    (hcenterNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ M) :
    ⁅DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep,
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤ C := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let W := DistanceTwoNeighborhoodV Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let Q := twoCoreIn E
  let L := GeneratedNeighborhoodV Γ lambda
  let Z := ZAt Γ mu
  let K := (L ⊓ M) ⊔ C
  have hgeometry := nine_ten_distance_two_neighborhood_geometry ctx.toLocalContext hb
  have hWP : W ≤ P := hgeometry.1.trans (by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.stabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _)
  have hWV : W ≤ Subgroup.normalizer (V:Set G) :=
    hgeometry.2.2.1.trans (Subgroup.centralizer_le_normalizer _)
  have hPW : P ≤ Subgroup.normalizer (W:Set G) := hgeometry.2.2.2.1
  have hPV : P ≤ Subgroup.normalizer (V:Set G) := stabilizer_le_normalizer_v Γ cp.firstStep
  have hEeq : E = twoResidualIn P := Γ.twoResidualAt_def cp.firstStep
  have hgen : (GAt Γ lambda ⊓ P) ⊔ Z = P := hgeneration
  have hEP : E ≤ P := hEeq ▸ twoResidualIn_le P
  have hPE : P ≤ Subgroup.normalizer (E:Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp
      (hEeq ▸ twoResidualIn_normal P)
  have hQP : Q ≤ P := (twoCoreIn_le E).trans hEP
  have hPQ : P ≤ Subgroup.normalizer (Q:Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp
      (twoCoreIn_normal_of_normal E P hEP
        (hEeq ▸ twoResidualIn_normal P))
  have hCW : C ≤ W := hCdef ▸ Subgroup.commutatorPreimage_le W E V
  have hCE : ⁅C,E⁆ ≤ V := hCdef ▸ Subgroup.commutator_commutatorPreimage_le W E V hWV
  have hPC : P ≤ Subgroup.normalizer (C:Set G) := hCdef ▸
    Subgroup.commutatorPreimage_normalized W E V P hWV hPW hPE hPV
  have hVC : V ≤ C := by
    rw [hCdef]
    exact Subgroup.le_commutatorPreimage hfirst
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hEP.trans hPV))
  have hCM : C ≤ M := hMdef ▸ le_sup_right
  have hMW : M ≤ W := hMdef ▸ sup_le
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPW)) hCW
  have hPD : P ≤ Subgroup.normalizer ((⁅W,Q⁆ : Subgroup G) : Set G) := by
    intro p hp
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPW hp),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPQ hp)]
  have hPM : P ≤ Subgroup.normalizer (M:Set G) := by
    rw [hMdef]
    exact (le_inf hPD hPC).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hZP : Z ≤ P := hgen ▸ le_sup_right
  have hRint : (R ⊔ ZAt Γ cp.a') ⊓ M ≤ C :=
    (joined_line_intersection_le R (ZAt Γ cp.a') M
      (hRfirst.trans (hVC.trans hCM)) hRcenter hcenterCard hcenterNot).trans
        (hRfirst.trans hVC)
  have hJZ : ⁅L ⊓ M,Z⁆ ≤ C := (le_inf
    ((Subgroup.commutator_mono inf_le_left le_rfl).trans hbound)
    ((Subgroup.commutator_mono inf_le_right le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZP.trans hPM)))).trans hRint
  have hKZ : ⁅K,Z⁆ ≤ C := by
    have hJ : L ⊓ M ≤ Subgroup.commutatorPreimage W Z C :=
      Subgroup.le_commutatorPreimage (inf_le_left.trans hjoin) hJZ
    have hC : C ≤ Subgroup.commutatorPreimage W Z C :=
      Subgroup.le_commutatorPreimage hCW
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZP.trans hPC))
    exact (Subgroup.commutator_mono (sup_le hJ hC) le_rfl).trans
      (Subgroup.commutator_commutatorPreimage_le W Z C (hWP.trans hPC))
  have hPK : P ≤ Subgroup.normalizer (K:Set G) := by
    rw [←hgen]
    apply sup_le
    · have hEL : GAt Γ lambda ⊓ P ≤ Subgroup.normalizer (L:Set G) :=
        inf_le_left.trans (nine_seven_stabilizer_normalizes_neighborhood Γ lambda)
      have hEM : GAt Γ lambda ⊓ P ≤ Subgroup.normalizer (M:Set G) := inf_le_right.trans hPM
      have hEC : GAt Γ lambda ⊓ P ≤ Subgroup.normalizer (C:Set G) := inf_le_right.trans hPC
      exact (le_inf ((le_inf hEL hEM).trans Subgroup.inf_normalizer_le_normalizer_inf)
        hEC).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr (hKZ.trans le_sup_right)
  have hKEC : ⁅K,E⁆ ≤ C := nine_ten_actor_trivial_quotient_residual_commutator_le ctx
    K C le_sup_right hPK hPC actor hactorNot hactorTwo
      ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans hKZ)
  have hKW : K ≤ W := sup_le (inf_le_left.trans hjoin) hCW
  have hKtwo : IsPGroup 2 K := nine_seven_subgroup_isTwoGroup_of_le_vertex_core Γ
    cp.firstStep K (hKW.trans hgeometry.1)
  have hKEV : ⁅K,E⁆ ≤ V := by
    have hidem := commutator_twoResidualAmbient_idempotent K P hKtwo hPK
    have hEeq : E = twoResidualAmbient P := Γ.twoResidualAt_def cp.firstStep
    rw [←hEeq] at hidem
    rw [←hidem]
    exact (Subgroup.commutator_mono hKEC le_rfl).trans hCE
  have hKC : K ≤ C := by
    rw [hCdef]
    exact Subgroup.le_commutatorPreimage hKW hKEV
  have hQlambda : Q ≤ GAt Γ lambda := by
    have hcore : Q ≤ QAt Γ cp.firstStep := by
      change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.twoCoreAt cp.firstStep
      rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
      exact inf_le_right
    exact hcore.trans (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
      cp.firstStep lambda hlambda default).2.2)
  have hLQC : ⁅L,Q⁆ ≤ C := (le_inf
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQlambda.trans (nine_seven_stabilizer_normalizes_neighborhood Γ lambda)))
    (((Subgroup.commutator_mono hjoin le_rfl).trans
      (show ⁅W,Q⁆ ≤ M from hMdef ▸ le_sup_left)))).trans
        ((show L ⊓ M ≤ K from le_sup_left).trans hKC)
  let F := Subgroup.commutatorPreimage W Q C
  have hPF : P ≤ Subgroup.normalizer (F:Set G) :=
    Subgroup.commutatorPreimage_normalized W Q C P (hWP.trans hPC) hPW hPQ hPC
  have hLF : L ≤ F := Subgroup.le_commutatorPreimage hjoin hLQC
  have hWF : W ≤ F := nine_ten_distance_two_le_of_normalized_neighborhood
    ctx.sectionSeven Γ cp.firstStep lambda hlambda F hPF hLF
  exact (Subgroup.commutator_mono hWF le_rfl).trans
    (Subgroup.commutator_commutatorPreimage_le W Q C (hWP.trans hPC))

end Stellmacher.SectionNine
