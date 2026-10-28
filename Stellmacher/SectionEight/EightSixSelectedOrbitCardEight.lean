module
public import Stellmacher.SectionEight.EightSixSelectedOrbitFirstCommutator

/-!
# The selected orbit subgroup has order eight

The actual selected subgroup V1=⟨Za^E⟩ in the large-index branch of (8.6)
has order eight. All local hypotheses and selected witnesses of the proved
first-commutator span are retained; no abstract replacement for V1 is used.

The geometric generation E=A∨A^x and [V1,A]≤Za imply that Za∨Za^x is
E-invariant, hence equal to V1. Both seed groups have order four and share
the next center line of order two. The local identity [Vnext,Qnext]=Znext
makes the two factors normalize each other, so the subgroup-product formula
bounds |V1| by eight. If |V1|=4, E normalizes Za; adjoining the edge would
make the next stabilizer normalize a neighboring center, contradicting the
critical-path normalizer theorem. Divisibility forces |V1|=8.

Source: Stellmacher, Journal of Algebra 190 (1997), Lemma (8.6), printed
p.43, cardinality conclusion of assertion (12). The subsequent containment
in [Qnext,O²(E)] is a separate local transfer.

The companion elementary-abelian conclusion uses only V1≤Qa: Za centralizes
Qa, so the entire E-orbit closure centralizes itself. Its generators are
conjugates of involutions, and hence the abelian closure has exponent two.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_selected_orbit_card_eight
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
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a)) :
    Nat.card (conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E) = 8 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let B := ZAt Γ cp.a
  let Z := ZAt Γ cp.firstStep
  let U := conjugateClosure B E
  let C := B.conjBy geom.x
  have hseed : B ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hUN : E ≤ Subgroup.normalizer (U : Set G) :=
    eight_six_conjugate_closure_normalizer _ _
  have hx : geom.x ∈ E := SevenSix.twoResidualIn_le E geom.residual_mem
  have hUx : U.map (MulAut.conj geom.x).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUN hx)
  have hconjSeed : C ≤ U := by
    have hh := Subgroup.map_mono (f := (MulAut.conj geom.x).toMonoidHom) hseed
    rw [hUx] at hh
    exact hh
  have hcomm : ⁅U,A⁆ ≤ B := le_sup_left.trans_eq
    (eight_six_selected_orbit_commutator_sup_line ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL)
  have hcommConj : ⁅U,A.conjBy geom.x⁆ ≤ C := by
    have hh := Subgroup.map_mono (f := (MulAut.conj geom.x).toMonoidHom) hcomm
    rw [Subgroup.map_commutator,hUx] at hh
    exact hh
  have hjoinU : B ⊔ C ≤ U := sup_le hseed hconjSeed
  have hEN : E ≤ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := by
    rw [geom.generated]
    apply sup_le
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
        ((Subgroup.commutator_mono hjoinU le_rfl).trans (hcomm.trans le_sup_left))
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
        ((Subgroup.commutator_mono hjoinU le_rfl).trans (hcommConj.trans le_sup_right))
  have hUeq : U = B ⊔ C := le_antisymm
    (eight_six_conjugate_closure_le B E (B ⊔ C) le_sup_left hEN) hjoinU
  have hZdata := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hZB : Z ≤ B := hZdata.2
  have hZx : Z.map (MulAut.conj geom.x).toMonoidHom = Z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (stabilizer_le_normalizer_z Γ cp.firstStep (geom.group_le hx))
  have hZC : Z ≤ C := by
    have hh := Subgroup.map_mono (f := (MulAut.conj geom.x).toMonoidHom) hZB
    rw [hZx] at hh
    exact hh
  have hUV : U ≤ VAt Γ cp.firstStep := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨e,z,rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (stabilizer_le_normalizer_v Γ cp.firstStep (geom.group_le e.property)) z).mp
        ((lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 z.property)
  have hUQ : U ≤ QAt Γ cp.firstStep := hUV.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) _)
  have hUU : ⁅U,U⁆ ≤ Z := (Subgroup.commutator_mono hUV hUQ).trans_eq data.first_commutator
  have hCN : C ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hseed hconjSeed).trans (hUU.trans hZB))
  have hcardC : Nat.card C = 4 := by
    change Nat.card (B.map (MulAut.conj geom.x).toMonoidHom) = 4
    rw [Subgroup.card_map_of_injective (MulAut.conj geom.x).injective]
    exact hcard
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes B C hCN
  have hcardB : Nat.card B = 4 := hcard
  have hcardZ : Nat.card Z = 2 := hZdata.1
  have hinf : 2 ≤ Nat.card (B ⊓ C : Subgroup G) := by
    simpa only [hcardZ] using Subgroup.card_le_of_le (le_inf hZB hZC)
  have hbound : Nat.card U ≤ 8 := by
    rw [hcardB,hcardC,←hUeq] at hprod
    nlinarith
  have hmore : 4 < Nat.card U := by
    have hb := Subgroup.card_le_of_le hseed
    rw [hcardB] at hb
    by_contra hn
    have heq : B = U := Subgroup.eq_of_le_of_card_ge hseed (by omega)
    have hEB : E ≤ Subgroup.normalizer (B : Set G) := heq ▸ hUN
    apply neighbor_center_not_normalized ctx.sectionSeven Γ cp.firstStep cp.a
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    change GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (B : Set G)
    rw [←hedge]
    exact sup_le hEB (inf_le_left.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hdvd : 4 ∣ Nat.card U := hcardB ▸ Subgroup.card_dvd_of_le hseed
  obtain ⟨k,hk⟩ := hdvd
  change Nat.card U = 8
  omega

public theorem eight_six_selected_orbit_elementary
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2) (E : Subgroup G)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a) :
    IsElementaryAbelian 2 (conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E) := by
  let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
  have hfirst : ctx.criticalPath.firstStep ∈ Neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hfirst
  have hseed : ZAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.centralizer (U : Set G) :=
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _ hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))).trans (Subgroup.centralizer_le hcore)
  have hCN : Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (U : Set G))).mp inferInstance
  have hUC : U ≤ Subgroup.centralizer (U : Set G) :=
    eight_six_conjugate_closure_le _ _ _ hseed
      ((eight_six_conjugate_closure_normalizer _ _).trans hCN)
  let _ : IsMulCommutative U := Subgroup.le_centralizer_iff_isMulCommutative.mp hUC
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  rintro ⟨x,hx⟩
  apply Subtype.ext
  change x ^ 2 = 1
  change x ∈ Subgroup.closure _ at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨e,z,rfl⟩ := hx
    have hz : (z : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ z.property
    simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj (e : G)) hz
  | one => simp
  | mul x y hx hy hix hiy =>
    have hc : Commute x y := Subgroup.mem_centralizer_iff.mp (hUC hy) x hx
    rw [hc.mul_pow,hix,hiy,one_mul]
  | inv x hx hix => rw [inv_pow,hix,inv_one]


end Stellmacher.SectionEight
