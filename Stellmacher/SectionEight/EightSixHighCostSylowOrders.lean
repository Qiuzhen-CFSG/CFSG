module
public import Stellmacher.SectionEight.EightSixHighCostModuleData
public import Stellmacher.SectionEight.EightSixHighCostResidualFixedFree
public import Stellmacher.SectionEight.EightSixHighCostFixedCoreSplitting
public import Theory.GroupTheory.CyclicCenterSplitElementaryEight
public import Theory.GroupAction.RankThreeBinaryFactorOrbitCount
public import Theory.GroupAction.RankThreeBinaryFourFactorCount

/-!
# The Sylow order interval in the actual high-cost configuration

The original selected high-cost local hypotheses of Stellmacher (8.6),
including elementary D, imply 2^14≤|S|≤2^15. Every quotient and action
is constructed from the supplied graph data; no Sylow order, complement,
factor transitivity or classification alternative is assumed.

The literal next-stabilizer action on Vnext/Znext has kernel Qnext,
which is extraspecial of order512. Its Sylow image T has a normal
elementary-eight actor A. Initial-side coprime decomposition and the
proved fixed-core splitting produce a complement to A in T. The actual
quotient S/Qnext has cyclic center, so the generic split-eight theorem
bounds |T| by64. For the lower bound, the three compatible conjugation
actions give a transitive orbit of four active coatom fixed factors.
Since A is abelian it lies in the stabilizer of every coatom; therefore
orbit-stabilizer gives |T|≥4*8. Multiplication by the exact kernel order
proves both required bounds.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6)(c), printed p.41,
and the factor argument following (21), printed p.45. This supplies exactly
the numerical Sylow field of the existing public case-C alternative.
-/
namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise IsMulCommutative
universe u
private theorem conjugation_action_data
    {X : Type*} [Group X] [Finite X]
    (A F T : Subgroup X)
    (hAF : A ≤ Subgroup.normalizer (F : Set X))
    (hTA : T ≤ Subgroup.normalizer (A : Set X))
    (hTF : T ≤ Subgroup.normalizer (F : Set X))
    (hfaith : A ⊓ Subgroup.centralizer (F : Set X) = ⊥)
    (hfull : F ⊓ Subgroup.centralizer (A : Set X) = ⊥)
    (hfixed : ∀ a : A, a ≠ 1 → Nat.card
      (F ⊓ Subgroup.centralizer (Subgroup.zpowers (a:X) : Set X) : Subgroup X) ≤ 9)
    (hirred : IsIrreducibleSection T ⊥ F) :
    let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer A F hAF
    let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T A hTA
    let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T F hTF
    FaithfulSMul A F ∧
    FixedPoints.subgroup (⊤ : Subgroup A) F = ⊥ ∧
    (∀ a : A, a ≠ 1 → Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) F) ≤ 9) ∧
    (∀ H : Subgroup F, IsInvariant T F H → H = ⊥ ∨ H = ⊤) ∧
    (∀ t : T, ∀ a : A, ∀ x : F, t • (a • x) = (t • a) • (t • x)) := by
  classical
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer A F hAF
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T A hTA
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T F hTF
  have hfaithful : FaithfulSMul A F := faithfulSMul_iff.mpr (by
    intro a ha
    have hcent : (a:X) ∈ Subgroup.centralizer (F : Set X) := by
      intro f hf
      have hh := congrArg Subtype.val (ha (⟨f,hf⟩:F))
      change (a:X)*f*(a:X)⁻¹=f at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact Subtype.ext (show (a:X)=1 from
      (show (a:X) ∈ (⊥ : Subgroup X) from hfaith ▸ ⟨a.property,hcent⟩)))
  refine ⟨hfaithful,?_,?_,?_,?_⟩
  · apply bot_unique
    intro f hf
    have hcent : (f:X) ∈ Subgroup.centralizer (A : Set X) := by
      intro a ha
      have hh := congrArg Subtype.val (hf (⟨⟨a,ha⟩,Subgroup.mem_top _⟩ : (⊤ : Subgroup A)))
      change a*(f:X)*a⁻¹=(f:X) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    exact Subtype.ext (show (f:X)=1 from
      (show (f:X) ∈ (⊥ : Subgroup X) from hfull ▸ ⟨f.property,hcent⟩))
  · intro a ha
    let J := FixedPoints.subgroup (Subgroup.zpowers a) F
    let C := F ⊓ Subgroup.centralizer (Subgroup.zpowers (a:X) : Set X)
    have hcent (x : J) : ((x:F):X) ∈ C := by
      refine ⟨(x:F).property,?_⟩
      rw [Subgroup.zpowers_eq_closure,Subgroup.centralizer_closure]
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val (x.property ⟨a,Subgroup.mem_zpowers a⟩)
      change (a:X)*((x:F):X)*(a:X)⁻¹=((x:F):X) at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    let inclusion : J → C := fun x => ⟨((x:F):X),hcent x⟩
    have hinj : Function.Injective inclusion := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : C => (z:X)) hxy
    exact (Nat.card_le_card_of_injective inclusion hinj).trans (hfixed a ha)
  · intro H hH
    let _ := hH
    have hinv : IsConjugateInvariantBy (H.map F.subtype) T := by
      intro t x hx
      obtain ⟨f,hf,rfl⟩ := hx
      exact ⟨t • f,(IsInvariant.invariant t f).mp hf,rfl⟩
    rcases hirred.2.2 (H.map F.subtype) bot_le (Subgroup.map_subtype_le H) hinv with hb | ht
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective H F.subtype_injective).mp hb
    · right
      apply Subgroup.map_injective F.subtype_injective
      rw [ht,←MonoidHom.range_eq_map,Subgroup.range_subtype]
  · intro t a x
    apply Subtype.ext
    change (t:X)*((a:X)*(x:X)*(a:X)⁻¹)*(t:X)⁻¹ =
      ((t:X)*(a:X)*(t:X)⁻¹)*((t:X)*(x:X)*(t:X)⁻¹)*((t:X)*(a:X)*(t:X)⁻¹)⁻¹
    group

public theorem eight_six_high_cost_sylow_card_bounds
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
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    : 2 ^ 14 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 15 := by
  classical
  obtain ⟨hN,hW,action,hformula,hkernel,hF⟩ := eight_six_high_cost_residual_module_data
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hhigh helementary
  let _ := hN
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let Abar := ((VAt Γ previous ⊓ QAt Γ cp.a).subgroupOf P).map action
  let F := ((twoResidualIn P).subgroupOf P).map action
  let T := (S.subgroupOf P).map action
  have hAdata := eight_six_high_cost_actor_image_data ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hFdata := eight_six_high_cost_residual_irreducible_fixed_free ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hfaith := eight_six_high_cost_actor_residual_centralizer_trivial ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hTA : T ≤ Subgroup.normalizer (Abar : Set (MulAut W)) :=
    (eight_six_actor_image_eq_core_and_normalized ctx hlength previous D L Q hD hL hQ
      data action hkernel.ge).2.1
  let _ : ((twoResidualIn P).subgroupOf P).Normal := twoResidualIn_normal P
  have hAF : Abar ≤ Subgroup.normalizer (F : Set (MulAut W)) :=
    (Subgroup.map_mono (show (VAt Γ previous ⊓ QAt Γ cp.a).subgroupOf P ≤
      Subgroup.normalizer ((twoResidualIn P).subgroupOf P : Set P) from
        Subgroup.le_normalizer_of_normal)).trans (Subgroup.le_normalizer_map action)
  have hTF : T ≤ Subgroup.normalizer (F : Set (MulAut W)) :=
    (Subgroup.map_mono (show S.subgroupOf P ≤
      Subgroup.normalizer ((twoResidualIn P).subgroupOf P : Set P) from
        Subgroup.le_normalizer_of_normal)).trans (Subgroup.le_normalizer_map action)
  have hTtwo : IsPGroup 2 T := by
    obtain ⟨hSP,sylow,hsylow⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
    have hSnative : (sylow : Subgroup P) = S.subgroupOf P := by
      apply Subgroup.map_injective P.subtype_injective
      rw [hsylow,Subgroup.map_subgroupOf_eq_of_le hSP]
    change IsPGroup 2 ((S.subgroupOf P).map action)
    rw [←hSnative]
    exact sylow.isPGroup'.map action
  have hSP : S ≤ P := (edge_sylow_data ctx.sectionSeven Γ cp).2.1
  let R := QAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  have hAS : A ≤ S := inf_le_right.trans
    (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hAbarT : Abar ≤ T := Subgroup.map_mono (Subgroup.subgroupOf_mono P hAS)
  let projection : S →* T := (action.comp (Subgroup.inclusion hSP)).codRestrict T
    (fun s => ⟨Subgroup.inclusion hSP s,s.property,rfl⟩)
  have hsurj : Function.Surjective projection := by
    intro t
    obtain ⟨s,hs,hst⟩ := t.property
    exact ⟨⟨s,hs⟩,Subtype.ext hst⟩
  have hRnative : R.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hker : projection.ker = R.subgroupOf S := by
    ext s
    change projection s = 1 ↔ (s:G) ∈ R
    rw [Subtype.ext_iff]
    change action (Subgroup.inclusion hSP s) = 1 ↔ (s:G) ∈ R
    change Subgroup.inclusion hSP s ∈ action.ker ↔ (s:G) ∈ R
    rw [hkernel,←hRnative]
    rfl
  have hRcard : Nat.card R = 512 := (eight_six_high_cost_next_core_extraspecial
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
    hD hL ha hout hlarge hmin hQ hhigh helementary).2
  have hScard : Nat.card S = 512 * Nat.card T := by
    have hh := projection.ker.card_mul_index
    rw [Subgroup.index_ker,hker] at hh
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2).toEquiv,hRcard] at hh
    rw [projection.range_eq_top_of_surjective hsurj,Subgroup.card_top] at hh
    exact hh.symm
  let Ainside := Abar.subgroupOf T
  have hAinside : (A.subgroupOf S).map projection = Ainside := by
    ext a
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨Subgroup.inclusion hSP s,hs,rfl⟩
    · intro ha
      obtain ⟨p,hp,hpa⟩ := ha
      exact ⟨⟨p,hAS hp⟩,hp,Subtype.ext hpa⟩
  let _ : IsElementaryAbelian 2 Abar := hAdata.1
  let _ : IsElementaryAbelian 2 Ainside :=
    IsElementaryAbelian.subgroupOf hAbarT
  have hAinsideCard : Nat.card Ainside = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAbarT).toEquiv).trans hAdata.2.1
  let _ : Ainside.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTA
  have hTupper : Nat.card T ≤ 64 := by
    let cubicSylow : Sylow 3 (GAt Γ cp.a) := Classical.choice inferInstance
    let cubic : Subgroup G := (cubicSylow : Subgroup (GAt Γ cp.a)).map (GAt Γ cp.a).subtype
    have hcubic : IsSylowIn 3 cubic (GAt Γ cp.a) := ⟨cubicSylow,rfl⟩
    let C := QAt Γ cp.a ⊓ Subgroup.centralizer (cubic : Set G)
    let Cbar := (C.subgroupOf S).map projection
    have hfixed : Q ⊓ Subgroup.centralizer (cubic : Set G) ≤ D :=
      le_sup_left.trans (eight_six_high_cost_fixed_core_splitting ctx hcenter hquot hlength
        hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
        hQ hhigh helementary cubic hcubic).1.ge
    have hjoin : Ainside ⊔ Cbar = ⊤ := by
      rw [←hAinside,sup_comm,←eight_six_initial_core_barred_decomposition ctx.sectionSeven Γ cp
        hlength previous D L Q cubic hD hL hQ hcubic data projection hker]
      exact eight_six_initial_core_barred_image_top_local ctx hcard hlength projection hsurj hker
    have hinter : Ainside ⊓ Cbar = ⊥ := by
      rw [←hAinside,inf_comm]
      exact eight_six_barred_intersection_of_fixed_core ctx.sectionSeven Γ cp previous D L Q cubic
        hprev.1 hD hL hQ data hfixed projection hker
    let _ : IsCyclic (Subgroup.center T) :=
      eight_six_first_core_quotient_center_isCyclic ctx.sectionSeven Γ cp projection hsurj hker
    exact card_le_sixtyfour_of_cyclic_center_split_elementary_eight
      hTtwo Ainside Cbar hAinsideCard hjoin hinter
  let _ : IsElementaryAbelian 3 F := hF
  let _ : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).mpr hFdata.1.2.1.symm
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer Abar F hAF
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T Abar hTA
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T F hTF
  have hconj := conjugation_action_data Abar F T hAF hTA hTF hfaith hFdata.2
    hAdata.2.2 hFdata.1
  let _ : FaithfulSMul Abar F := hconj.1
  have hcount := rank_three_binary_fixed_factor_count_is_two_power
    hAdata.2.1 hTtwo hconj.2.2.2.2 hconj.2.1 hconj.2.2.2.1
  have hfour := rank_three_binary_fixed_factor_count_eq_four
    hAdata.2.1 hconj.2.2.1 hconj.2.1 hcount
  obtain ⟨K,_hKindex,_hKactive,hactive⟩ := rank_three_binary_fixed_factors_single_orbit
    hAdata.2.1 hconj.2.2.2.2 hconj.2.1 hconj.2.2.2.1
  have horbit : Nat.card (MulAction.orbit T K) = 4 :=
    (Nat.card_congr (Equiv.setCongr hactive)).symm.trans hfour
  have hAstab : Ainside ≤ MulAction.stabilizer T K := by
    intro a ha
    apply MulAction.mem_stabilizer_iff.mpr
    change K.map (MulDistribMulAction.toMulAut T Abar a).toMonoidHom = K
    have htrivial : (MulDistribMulAction.toMulAut T Abar a).toMonoidHom = MonoidHom.id Abar := by
      apply MonoidHom.ext
      intro b
      apply Subtype.ext
      change (a:MulAut W)*(b:MulAut W)*(a:MulAut W)⁻¹=(b:MulAut W)
      have hc := congrArg Subtype.val (mul_comm (⟨a,ha⟩:Abar) b)
      change (a:MulAut W)*(b:MulAut W)=(b:MulAut W)*(a:MulAut W) at hc
      rw [hc,mul_inv_cancel_right]
    rw [htrivial,Subgroup.map_id]
  have hTlower : 32 ≤ Nat.card T := by
    have hstab := Subgroup.card_le_of_le hAstab
    rw [hAinsideCard] at hstab
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup T K)
    rw [Nat.card_prod,horbit] at hh
    omega
  rw [hScard]
  constructor <;> norm_num <;> omega
end Stellmacher.SectionEight
