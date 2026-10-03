module
public import Stellmacher.SectionEight.EightSixHighCostModuleData
public import Stellmacher.SectionEight.EightSixHighCostResidualFixedFree
public import Theory.GroupAction.RankThreeBinaryFactorOrbitCount
public import Theory.GroupAction.RankThreeBinaryFourFactorCard
/-!
# Four factors in the actual high-cost residual quotient

The original selected high-cost configuration, with elementary D from
common structure, has E_next/O₂(E_next) elementary cubic of rank four.
Every group, action and quotient witness here is constructed from the
literal graph data; no actor rank or factor-transitivity input is assumed.

Use the supplied next-stabilizer action on Vnext/Znext with exact two-core
kernel. Its actual actor image A is elementary of order eight; its full
residual image F is elementary cubic. The preceding native results prove
faithfulness, whole-actor fixed freedom and Sylow irreducibility of F.
Equation-one generation makes A Sylow normalized. The three compatible
conjugation actions retain those exact subgroup and normalization witnesses.
The generic factor-orbit theorem gives a two-power number of independent
coatom fixed factors; the fixed-cardinality bounds force exactly four and
hence order81. Restricting the same action to E_next identifies its kernel
with O₂(E_next), giving the public quotient-rank statement.

This completes the numerical residual assertion in Stellmacher (8.6)(21),
printed p.45. The separate quotient-action clauses of case (c3) are not
premises of this proof.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
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

public theorem eight_six_high_cost_residual_quotient_rank_four
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
 :
    QuotientElementaryAbelian
      (EAt ctx.Γ ctx.criticalPath.firstStep)
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) 3 4 := by
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
  let _ : IsElementaryAbelian 2 Abar := hAdata.1
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
  have hFcard : Nat.card F = 81 := rank_three_binary_fixed_factor_card
    hAdata.2.1 hconj.2.2.1 hconj.2.1 hcount
  let R := EAt Γ cp.firstStep
  have hR : R = twoResidualIn P := Γ.twoResidualAt_def _
  have hRP : R ≤ P := hR ▸ SevenSix.twoResidualIn_le P
  let f : R →* MulAut W := action.comp (Subgroup.inclusion hRP)
  have hrange : f.range = ((twoResidualIn P).subgroupOf P).map action := by
    rw [MonoidHom.range_comp,Subgroup.inclusion_range,hR]
  have hF' : IsElementaryAbelian 3 f.range := hrange.symm ▸ hF
  have hcore : twoCoreIn R = R ⊓ QAt Γ cp.firstStep := by
    rw [hR,SevenSix.residual_core_eq_inter_core]
    rw [show QAt Γ cp.firstStep = twoCoreIn P from Γ.twoCoreAt_def _]
  have hnative : (QAt Γ cp.firstStep).subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hker : f.rangeRestrict.ker = (twoCoreIn R).subgroupOf R := by
    rw [MonoidHom.ker_rangeRestrict,←MonoidHom.comap_ker,hkernel,←hnative,hcore]
    ext r
    change (r:G) ∈ QAt Γ cp.firstStep ↔ (r:G) ∈ R ⊓ QAt Γ cp.firstStep
    exact ⟨fun hr => ⟨r.property,hr⟩, fun hr => hr.2⟩
  exact ⟨{ X := f.range
           projection := f.rangeRestrict
           surjective := f.rangeRestrict_surjective
           kernel_eq := hker }, ⟨hF', by
             change Nat.card f.range = 3 ^ 4
             rw [hrange]
             exact hFcard.trans (by decide)⟩⟩
end Stellmacher.SectionEight

