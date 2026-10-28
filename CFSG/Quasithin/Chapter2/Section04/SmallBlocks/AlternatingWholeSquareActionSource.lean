module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingActionMovementSource
public import Theory.SpecificGroups.SymmetricFourWreath.AmbientSquareActionKernel
/-!
# The full square action in the original single A5 case

The Borel residual and the ambient Sylow subgroup normalize E=P C_T(L).
The residual acts nontrivially because it contains the nonabelian extraspecial
core P. Its two-perfectness forces a cubic in the square-action image. The
original conjugate-module factorization supplies noncommuting images inside
one common two-subgroup. Together these force the full group O4+(2), of
order 72, with the literal normalizer action on E retained in the conclusion.

All model, kernel, movement, and central-factor premises are discharged from
MinimalBlockSetup. Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_whole_square_action
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
    let E := P ⊔ D
    let F := K ⊔ (T : Subgroup G)
    ∃ hD : IsElementaryAbelian 2 D,
    ∃ hp : QuaternionCentralProductData P, ∃ eE : E ≃* P × D,
    ∃ hn : F ≤ normalizer (E : Set G),
      letI := hD
      ((hp.centralFactorWreathAction eE).comp
        (E.normalizerMonoidHom.comp (inclusion hn))).range = ⊤ := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let Di := centralizer (d.block : Set d.H)
  let E := P ⊔ D
  let F := K ⊔ (T : Subgroup G)
  have hDm : Di.map d.H.subtype = D :=
    d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA
  have hDi := (d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA).2.2.1
  let : IsElementaryAbelian 2 Di := hDi
  let : IsElementaryAbelian 2 D := hDm ▸ IsElementaryAbelian.map d.H.subtype
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  obtain ⟨ep,_⟩ := d.single_alternating_core_centralizer_product hG T hM hTM hu hST hsingle hA
  let eE : E ≃* P×D := ep.symm
  obtain ⟨hEF,hFn,_⟩ := d.single_alternating_generated_setup hG T hM hTM hu hST hsingle hA
  refine ⟨inferInstance,hp,eE,hFn,?_⟩
  let a : F →* MulAut E := E.normalizerMonoidHom.comp (inclusion hFn)
  let f := (hp.centralFactorWreathAction eE).comp a
  let fT : T →* BinaryFourPlus.Wreath := f.comp (inclusion le_sup_right)
  have hPR := (d.single_borel_core_placement hsingle).1
  have hRP := (d.single_borel_core_placement hsingle).2
  have hDR : D ≤ R := by
    rw [show D=R⊓centralizer (d.block.map d.H.subtype : Set G) from
      d.single_block_sylow_centralizer T hST.le hsingle]
    exact inf_le_left
  have hRE : R ≤ normalizer (E : Set G) := (hST.le.trans le_sup_right).trans hFn
  obtain ⟨er,her⟩ := d.single_alternating_marked_ambient_sylow_model hG T hM hTM hu hST hsingle hA
  have her' : ((MonoidHom.fst SymmetricFourWreath.P Di).comp er.toMonoidHom).ker = D.subgroupOf R := by
    rw [her,hDm]
  have hker : (fT.comp (inclusion hST.le)).ker=E.subgroupOf R := by
    exact SymmetricFourWreath.ambient_square_action_ker R P D hPR hDR hRP hRE er her' hp eE
  obtain ⟨x,u,hmove⟩ := d.single_alternating_action_movement hG T hM hTM hu hST hsingle hA fT hker
  have hKP : P ≤ K := pCoreIn_le 2 K
  let eK : (K.subgroupOf F) ≃* K := subgroupOfEquivOfLe (show K≤F from le_sup_left)
  let erK : (pResidual 2 B) ≃* K := (pResidual 2 B).equivMapOfInjective B.subtype B.subtype_injective
  let ek := erK.trans eK.symm
  have hK : IsPPerfect 2 (K.subgroupOf F) :=
    (isPPerfect_pResidual (G:=B) 2).of_surjective ek.toMonoidHom ek.surjective
  have hnon : a.comp (K.subgroupOf F).subtype ≠ 1 := by
    intro he
    have hcent : center P=⊤ := by
      apply top_unique
      intro p _
      apply mem_center_iff.mpr
      intro q
      let pk : K.subgroupOf F := ⟨⟨p,mem_sup_left (hKP p.property)⟩,hKP p.property⟩
      let qe : E := ⟨q,mem_sup_left q.property⟩
      have hh := congrArg (fun v : MulAut E => (v qe:G)) (DFunLike.congr_fun he pk)
      change (p:G)*(q:G)*(p:G)⁻¹=(q:G) at hh
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hh := hp.center_card
    rw [hcent,Nat.card_congr (topEquiv : (⊤:Subgroup P) ≃* P).toEquiv,hp.card] at hh
    omega
  let tt : Subgroup F := (T : Subgroup G).subgroupOf F
  have htwo : IsPGroup 2 tt := T.isPGroup'.comap_subtype
  let xx : tt := ⟨⟨x,mem_sup_right x.property⟩,x.property⟩
  let uu : tt := ⟨⟨u,mem_sup_right u.property⟩,u.property⟩
  exact hp.centralFactorWreathAction_range_eq_top eE
    (d.single_alternating_centralizer_card_le_two hG T hM hTM hu hST hsingle hA)
    a (K.subgroupOf F) tt hK htwo hnon xx uu hmove
end CFSG.Quasithin.Chapter2
