module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Image
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The source Sylow subgroup and its trivial multiplicity action

Centerlessness of the marked SL₂ quotient identifies the kernel on K/O₂(K)
inside KT with O₂(KT). Its intersection with T is exactly R₁. Restriction
of the given Sylow subgroup to the normal quotient-centralizer then proves
that R₁ is Sylow in C.

The source splitting of T_L, together with the preceding equality of the
images of W and R₁ modulo O₂(LT), puts R₁ in W C_G(L). Both factors act
trivially on W/V₁. Thus odd order is a conclusion of the Sylow-kernel
calculation. No equality W=T∩L is used.

Source: Aschbacher--Smith, 11.5.7, printed p.782.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup
open scoped Pointwise commutatorElement
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

private theorem radical_le_sylow : E.R₁ ≤ (T : Subgroup G) := by
  simpa only [Geometry.R₁, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

/-- The actual centralizer identity, with no assumed Sylow or odd-order conclusion. -/
theorem radical_eq_sylow_inf_coreCentralizer (m : NaturalPair E)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hKL : E.K = E.L₁) :
    E.R₁ = (T : Subgroup G) ⊓ coreQuotientCentralizer E.K := by
  have hn : (T : Subgroup G) ≤ normalizer (E.K : Set G) :=
    hTG.trans E.G₁_normalizes_K
  have hz : center (E.K ⧸ pCore 2 E.K) = ⊥ := by
    apply (center _).eq_bot_iff_forall.mpr
    intro z hz
    apply m.actor.injective
    rw [map_one]
    apply mem_bot.mp
    rw [← Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot]
    apply mem_center_iff.mpr
    intro a
    obtain ⟨b,rfl⟩ := m.actor.surjective a
    simpa only [map_mul] using congrArg m.actor (mem_center_iff.mp hz b)
  have hk := pCoreJoinAction_kernel 2 hn T.isPGroup' hz
  have hR : E.R₁ = (E.K ⊔ (T : Subgroup G)).pCoreIn 2 := by rw [hKL]; rfl
  apply le_antisymm
  · refine le_inf (radical_le_sylow E) ?_
    rw [hR]
    rintro _ ⟨r,hr,rfl⟩
    refine ⟨inclusion (sup_le E.K.le_normalizer hn) r, ?_, rfl⟩
    exact hk.ge hr
  · rintro t ⟨ht,c,hc,hct⟩
    rw [hR]
    let t' : (E.K ⊔ (T : Subgroup G) : Subgroup G) := ⟨t,mem_sup_right ht⟩
    refine ⟨t',hk.le ?_,rfl⟩
    change coreQuotientAction E.K (inclusion (sup_le E.K.le_normalizer hn) t') = 1
    have he : inclusion (sup_le E.K.le_normalizer hn) t' = c := Subtype.ext hct.symm
    rw [he]
    exact hc

/-- All three generators of C centralize the same original core quotient. -/
theorem C_le_coreCentralizer (m : NaturalPair E)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hKL : E.K = E.L₁)
    (hres : outsideResidual E ≤ E.Y) : C E ≤ coreQuotientCentralizer E.K := by
  apply sup_le (sup_le ?_ (hres.trans inf_le_right)) inf_le_right
  rw [radical_eq_sylow_inf_coreCentralizer E m hTG hKL]
  exact inf_le_right

/-- The original R₁ is the image of a Sylow subgroup of the literal C. -/
theorem exists_radical_sylow (m : NaturalPair E)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hKL : E.K = E.L₁)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hres : outsideResidual E ≤ E.Y) :
    ∃ S : Sylow 2 (C E), (S : Subgroup (C E)) = E.R₁.subgroupOf (C E) := by
  let B := (coreQuotientCentralizer E.K).subgroupOf E.G₁
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (E.G₁_normalizes_K.trans (normalizer_normalizes_coreQuotientCentralizer E.K))
  obtain ⟨S,hS⟩ := (T.subtype hTG).exists_subgroupOf_eq_of_normal B
  have hCG := C_le_point_normalizer E hTG hHG hXG
  have hCB := C_le_coreCentralizer E m hTG hKL hres
  let f : C E →* B := ((inclusion hCG).codRestrict B (fun a => hCB a.property))
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : B => (x.val : G)) hab)
  have hSf : (S : Subgroup B) ≤ f.range := by
    intro b hb
    have hbT : (b.val : G) ∈ T := hS.le hb
    have hbR : (b.val : G) ∈ E.R₁ := by
      rw [radical_eq_sylow_inf_coreCentralizer E m hTG hKL]
      exact ⟨hbT,b.property⟩
    refine ⟨⟨b.val,mem_sup_left (mem_sup_left hbR)⟩,?_⟩
    rfl
  refine ⟨S.comapOfInjective f hf hSf,?_⟩
  ext a
  change f a ∈ (S : Subgroup B) ↔ (a : G) ∈ E.R₁
  rw [hS, radical_eq_sylow_inf_coreCentralizer E m hTG hKL]
  exact (and_iff_left (hCB a.property)).symm

omit [Finite G] in
include D in
/-- The splitting of T_L restricts to its two-core, with the true intersection
O₂(LT)∩L=O₂(L). -/
theorem ambient_core_le_seed_join_centralizer
    (hLV : L.pCoreIn 2 = V)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ V ⊔ centralizer (L : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let B := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hLB : L ≤ normalizer (B : Set G) :=
    (le_centralizer_iff.mp (show B ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hBQ : B ≤ Q := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le inf_le_left) (inf_le_left.trans le_sup_right) (sup_le hLB hTB)
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  intro q hq
  have hqTL : q ∈ LocalGeometry.sourceTL T L := ⟨hQT hq,mem_sup_right hq⟩
  rw [hsplit] at hqTL
  have hprod : q ∈ (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) * (B : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ (inf_le_right.trans hLB)]
    exact hqTL
  obtain ⟨a,ha,b,hb,rfl⟩ := hprod
  have haQ : a ∈ Q := by
    simpa only [mul_inv_cancel_right] using Q.mul_mem hq (Q.inv_mem (hBQ hb))
  have haV : a ∈ V := hLV ▸ inf_pCoreIn_le_of_le 2
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) ⟨ha.2,haQ⟩
  exact mul_mem_sup haV hb.2

/-- The preceding equality R̄₁=W̄ modulo O₂(LT), followed by the block
splitting, is enough; the false equality W=T∩L is unnecessary. -/
theorem radical_le_closure_join_centralizer
    (hLV : L.pCoreIn 2 = V)
    (himage : E.R₁ ≤ E.W ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    E.R₁ ≤ E.W ⊔ centralizer (L : Set G) :=
  himage.trans (sup_le le_sup_left ((ambient_core_le_seed_join_centralizer (D := D) hLV hsplit).trans
    (sup_le ((le_conjugateSpanBy V E.G₁).trans le_sup_left) le_sup_right)))

/-- Block splitting places the actual Sylow radical in the literal action kernel. -/
theorem radical_le_actionCentralizer (m : NaturalPair E)
    (hCG : C E ≤ E.G₁) (hWK : E.W = E.K.pCoreIn 2) (hWL : E.W ≤ L)
    (hLV : L.pCoreIn 2 = V)
    (himage : E.R₁ ≤ E.W ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    E.R₁.subgroupOf (C E) ≤ actionCentralizer E (C E) hCG := by
  have hWW : ⁅E.W,E.W⁆ ≤ E.V₁ := by
    apply commutator_le.mpr
    intro w hw u hu
    rw [hWK] at hw
    obtain ⟨k,hk,rfl⟩ := hw
    exact (mem_actionCentralizer_iff E E.K E.K_le_G₁ k).mp
      (m.core_action_eq_one k hk) u hu
  let N := (actionCentralizer E E.G₁ le_rfl).map E.G₁.subtype
  have hWN : E.W ≤ N := by
    intro w hw
    refine ⟨⟨w,closure_le_point_normalizer E hw⟩,?_,rfl⟩
    apply (mem_actionCentralizer_iff E E.G₁ le_rfl _).mpr
    intro u hu
    exact hWW (commutator_mem_commutator hw hu)
  have hCN : centralizer (L : Set G) ≤ N := by
    intro c hc
    have hcG : c ∈ E.G₁ :=
      (centralizer_le (E.V₁_le.trans (le_conjugateSpanBy V E.G₁ |>.trans hWL))).trans
        (Subgroup.centralizer_le_normalizer _) hc
    refine ⟨⟨c,hcG⟩,?_,rfl⟩
    apply (mem_actionCentralizer_iff E E.G₁ le_rfl _).mpr
    intro w hw
    have he : ⁅c,w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_iff.mp hc w (hWL hw)).symm
    rw [he]
    exact E.V₁.one_mem
  have hRN : E.R₁ ≤ N :=
    (radical_le_closure_join_centralizer E hLV himage hsplit).trans (sup_le hWN hCN)
  intro r hr
  obtain ⟨s,hs,hsr⟩ := hRN hr
  apply MonoidHom.mem_ker.mpr
  rw [quotientAction_restrict E (C E) hCG]
  change quotientAction E E.G₁ le_rfl (inclusion hCG r) = 1
  have he : inclusion hCG r = s := Subtype.ext hsr.symm
  rw [he]
  exact hs

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
