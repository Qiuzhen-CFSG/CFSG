module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Definitions
public import Theory.GroupTheory.InvolutionSylowBound

/-!
# The faithful second-centralizer action and the Sylow deduction

The subgroup C_{C_G(u)}(Lᵤ) normalizes L_B because it centralizes the
cyclic subgroup B. If Lᵤ and L_B generate G, this conjugation action is
faithful: its kernel centralizes both generators and therefore lies in Z(G).
The fixed-centralizer automorphism lemma then identifies the actor with
⟨u⟩. The normalizer condition promotes ⟨u⟩ to a Sylow subgroup of C_G(Lᵤ),
and Sylow divisibility bounds every two-subgroup of that centralizer.

Generation and the intrinsic automorphism rigidity remain explicit inputs.
Source: GLS, volume 4, Chapter 2, Lemma 13.3; Chapter 4, 3.4(d1).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

omit [Finite G] in
/-- The distinguished closure lies in the literal centralizer of the cyclic group. -/
public theorem distinguishedCentralizer_le (B : Subgroup G) :
    distinguishedCentralizer Z B ≤ centralizer (B : Set G) :=
  (closure_le _).mpr (fun _ hx => hx.2)

omit [Finite G] in
/-- Conjugacy invariance of Z gives relative normality in the ambient centralizer. -/
public theorem distinguishedCentralizer_normalizes
    (h : IsProductDisconnected Z M) (B : Subgroup G) :
    centralizer (B : Set G) ≤ normalizer (distinguishedCentralizer Z B : Set G) := by
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨h.invariant g x hx.1,
    (centralizer (B : Set G)).mul_mem
      ((centralizer (B : Set G)).mul_mem hg hx.2)
      ((centralizer (B : Set G)).inv_mem hg)⟩

/-- The source actor C_{C_G(u)}(Lᵤ). -/
@[expose] public def centralizerActor (Z : Set G) (u : G) : Subgroup G :=
  centralizer ({u} : Set G) ⊓ centralizer (centralizerClosure Z u : Set G)

omit [Finite G] in
/-- The source actor acts on the second distinguished centralizer. -/
public theorem centralizerActor_normalizes
    (h : IsProductDisconnected Z M) (d : SecondCentralizerData Z M z t u n) :
    centralizerActor Z u ≤ normalizer (distinguishedCentralizer Z d.torus : Set G) :=
  inf_le_right.trans ((centralizer_le d.torus_le_local).trans
    (distinguishedCentralizer_normalizes h d.torus))

/-- The actual conjugation homomorphism on L_B. -/
@[expose] public def secondCentralizerAction
    (h : IsProductDisconnected Z M) (d : SecondCentralizerData Z M z t u n) :
    centralizerActor Z u →* MulAut (distinguishedCentralizer Z d.torus) :=
  (distinguishedCentralizer Z d.torus).normalizerMonoidHom.comp
    (inclusion (centralizerActor_normalizes h d))

-- The older Selection module has this elementary lemma, but its Pair import
-- conflicts with the current Generation.Basic declaration path. Keep the
-- short proof local rather than changing that shared import boundary.
private theorem ambient_center_eq_bot
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) : center G = ⊥ := by
  rcases r.simple.eq_bot_or_eq_top_of_normal (center G) inferInstance with hc | hc
  · exact hc
  · obtain ⟨w, hw, hwM⟩ := h.disconnected.nonempty
    have hwC : w ∈ center G := hc ▸ mem_top w
    have htop : (⊤ : Subgroup G) ≤ M := by
      intro x _
      exact h.disconnected.centralizer_le hw hwM
        (mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hwC x))
    exact False.elim (h.disconnected.proper (top_le_iff.mp htop))

/-- Generation by Lᵤ and L_B makes the source centralizer action faithful. -/
public theorem secondCentralizerAction_injective
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : SecondCentralizerData Z M z t u n)
    (hgen : centralizerClosure Z u ⊔ distinguishedCentralizer Z d.torus = ⊤) :
    Function.Injective (secondCentralizerAction h.disconnected d) := by
  apply (secondCentralizerAction h.disconnected d).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro b hb
  have hbK : (b : G) ∈ centralizer (distinguishedCentralizer Z d.torus : Set G) := by
    have hk : inclusion (centralizerActor_normalizes h.disconnected d) b ∈
        (distinguishedCentralizer Z d.torus).normalizerMonoidHom.ker := hb
    rw [normalizerMonoidHom_ker] at hk
    exact hk
  have htop : (⊤ : Subgroup G) ≤ centralizer ({(b : G)} : Set G) := by
    rw [← hgen]
    apply sup_le
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (b.property.2 x hx)
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hbK x hx)
  have hbZ : (b : G) ∈ center G :=
    mem_center_iff.mpr (fun x => mem_centralizer_singleton_iff.mp (htop (mem_top x)))
  rw [ambient_center_eq_bot h r] at hbZ
  exact Subtype.ext (mem_bot.mp hbZ)

omit [Finite G] in
/-- The given element centralizes its distinguished centralizer closure. -/
public theorem involution_mem_centralizerActor : u ∈ centralizerActor Z u := by
  refine ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
  intro x hx
  exact mem_centralizer_singleton_iff.mp (centralizerClosure_le Z u hx)

/-- Faithfulness and fixed-subgroup rigidity identify the source actor with ⟨u⟩. -/
public theorem centralizerActor_eq_zpowers
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : SecondCentralizerData Z M z t u n)
    (hgen : centralizerClosure Z u ⊔ distinguishedCentralizer Z d.torus = ⊤)
    (hrigid : FixedCentralizerRigidity (secondInvolution d)) :
    centralizerActor Z u = zpowers u := by
  let a : centralizerActor Z u := ⟨u, involution_mem_centralizerActor⟩
  let rho := secondCentralizerAction h.disconnected d
  have ha : rho a = secondInvolution d := rfl
  refine le_antisymm ?_ (zpowers_le.mpr involution_mem_centralizerActor)
  intro b hb
  let b' : centralizerActor Z u := ⟨b, hb⟩
  have hcomm : Commute (rho b') (secondInvolution d) := by
    rw [← ha]
    apply Commute.map _ rho
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hb.1)
  have hfixed : ∀ x, secondInvolution d x = x → rho b' x = x := by
    intro x hx
    have hxC : (x : G) ∈ centralizer ({u} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hx' : u * (x : G) * u⁻¹ = (x : G) := congrArg Subtype.val hx
      exact (mul_inv_eq_iff_eq_mul.mp hx').symm
    have hxL : (x : G) ∈ residualGenerated M z t :=
      d.fixed ▸ (show (x : G) ∈ distinguishedCentralizer Z d.torus ⊓ centralizer ({u} : Set G)
        from ⟨x.property, hxC⟩)
    have hxLu : (x : G) ∈ centralizerClosure Z u :=
      (d.intersection ▸ (inf_le_right : distinguishedCentralizer Z d.torus ⊓
        centralizerClosure Z u ≤ centralizerClosure Z u)) hxL
    apply Subtype.ext
    change b * (x : G) * b⁻¹ = (x : G)
    rw [(hb.2 x hxLu).symm, mul_inv_cancel_right]
  rcases hrigid (rho b') hcomm hfixed with hb1 | hba
  · have he : b' = 1 := secondCentralizerAction_injective h r d hgen
      (hb1.trans rho.map_one.symm)
    have he' : b = 1 := congrArg (fun x : centralizerActor Z u => (x : G)) he
    rw [he']
    exact (zpowers u).one_mem
  · have he : b' = a := secondCentralizerAction_injective h r d hgen (hba.trans ha.symm)
    have he' : b = u := congrArg (fun x : centralizerActor Z u => (x : G)) he
    rw [he']
    exact mem_zpowers u

/-- The exact Sylow assertion and the bound for all ambient two-subgroups. -/
public theorem centralizer_sylow_and_bound_of_generation_and_rigidity
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hu : PFAppendixIII.IsInvolution u) (d : SecondCentralizerData Z M z t u n)
    (hgen : centralizerClosure Z u ⊔ distinguishedCentralizer Z d.torus = ⊤)
    (hrigid : FixedCentralizerRigidity (secondInvolution d)) :
    (∃ S : Sylow 2 (centralizer (centralizerClosure Z u : Set G)),
      (S : Subgroup (centralizer (centralizerClosure Z u : Set G))).map
        (centralizer (centralizerClosure Z u : Set G)).subtype = zpowers u) ∧
      CentralizerTwoBound Z u := by
  let C := centralizer (centralizerClosure Z u : Set G)
  let a : C := ⟨u, involution_mem_centralizerActor.2⟩
  have ha : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hu.sq_eq_one hu.ne_one
  have hcollapse := centralizerActor_eq_zpowers h r d hgen hrigid
  have hself : centralizer ({a} : Set C) ≤ zpowers a := by
    intro x hx
    have hb : (x : G) ∈ centralizerActor Z u :=
      ⟨mem_centralizer_singleton_iff.mpr
        (congrArg (fun y : C => (y : G)) (mem_centralizer_singleton_iff.mp hx)), x.property⟩
    rw [hcollapse] at hb
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
  constructor
  · obtain ⟨S, hS⟩ := exists_sylow_of_self_centralizing_involution a ha hself
    refine ⟨S, ?_⟩
    rw [hS, MonoidHom.map_zpowers]
    rfl
  · intro P hPC hP
    have hPc : IsPGroup 2 (P.subgroupOf C) := hP.comap_of_injective C.subtype C.subtype_injective
    have hbound := card_le_two_of_self_centralizing_involution a ha hself (P.subgroupOf C) hPc
    rwa [Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv] at hbound

end BenderSuzuki.ZD.UnitaryExclusion
