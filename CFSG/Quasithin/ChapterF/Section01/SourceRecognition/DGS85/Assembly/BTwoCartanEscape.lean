module
public import Theory.SpecificGroups.SL2.TorusSylowCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ExtendedCartanKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoOddEdgeObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoRegular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicEdgeGeneration

/-!
# Escape of the Cartan displacement from the adjacent-core intersection

For the original nonsolvable alpha endpoint at critical distance two,
every nontrivial subgroup of the beta torus moves the source seed outside
Dα. A trapped action would fix the full Sylow image at t and at g • u.
Full-torus rigidity then makes both adjacent local quotient actions trivial,
and coprime centralizer lifting contradicts graph faithfulness.

The same full Cartan turns a nonzero invariant two-subgroup into the full
Sylow image. This supplies the subsequent seed-generation step of (10.8).
All local markings and both Sylow-product identities in the escape theorem
are derived from the original F.1.11 source. The tested residual's final
vanishing and the binary alpha branches are not asserted here.

Source: DGS, *Groups and Graphs* (1985), (10.8), printed pp.160--161.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Noncommuting NoncommutingProfile
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem full_cartan_sylow_centralizes_local_quotient
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (hF : 2 < Nat.card F)
    (K : Subgroup G) [IsMulCommutative K]
    (hKE : K ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hdis : Disjoint K ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hgen : K ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (ho : Odd (Nat.card K))
    (x : G) (hx : x ∈ K)
    (hmove : ∀ s ∈ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2,
      ⁅x,s⁆ ∈ Q (family P) w) :
    ∀ l ∈ graphLocalGroup (family P) w, ⁅x,l⁆ ∈ Q (family P) w := by
  let _ := finite_endpoints h
  let M := graphLocalGroup (family P) w
  let E := stabilizer (family P) w ⊓ stabilizer (family P) v
  let C := K ⊓ M
  let _ : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  obtain ⟨T,hT⟩ := CommutingTrivial.local_edge_sylow h hB hS hvw.symm
  change (T : Subgroup M).map M.subtype = E.pCoreIn 2 at hT
  have hTN := graph_intrinsic_edge_sylow_normalizer h hB hvw.symm T hT
  have hKE' : K ≤ E := hKE.trans (inf_comm _ _).le
  obtain ⟨⟨eC⟩,_⟩ := CommutingTrivial.edge_complement_local_torus h hB hS hvw.symm e K hKE'
    (by simpa only [E,inf_comm (stabilizer (family P) w)] using hdis)
    (by simpa only [E,inf_comm (stabilizer (family P) w)] using hgen)
  have hxN : x ∈ normalizer (M : Set G) :=
    sylowGenerated_normalized _ (hKE hx).2
  let α := M.normalizerMonoidHom ⟨x,hxN⟩
  have hα (l : M) : (α l : G) = x*l*x⁻¹ := rfl
  have hCN : C.subgroupOf M ≤ normalizer (T : Set M) := by
    rw [←hTN]
    exact fun c hc => (hKE hc.1).1
  have hCo : Odd (Nat.card (C.subgroupOf M)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ M from inf_le_right)).toEquiv]
    exact ho.of_dvd_nat (card_dvd_of_le (show C ≤ K from inf_le_left))
  have hCc : Nat.card (C.subgroupOf M) = Nat.card Fˣ :=
    (Nat.card_congr (subgroupOfEquivOfLe (show C ≤ M from inf_le_right)).toEquiv).trans
      (Nat.card_congr eC.toEquiv)
  have hfixC : ∀ c ∈ C.subgroupOf M, α c = c := by
    intro c hc
    apply Subtype.ext
    change x*c*x⁻¹ = c
    exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val
      (mul_comm (⟨x,hx⟩ : K) (⟨c,hc.1⟩ : K)))
  have hfixT : ∀ t ∈ T, QuotientGroup.mk' (pCore 2 M) (α t) =
      QuotientGroup.mk' (pCore 2 M) t := by
    intro t ht
    apply QuotientGroup.eq_iff_div_mem.mpr
    have htE : (t : G) ∈ E.pCoreIn 2 := hT ▸ mem_map_of_mem M.subtype ht
    have hm := hmove t (by simpa only [E,inf_comm] using htE)
    have he : ((α t / t : M) : G) = ⁅x,(t : G)⁆ := by
      change (x*t*x⁻¹)/t = ⁅x,(t : G)⁆
      simp only [div_eq_mul_inv,commutatorElement_def]
    rw [←he,←CommutingTrivial.graphLocalGroup_core h w] at hm
    obtain ⟨d,hd,hdv⟩ := hm
    exact (show d = α t / t from Subtype.ext hdv) ▸ hd
  have hqα := Matrix.SpecialLinearGroup.core_quotient_torus_sylow_fixed hF e T
    (C.subgroupOf M) hCN hCo hCc α hfixT hfixC
  intro l hl
  let l' : M := ⟨l,hl⟩
  have he : QuotientGroup.mk' (pCore 2 M) (α l') =
      QuotientGroup.mk' (pCore 2 M) l' := by
    calc
      QuotientGroup.mk' (pCore 2 M) (α l') =
          (pCore 2 M).quotientAut α (QuotientGroup.mk' (pCore 2 M) l') :=
        (quotientAut_apply_mk (pCore 2 M) α l').symm
      _ = QuotientGroup.mk' (pCore 2 M) l' := by rw [hqα]; rfl
  have hmem := QuotientGroup.eq_iff_div_mem.mp he
  apply (CommutingTrivial.graphLocalGroup_core h w).le
  refine ⟨α l'/l',hmem,?_⟩
  change (x*l*x⁻¹)/l = ⁅x,l⁆
  simp only [div_eq_mul_inv,commutatorElement_def]


section CartanSpan
open CommutingTrivial
theorem cartan_normalized_two_subgroup_core_product
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (C A : Subgroup G)
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hc : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hAS : A ≤ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hp : IsPGroup 2 A) (hn : C ≤ normalizer (A : Set G))
    (hne : ¬ A ≤ Q (family P) v) :
    A ⊔ Q (family P) v = (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 := by
  have hAE : A ≤ stabilizer (family P) v ⊓ stabilizer (family P) w := hAS.trans (pCoreIn_le 2 _)
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let E := stabilizer Γ v ⊓ stabilizer Γ w
  let S := E.pCoreIn 2
  let T := C ⊓ H
  let D := T ⊔ A
  have hAH : A ≤ H := pGroup_le_sylowGenerated _ A (hAE.trans inf_le_left) hp
  have hDH : D ≤ H := sup_le inf_le_right hAH
  have hDE : D ≤ E := sup_le (inf_le_left.trans hCE) hAE
  have hTS : S ⊔ T = H ⊓ E := (edge_complement_local_torus h hB hS hvw e C hCE hc hg).2
  have hSH : S ≤ H := le_sup_left.trans (hTS.le.trans inf_le_left)
  have hDS : D ⊔ S = H ⊓ E := by
    apply le_antisymm (sup_le (le_inf hDH hDE) (le_inf hSH (pCoreIn_le 2 E)))
    rw [←hTS]
    exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  have hDN : D ≤ normalizer (A : Set G) := sup_le (inf_le_left.trans hn) A.le_normalizer
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk₀ : q₀.ker = (Q Γ v).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    rw [←graphLocalGroup_core h v]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  obtain ⟨s,hs⟩ := source_linear_borel_marking h hB hS hvw q₀ hq₀ hk₀
  let q := (MulAut.conj s).toMonoidHom.comp q₀
  have hk : q.ker = (Q Γ v).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj s).injective,hk₀]
  have hgen : D.subgroupOf H ⊔ S.subgroupOf H = (Matrix.SpecialLinearGroup.rankOneBorel F).comap q := by
    rw [←hs]
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hDH,map_subgroupOf_eq_of_le hSH,hDS,
      subgroupOf_map_subtype]
    apply le_antisymm (le_inf (inf_le_right.trans inf_le_right) inf_le_left)
    intro z hz
    exact ⟨hz.2,⟨sylowGenerated_le _ hz.2,hz.1⟩⟩
  have hnorm : D.subgroupOf H ≤ normalizer (A.subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro d hd a ha
    exact (mem_normalizer_iff.mp (hDN hd) (a : G)).mp ha
  have him := Matrix.SpecialLinearGroup.normal_two_image_of_borel_supplement q
    ((MulAut.conj s).surjective.comp hq₀) (D.subgroupOf H) (S.subgroupOf H)
    (A.subgroupOf H) hgen (isPGroup_pCoreIn 2 E).comap_subtype hp.comap_subtype
    (comap_mono (show A ≤ D from le_sup_right)) hnorm (by
      intro he
      apply hne
      intro a ha
      have hh := he (show (⟨a,hAH ha⟩ : H) ∈ A.subgroupOf H from ha)
      rw [hk] at hh
      exact hh)
  have hSQ : (S.subgroupOf H).map q ≤ Matrix.SpecialLinearGroup.upperUnipotent F := by
    have hpS := (isPGroup_pCoreIn 2 E).comap_subtype.map q
    have hh := hpS.inf_normalizer_sylow (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
    have hSB : (S.subgroupOf H).map q ≤ Matrix.SpecialLinearGroup.rankOneBorel F :=
      map_le_iff_le_comap.mpr (le_sup_right.trans hgen.le)
    change (S.subgroupOf H).map q ⊓ Matrix.SpecialLinearGroup.rankOneBorel F =
      (S.subgroupOf H).map q ⊓ Matrix.SpecialLinearGroup.upperUnipotent F at hh
    rw [inf_eq_left.mpr hSB] at hh
    exact hh.le.trans inf_le_right
  have hcover : S.subgroupOf H ≤ A.subgroupOf H ⊔ q.ker := by
    rw [←comap_map_eq]
    exact (map_le_iff_le_comap).mp (hSQ.trans him.ge)
  have hcover' := map_mono (f := H.subtype) hcover
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hSH,map_subgroupOf_eq_of_le hAH,
    hk,map_subgroupOf_eq_of_le ((graph_Q_le_edgeCore h hvw).trans (graph_intrinsic_edgeCore_le h))] at hcover'
  exact le_antisymm (sup_le hAS (graph_Q_le_edgeCore h hvw)) hcover'

end CartanSpan

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Reduction Noncommuting NoncommutingProfile
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private def localQuotientConjugate (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (g : G) (hg : g • v = w) :
    (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃*
      (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) := by
  let e := ((graphLocalGroup (family P) v).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr ((graphLocalGroup_conjugate h g v).symm.trans (congrArg _ hg)))
  exact QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private theorem cartan_fixes_translate (K : Subgroup G) {g : G}
    (hgK : g ∈ normalizer (K : Set G)) {v : Vertex (family P)}
    (hv : K ≤ stabilizer (family P) v) :
    K ≤ stabilizer (family P) (g • v) := by
  intro k hk
  have hh := (mem_normalizer_iff.mp ((normalizer (K : Set G)).inv_mem hgK) k).mp hk
  have he : (g⁻¹*k*g) • v = v := hv (by simpa only [inv_inv] using hh)
  have he' := congrArg (g • ·) he
  change k • (g • v) = g • v
  simpa only [mul_smul,smul_inv_smul] using he'

private theorem edge_core_translate (g : G) (v w : Vertex (family P)) :
    ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2).map
      (MulAut.conj g).toMonoidHom =
      (stabilizer (family P) (g • v) ⊓ stabilizer (family P) (g • w)).pCoreIn 2 := by
  rw [stabilizer_translate,stabilizer_translate,
    ←map_inf _ _ _ (MulAut.conj g).injective,
    Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj g).injective]

universe u
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

/-- A nontrivial subgroup of the beta torus moves the actual seed outside Dα.
The hypothetical trapped action would be trivial on two adjacent local
quotients, contradicting graph faithfulness. -/
theorem original_bTwo_cartan_commutator_escape
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    (K : Subgroup (G₀ L S)) [IsMulCommutative K]
    (hKE : K ≤ stabilizer F α ⊓ stabilizer F β)
    (hKt : K ≤ stabilizer F t) (hKu : K ≤ stabilizer F u)
    (hd : Disjoint K ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2))
    (hgen : K ⊔ (stabilizer F α ⊓ stabilizer F β).pCoreIn 2 =
      stabilizer F α ⊓ stabilizer F β)
    (ho : Odd (Nat.card K))
    (g : G₀ L S) (hg : g ∈ graphLocalGroup F α)
    (hgK : g ∈ normalizer (K : Set (G₀ L S))) (hgt : g • β = t)
    (a : G₀ L S) (hau : a • α = u)
    (T : Subgroup (G₀ L S)) (hTK : T ≤ K ⊓ graphLocalGroup F β) (hTne : T ≠ ⊥) :
    ¬ ⁅V F β 1 ⊓ Q F α,T⁆ ≤ D F β t := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hB := reduced_borel_core_sylow h
  have hS := reduced_vertex_sylow h
  have hSyl := reduced_kernel_sylow h
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let _ : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk := field_gt_two_of_nonsolvable h c hactor hns
  obtain ⟨n,hn,J,fJ,finJ,hJ,⟨eJ⟩⟩ :=
    reduced_noncommuting_actor_quotients_linear h hc hne β
  let _ := fJ
  let _ := finJ
  let _ : Fintype J := Fintype.ofFinite J
  let _ : CharP J 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hJ)
  let eβ := eJ.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi J)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  have hJlarge : 2 < Nat.card J := hk.trans_le
    (c.linear_central_core_structure H hB hS hb hactor hcentral ht htne hcomm.le hnot eβ).1
  have hcore : c.actor.pCoreIn 2 = Q F α := by
    rw [hactor]
    exact CommutingTrivial.graphLocalGroup_core H α
  have hker : c.quotient.ker = pCore 2 c.actor := by
    rw [c.kernel]
    change (Q F α).subgroupOf c.actor = pCore 2 c.actor
    rw [←hcore]
    exact comap_map_eq_self_of_injective c.actor.subtype_injective _
  let eA := MulEquiv.subgroupCongr hactor
  let eQ := QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)
  let eα := eQ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto))
  let z := g • u
  have hga : g • α = α := sylowGenerated_le _ hg
  have htz : (graph F).Adj t z := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hβu
    change (graph F).Adj (g • β) (g • u) at hh
    simpa only [hgt] using hh
  have hKz : K ≤ stabilizer F z := cartan_fixes_translate K hgK hKu
  let et : (graphLocalGroup F t ⧸ pCore 2 (graphLocalGroup F t)) ≃* SL(2,J) :=
    (localQuotientConjugate H g hgt).symm.trans eβ
  have hgaz : (g*a) • α = z := by simp only [mul_smul,hau]; rfl
  let ez : (graphLocalGroup F z ⧸ pCore 2 (graphLocalGroup F z)) ≃* SL(2,k) :=
    (localQuotientConjugate H (g*a) hgaz).symm.trans eα
  have nQ (v : Vertex F) : stabilizer F v ≤ normalizer (Q F v : Set (G₀ L S)) :=
    CommutingNontrivial.stabilizer_normalizes_Q F v
  have hQat : Q F α ≤ stabilizer F t :=
    (source_Z_Q_U H α).2.trans ((ballKernel_one_le_edge F ht).trans inf_le_right)
  have hQut : Q F u ≤ stabilizer F β :=
    (source_Z_Q_U H u).2.trans ((ballKernel_one_le_edge F hβu.symm).trans inf_le_right)
  have hseed := (c.linear_seed_eq_core_and_index H hB hS hSyl hb ht htne hnot eβ).1
  have hVt : V F t 1 ≤ Q F t := graph_V_le_Q_of_short H hSyl t (by rw [hb]; decide)
  have hEαt : (stabilizer F α ⊓ stabilizer F t).pCoreIn 2 = Q F α ⊔ Q F t := by
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) (c.core_product_eq_edge_core H)
    rw [Subgroup.map_sup,←Q_translate,←Q_translate,edge_core_translate,hgt,hga] at hh
    simpa only [inf_comm,sup_comm] using hh.symm
  have hEu : Z F α ⊔ Q F u = (stabilizer F u ⊓ stabilizer F β).pCoreIn 2 := by
    obtain ⟨R,hR⟩ := c.critical_product
    have hZu : Z F α ⊔ Q F u ≤ stabilizer F u := hR ▸ map_subtype_le _
    have hZβ : Z F α ≤ Q F β := graph_Z_le_Q_of_short H hSyl (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab,hb]; decide)
    have hE : Z F α ⊔ Q F u ≤ stabilizer F u ⊓ stabilizer F β :=
      le_inf hZu (sup_le (hZβ.trans (Q_le_stabilizer F β)) hQut)
    exact hR.symm.trans (sylow_image_eq_edge_core _ _ inf_le_left
      (source_edge_core_sylow H hB hβu.symm) R (hR ▸ hE))
  have hZt : Z F t ≤ Q F z := graph_Z_le_Q_of_short H hSyl (by
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr htz,hb]; decide)
  have hEz : (stabilizer F t ⊓ stabilizer F z).pCoreIn 2 = Z F β ⊔ Q F z := by
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) hEu
    rw [Subgroup.map_sup,←Z_translate,←Q_translate,edge_core_translate,hga,hgt] at hh
    change Z F α ⊔ Q F z = (stabilizer F z ⊓ stabilizer F t).pCoreIn 2 at hh
    rw [(c.central_neighbor_centers H hB hS hb hactor hcentral ht htne).1,
      sup_assoc,sup_eq_right.mpr hZt] at hh
    simpa only [inf_comm] using hh.symm
  intro htrapped
  have hTfix (v : Vertex F) (hKv : K ≤ stabilizer F v) :
      T ≤ normalizer (Q F v : Set (G₀ L S)) := (hTK.trans inf_le_left).trans (hKv.trans (nQ v))
  have hQt : ⁅Q F t,T⁆ ≤ Q F t :=
    le_normalizer_iff_commutator_le_left.mp (hTfix t hKt)
  have hQa : ⁅Q F α,T⁆ ≤ Q F t := by
    rw [←hseed]
    unfold centralSeed
    apply commutator_sup_le_of_relative_normal (Q F α) _ _ _ _
      (hQat.trans (nQ t))
      (sup_le inf_le_right inf_le_right)
      (by
        obtain ⟨_,_,hD,_,_,_,_,_⟩ := c.central_D_structure H hSyl hb
          (c.omega_eq_bot_of_central_neighbor H hB hS hactor hcentral) ht htne
        exact hD)
    · exact commutator_sup_le_of_relative_normal (Q F α) _ _ _ _
        (hQat.trans (nQ t)) inf_le_right inf_le_right
        (htrapped.trans inf_le_right)
        ((commutator_mono (inf_le_left.trans hVt) le_rfl).trans hQt)
    · exact (commutator_mono inf_le_right le_rfl).trans hQt
  have hEt : ⁅(stabilizer F α ⊓ stabilizer F t).pCoreIn 2,T⁆ ≤ Q F t := by
    rw [hEαt]
    exact commutator_sup_le_of_relative_normal (stabilizer F t) _ _ _ _
      (nQ t) hQat (Q_le_stabilizer F t) hQa hQt
  have hZc : ⁅Z F β,T⁆ ≤ Q F z := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr
      ((hcentral.trans inf_le_right).trans (centralizer_le (hTK.trans inf_le_right)))]
    exact bot_le
  have hQz : ⁅Q F z,T⁆ ≤ Q F z :=
    le_normalizer_iff_commutator_le_left.mp (hTfix z hKz)
  have hEzm : ⁅(stabilizer F t ⊓ stabilizer F z).pCoreIn 2,T⁆ ≤ Q F z := by
    rw [hEz]
    exact commutator_sup_le_of_relative_normal (stabilizer F z) _ _ _ _
      (nQ z)
      ((le_sup_left.trans hEz.ge).trans ((pCoreIn_le 2 _).trans inf_le_right))
      (Q_le_stabilizer F z) hZc hQz
  have htK : K ≤ stabilizer F α ⊓ stabilizer F t := le_inf (hKE.trans inf_le_left) hKt
  have hzK : K ≤ stabilizer F t ⊓ stabilizer F z := le_inf hKt hKz
  obtain ⟨hdt,hgtK⟩ := CommutingTrivial.path_cartan_complement_at_edge H hab ht K hKE htK ho hd hgen
  obtain ⟨hdz,hgzK⟩ := CommutingTrivial.path_cartan_complement_at_edge H hab htz K hKE hzK ho hd hgen
  have htall : ⁅graphLocalGroup F t,T⁆ ≤ Q F t := by
    rw [commutator_comm] at hEt ⊢
    apply commutator_le.mpr
    intro x hx l hl
    exact full_cartan_sylow_centralizes_local_quotient H hB hS ht et hJlarge K htK
      hdt hgtK ho x ((hTK hx).1) (fun s hs => hEt (commutator_mem_commutator hx hs)) l hl
  have hzall : ⁅graphLocalGroup F z,T⁆ ≤ Q F z := by
    rw [commutator_comm] at hEzm ⊢
    apply commutator_le.mpr
    intro x hx l hl
    exact full_cartan_sylow_centralizes_local_quotient H hB hS htz ez hk K hzK
      hdz hgzK ho x ((hTK hx).1) (fun s hs => hEzm (commutator_mem_commutator hx hs)) l hl
  have commT (x y : T) : x*y = y*x := by
    apply Subtype.ext
    exact congrArg (fun k : K => (k : G₀ L S))
      (mul_comm (⟨x,(hTK x.property).1⟩ : K) (⟨y,(hTK y.property).1⟩ : K))
  let _ : IsMulCommutative T := ⟨⟨commT⟩⟩
  let _ : Group.IsSolvable T := Group.isSolvable_of_comm (mul_comm' (M := T))
  exact hTne (odd_edge_actor_eq_bot_of_core_displacement H hB hS htz T
    ((hTK.trans inf_le_left).trans hzK)
    (ho.of_dvd_nat (card_dvd_of_le (hTK.trans inf_le_left))) htall hzall)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
