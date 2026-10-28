module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalNonbinary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicRadiusAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingCatalogue

/-!
# The strict residual generates the beta core

The two adjacent-core intersections generate Q_alpha. Their commutators
with R_alpha lie in the two neighboring centers, hence in Z_alpha.
The resulting commutator is invariant under the actual alpha actor:
the opposite centers centralize R_alpha and normalize Q_alpha. If it
were trivial, R_alpha would lie in the vanishing central omega. The
natural alpha-center action therefore gives [R_alpha,Q_alpha] = Z_alpha.

The beta-local conjugates of Z_alpha generate V_beta. Since Q_alpha
lies in the beta local group and Q_beta = V_beta D_alpha with
D_alpha = Z_alpha R_alpha, the beta-local conjugates of the same residual
generate Q_beta. The original-source application preserves any chosen
opposite-center transporter and all original endpoint inclusions.

These are the residual-generation calculations for the commutator step
in DGS, Groups and Graphs (1985), (10.10)(d), printed pp.164--165,
using (10.4) and (10.7). Nonbinary torus movement and irreducibility are
subsequent steps; neither is assumed here.
-/

public noncomputable section
open Subgroup Representation Representation.RankOne.QuadraticRecognition
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- Every strict opposite-center residual generates the natural alpha center
by commutators with the actual alpha core. -/
theorem BTwoCenterActionData.strict_residual_core_commutator
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    (hb : b F=2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor=graphLocalGroup F v)
    (hcentral : Z F m≤centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (htne : t≠m)
    (hcomm : ⁅V F m 1,Q F m⁆=Z F m)
    (hnot : ¬stabilizer F v≤normalizer ((Q F m⊓Q F v:Subgroup G):Set G))
    (eβ : (graphLocalGroup F m⧸pCore 2 (graphLocalGroup F m))≃*SL(2,K))
    (hD : D F m t≠Z F v) (E : W≃ₗ[ZMod 2](Fin 2→k))
    (g : c.actor) (hg : (g:G) • m=t) :
    ⁅bTwoResidual F m t w ((g:G) • w),Q F v⁆=Z F v := by
  let := finite_endpoints h
  let hS := source_kernel_sylow h hB hSyl
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  have hop : c.quotient g∉normalizer (c.imageSylow:Set SL(2,k)) := by
    intro he
    exact htne (hg.symm.trans (c.normalizer_fixes_neighbor h g he))
  obtain ⟨d,hdactor,hker⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  let A := Z F w⊔Z F ((g:G) • w)
  let R := bTwoResidual F m t w ((g:G) • w)
  let I := Q F v⊓Q F m
  let J := ⁅R,Q F v⁆
  have hres : d.residual=R := d.residual_eq_source h hS hb (hdactor.symm ▸ hω)
  have hgen : A⊔Q F v=c.actor := d.actor_generators.symm.trans hdactor
  have hRQ : R≤Q F v := inf_le_left.trans d.separated
  have hRne : R≠⊥ := by
    intro he
    apply hD
    have hh := d.decomposition h hS hb
    rw [hres,he,sup_bot_eq] at hh
    exact hh
  have hdis : Disjoint d.residual (Z F v) :=
    disjoint_iff.mpr (bot_unique (hker.trans hω.le))
  let hDel := d.elementary h hS hb c.sylow (hdactor.symm ▸ c.sylow_le_actor) hdis
  let _ := hDel
  have hR2 (r : G) (hr : r∈R) : r^2=1 :=
    elemPow_eq_one_of_isElementaryAbelian r hr.1
  have hder := (c.beta_core_frattini_eq h hB hSyl hb hactor hcentral ht htne hcomm).2
  have hgv : (g:G) • v=v := c.actor_le g.property
  have hgenQ : I⊔I.conjBy (g:G)=Q F v := by
    dsimp only [I]
    rw [conjBy,map_inf _ _ _ (MulAut.conj (g:G)).injective,←Q_translate,←Q_translate,hgv,hg]
    exact (c.seed_eq_core_intersections h hS hb ht htne).symm.trans
      (c.linear_seed_eq_core_and_index h hB hSyl hS hb ht htne hnot eβ).1
  have hZmv := center_le_of_central_neighbor h hB hSyl c.middle hcentral
  have hZtv : Z F t≤Z F v := by
    have hh := map_mono (f:=(MulAut.conj (g:G)).toMonoidHom) hZmv
    rwa [←Z_translate,←Z_translate,hgv,hg] at hh
  have hdert : ⁅Q F t,Q F t⁆=Z F t := by
    have hh := congrArg (map (MulAut.conj (g:G)).toMonoidHom) hder
    rwa [map_commutator,←Q_translate,←Z_translate,hg] at hh
  have hIle : I.conjBy (g:G)≤Q F t := by
    change I.map (MulAut.conj (g:G)).toMonoidHom≤Q F t
    have hh := map_mono (f:=(MulAut.conj (g:G)).toMonoidHom) (show I≤Q F m from inf_le_right)
    rwa [←Q_translate,hg] at hh
  have hJZ : J≤Z F v := by
    change ⁅R,Q F v⁆≤Z F v
    rw [commutator_comm,←hgenQ]
    apply commutator_sup_le_of_relative_normal (Q F v) I (I.conjBy (g:G)) R (Z F v)
      ((graph_Q_centralizes_Z h v).trans (Subgroup.centralizer_le_normalizer _))
      inf_le_left (le_sup_right.trans hgenQ.le)
    · exact ((commutator_mono inf_le_right (inf_le_left.trans inf_le_left)).trans hder.le).trans hZmv
    · exact ((commutator_mono hIle (inf_le_left.trans inf_le_right)).trans hdert.le).trans hZtv
  have hnQ : c.actor≤normalizer (Q F v:Set G) :=
    c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F v)
  have hnJ : c.actor≤normalizer (J:Set G) := by
    rw [←hgen]
    apply sup_le ?_ (normalizer_commutator_ge_right R (Q F v))
    intro a ha
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅R,Q F v⁆).map (MulAut.conj a).toMonoidHom=⁅R,Q F v⁆
    rw [map_commutator]
    have haR : a∈normalizer (R:Set G) :=
      (Subgroup.centralizer_le_normalizer _) ((le_centralizer_iff.mp (show R≤centralizer (A:Set G) from inf_le_right)) ha)
    have hrm : R.map (MulAut.conj a).toMonoidHom=R :=
      mem_normalizer_iff_map_conj_eq.mp haR
    have hqm : (Q F v).map (MulAut.conj a).toMonoidHom=Q F v :=
      mem_normalizer_iff_map_conj_eq.mp (hnQ (hgen ▸ mem_sup_left ha))
    rw [hrm,hqm]
  have hJne : J≠⊥ := by
    intro he
    have hRC : R≤centralizer (Q F v:Set G) := commutator_eq_bot_iff_le_centralizer.mp he
    apply hRne
    apply bot_unique
    intro r hr
    have hLC : c.actor≤centralizer ({r}:Set G) := by
      rw [←hgen]
      exact sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (hr.2 a ha))
        (fun q hq => mem_centralizer_singleton_iff.mpr (hRC hr q hq))
    exact hω ▸ (mem_omegaCenterIn_iff _ _).mpr
      ⟨c.core_le (hRQ hr),fun a ha => mem_centralizer_singleton_iff.mp (hLC ha),hR2 r hr⟩
  obtain ⟨eZ,heZ⟩ := c.center_natural_coordinates E
  let : c.representation.IsIrreducible := irreducible_of_natural_coordinates c.representation eZ heZ
  let : IsIrreducible (c.representation.comp c.quotient) :=
    (irreducible_comp_surjective_iff c.quotient c.onto c.representation).mpr inferInstance
  exact (c.coordinates.eq_kernel_or_section J (hω ▸ bot_le) hJZ hnJ).resolve_left
    (fun hh => hJne (hh.trans hω))

/-- The beta-local conjugates of the same residual generate the beta core. -/
theorem BTwoCenterActionData.strict_residual_beta_span
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    (hb : b F=2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor=graphLocalGroup F v)
    (hcentral : Z F m≤centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (htne : t≠m)
    (hcomm : ⁅V F m 1,Q F m⁆=Z F m)
    (hnot : ¬stabilizer F v≤normalizer ((Q F m⊓Q F v:Subgroup G):Set G))
    (eβ : (graphLocalGroup F m⧸pCore 2 (graphLocalGroup F m))≃*SL(2,K))
    (hD : D F m t≠Z F v) (E : W≃ₗ[ZMod 2](Fin 2→k))
    (g : c.actor) (hg : (g:G) • m=t) :
    conjugateSpanBy (bTwoResidual F m t w ((g:G) • w)) (graphLocalGroup F m)=Q F m := by
  let R := bTwoResidual F m t w ((g:G) • w)
  let N := conjugateSpanBy R (graphLocalGroup F m)
  have hRN : R≤N := le_conjugateSpanBy _ _
  have hnN : graphLocalGroup F m≤normalizer (N:Set G) := le_normalizer_conjugateSpanBy _ _
  have hQaL : Q F v≤graphLocalGroup F m := by
    have hh := graph_Q_le_edgeCore h c.middle
    have hh' : Q F v≤(stabilizer F m⊓stabilizer F v).pCoreIn 2 := by
      simpa only [inf_comm] using hh
    exact hh'.trans (graph_intrinsic_edgeCore_le h)
  have hZaN : Z F v≤N := by
    rw [←c.strict_residual_core_commutator h hB hSyl hb hactor hcentral ht htne
      hcomm hnot eβ hD E g hg]
    exact (commutator_mono hRN le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hQaL.trans hnN))
  have hVN : V F m 1≤N := by
    rw [←graph_intrinsic_radius_span h hB hSyl c.middle
      (center_le_of_central_neighbor h hB hSyl c.middle hcentral)]
    exact conjugateSpanBy_le hZaN hnN
  have hS := source_kernel_sylow h hB hSyl
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  have hop : c.quotient g∉normalizer (c.imageSylow:Set SL(2,k)) := by
    intro he
    exact htne (hg.symm.trans (c.normalizer_fixes_neighbor h g he))
  obtain ⟨d,hdactor,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hdec : D F m t=Z F v⊔R := by
    rw [d.decomposition h hS hb,d.residual_eq_source h hS hb (hdactor.symm ▸ hω)]
  apply le_antisymm
  · exact conjugateSpanBy_le (inf_le_left.trans inf_le_left)
      ((sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Q F m))
  · rw [c.beta_core_product h hS hb ht htne,hdec]
    exact sup_le hVN (sup_le hZaN hRN)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The original strict source supplies residual commutator generation and
normal generation of the full beta core, for any chosen opposite transporter.
All natural actions and linear quotient markings are constructed internally. -/
theorem original_bTwo_strict_residual_normal_generation
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (g : G₀ L S) (hg : g∈graphLocalGroup F α) (hgt : g • β=t) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁⊓(Q F t).map ι
    let Z₀ := (Z F α).map ι
    let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
    let R₀ := D₀⊓centralizer (W₀:Set G)
    ⁅R₀,Q₀⁆=Z₀ ∧ conjugateSpanBy R₀ (enlargedEndpoint L S 1)=Q₁ := by
  let H := reduced_triple h
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  obtain ⟨n,hn,K,fK,finK,hK,⟨eK⟩⟩ := reduced_bTwo_middle_quotient_linear h hc hne hb hab hβu
  let _ := fK
  let _ := finK
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eβ := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hQa : (Q F α).map ι=(parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQb : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hDm : (D F β t).map ι=(parabolic L S 1).pCoreIn 2⊓(Q F t).map ι := by
    change (Q F β⊓Q F t).map ι=_
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQb]
  have hDr : D F β t≠Z F α := by
    intro he
    apply hD
    rw [←hDm,he]
  let g' : c.actor := ⟨g,hactor.symm ▸ hg⟩
  have hco := c.strict_residual_core_commutator H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm hnot eβ hDr
    (LinearEquiv.refl _ _) g' hgt
  have hsp := c.strict_residual_beta_span H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm hnot eβ hDr
    (LinearEquiv.refl _ _) g' hgt
  let R := bTwoResidual F β t u (g • u)
  have hRm : R.map ι=((parabolic L S 1).pCoreIn 2⊓(Q F t).map ι)⊓
      centralizer (((Z F u).map ι⊔(Z F (g • u)).map ι:Subgroup G):Set G) := by
    change (D F β t⊓centralizer ((Z F u⊔Z F (g • u):Subgroup (G₀ L S)):Set (G₀ L S))).map ι=_
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,hDm,Subgroup.map_sup]
  constructor
  · have hh := congrArg (map ι) hco
    change (⁅R,Q F α⁆).map ι=(Z F α).map ι at hh
    rwa [map_commutator,hRm,hQa] at hh
  · have hh := congrArg (map ι) hsp
    change (conjugateSpanBy R (graphLocalGroup F β)).map ι=(Q F β).map ι at hh
    rwa [map_conjugateSpanBy,hRm,hQb,reduced_graphLocalGroup_image h true] at hh

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
