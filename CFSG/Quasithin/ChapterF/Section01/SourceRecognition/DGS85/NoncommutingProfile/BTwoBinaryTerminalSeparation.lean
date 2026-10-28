module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryThirdNeighbor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryCoreCentralizer

/-!
# Binary terminal-core separation

This completes the binary beta-quotient branch of DGS (10.8) for the
literal residual inside the original completion. In the strict case,
the existing dihedral-centralizing actor exchanges the critical endpoints
and fixes their third common neighbor. Transport of the critical center
intersections around the three-neighbor action shows that the terminal
center escapes the third core.

The third core has index two in the beta actor's edge stabilizer. A
terminal-center correction therefore puts the actor in that core while
preserving centralization of the same dihedral subgroup and its coset
outside the beta core. The transported binary core-centralizer bound
then forces it into the beta core, a contradiction.

The final original-source theorem also treats the exceptional case,
where the established residual decomposition makes the residual trivial.
Both results retain the chosen opposite-center conjugator and the actual
reduced-to-original inclusion. Nonbinary terminal separation and the
strict path parameters remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.8), printed pp.159--162, especially the last paragraph on p.162.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting

private theorem binary_edge_index
    {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (family P) v⧸pCore 2 (graphLocalGroup (family P) v))≃*SL(2,K))
    (hK : Nat.card K=2) (hv : Nat.card (Q (family P) v)=32)
    (hw : Nat.card (Q (family P) w)=32) :
    (Q (family P) w).relIndex (graphLocalGroup (family P) v⊓stabilizer (family P) w)=2 := by
  let := finite_endpoints h
  let F := family P
  let A := graphLocalGroup F v
  let E := A⊓stabilizer F w
  have hQc : Nat.card (pCore 2 A)=32 := by
    have hh := card_map_of_injective (f:=A.subtype) (K:=pCore 2 A) A.subtype_injective
    change Nat.card (A.pCoreIn 2)=Nat.card (pCore 2 A) at hh
    have he : A.pCoreIn 2=Q F v := sylowGenerated_core _
    rw [he] at hh
    exact hh.symm.trans hv
  have hA : Nat.card A=192 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
    rw [Nat.card_congr e.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hK,hQc] at hh
    exact hh
  have hEi : E.relIndex A=3 := by
    rw [show E=A⊓stabilizer F w from rfl,inf_relIndex_left]
    have hh := source_linear_edge_index_of_quotient h hB hSyl hvw e
    rw [source_edge_index_local h hB hSyl hvw,hK] at hh
    exact hh
  have hEc : Nat.card E=64 := by
    have hh := (E.subgroupOf A).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show E≤A from inf_le_left)).toEquiv,hA] at hh
    change E.relIndex A*Nat.card E=192 at hh
    rw [hEi] at hh
    omega
  have hQv : Q F w≤stabilizer F v :=
    (source_Z_Q_U h w).2.trans ((ballKernel_one_le_edge F hvw.symm).trans inf_le_right)
  have hQE : Q F w≤E := le_inf
    (pGroup_le_sylowGenerated _ _ hQv (isPGroup_pCoreIn 2 _)) (Q_le_stabilizer F w)
  have hh := ((Q F w).subgroupOf E).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hQE).toEquiv,hw,hEc] at hh
  change (Q F w).relIndex E*32=64 at hh
  change (Q F w).relIndex E=2
  omega

private theorem centralizer_bound_conjugate
    {G : Type*} [Group G] (A B : Subgroup G) (e : G≃*G)
    (h : ∀ r∈B, r∉A → A⊓centralizer ({r}:Set G)≤B) :
    ∀ r∈B.map e.toMonoidHom, r∉A.map e.toMonoidHom →
      A.map e.toMonoidHom⊓centralizer ({r}:Set G)≤B.map e.toMonoidHom := by
  rintro r ⟨r₀,hr,rfl⟩ hrn x ⟨⟨x₀,hx,rfl⟩,hc⟩
  apply mem_map_of_mem
  apply h r₀ hr (fun hh => hrn (mem_map_of_mem _ hh))
  refine ⟨hx,mem_centralizer_singleton_iff.mpr ?_⟩
  apply e.injective
  change e.toMonoidHom (x₀*r₀)=e.toMonoidHom (r₀*x₀)
  rw [map_mul,map_mul]
  exact mem_centralizer_singleton_iff.mp hc

namespace Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The strict binary case of DGS (10.8), on the actual original residual. -/
theorem original_bTwo_binary_strict_terminal_separation
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e : (L 1 ⧸ pCore 2 (L 1))≃*PSL(2,K)) (hK : Nat.card K=2)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      Nat.card R₀=2 ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠β → R₀⊓(Q F y).map ι=⊥ := by
  classical
  obtain ⟨g,hg,hgt,hRc,hΔc,hΔiso,δ,hδ,hδα,hδu,hall,hsep,hcase⟩ :=
    original_bTwo_binary_third_neighbor h hc hne hb hβu ht htne e hK hD
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
    reduced_bTwo_center_action_exists h hc hne hb hab hβu
  change BTwoCenterActionData F α β u k (Fin 2 → k) at c
  change c.actor=graphLocalGroup F α at hactor
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  obtain ⟨g',hg',hgt',hfour,hwhole,hRc',hDel',hdec,hdis,hprod,hZa,hZb,hDc,hQac,hQbc,_⟩ :=
    original_bTwo_binary_strict_orders h hc hne hb hβu ht htne e hK hD
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁⊓(Q F t).map ι
  let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
  let R := D₀⊓centralizer (W₀:Set G)
  let Δ := R⊔centerIn ((V F β 1).map ι)
  change Nat.card R=2 at hRc
  have hQam : (Q F α).map ι=Q₀ := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι=Q₁ := reduced_base_Q_map h true
  have hQag : Nat.card (Q F α)=32 := by
    rw [←card_map_of_injective (f:=ι) (K:=Q F α) (G₀ L S).subtype_injective,hQam]
    exact hQac
  have hQbg : Nat.card (Q F β)=32 := by
    rw [←card_map_of_injective (f:=ι) (K:=Q F β) (G₀ L S).subtype_injective,hQbm]
    exact hQbc
  have image_conj (A : Subgroup (G₀ L S)) (s : G₀ L S) :
      (A.map ι).map (MulAut.conj (ι s)).toMonoidHom=
        (A.map (MulAut.conj s).toMonoidHom).map ι := by
    rw [map_map,map_map]
    congr 1
  have hQconj (v : Vertex F) (s : G₀ L S) :
      ((Q F v).map ι).map (MulAut.conj (ι s)).toMonoidHom=(Q F (s • v)).map ι := by
    rw [image_conj,←Q_translate]
  have hau : α≠u := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    contradiction
  have hmoveadj (s : G₀ L S) (hs : s∈graphLocalGroup F β)
      (v : Vertex F) (hv : (graph F).Adj β v) : (graph F).Adj β (s • v) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F s).map_adj_iff.mpr hv
    change (graph F).Adj (s • β) (s • v) at hh
    rwa [show s • β=β from sylowGenerated_le _ hs] at hh
  obtain ⟨s,hs,hsδ⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) β ⟨α,hab.symm⟩ ⟨δ,hδ⟩
  change s • α=δ at hsδ
  have hsβ : s • β=β := sylowGenerated_le _ hs
  have hQδc : Nat.card (Q F δ)=32 := by
    rw [←hsδ,Q_translate,card_map_of_injective (MulAut.conj s).injective]
    exact hQag
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let E := graphLocalGroup F β⊓stabilizer F δ
  have hindex : (Q F δ).relIndex E=2 := binary_edge_index H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hδ eβ hK hQbg hQδc
  have hCbound : ∀ r∈Q₁, r∉(Q F δ).map ι →
      (Q F δ).map ι⊓centralizer ({r}:Set G)≤Q₁ := by
    have hh := centralizer_bound_conjugate Q₀ Q₁ (MulAut.conj (ι s))
      (original_bTwo_binary_core_centralizer h hc hne hb hβu ht htne e hK)
    rw [←hQam,←hQbm,hQconj,hQconj,hsδ,hsβ,hQbm] at hh
    exact hh
  have hinter : (Z F u)⊓Q F δ=Z F β := by
    obtain ⟨a,ha,haδ⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) β ⟨δ,hδ⟩ ⟨α,hab.symm⟩
    change a • δ=α at haδ
    have haβ : a • β=β := sylowGenerated_le _ ha
    have hia : a • α≠α := fun hh => hδα ((MulAction.injective a) (haδ.trans hh.symm))
    have hiu : a • u≠α := fun hh => hδu ((MulAction.injective a) (haδ.trans hh.symm))
    have hia' : a • α≠a • u := fun hh => hau ((MulAction.injective a) hh)
    obtain ⟨h0,h1,_⟩ := c.central_critical_intersections H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hcentral
    change Z F α⊓Q F u=Z F β at h0
    change Z F u⊓Q F α=Z F β at h1
    have hm0 := congrArg (map (MulAut.conj a).toMonoidHom) h0
    have hm1 := congrArg (map (MulAut.conj a).toMonoidHom) h1
    rw [map_inf _ _ _ (MulAut.conj a).injective,←Z_translate,←Q_translate,←Z_translate,haβ] at hm0 hm1
    rcases hall (a • α) (hmoveadj a ha α hab.symm) with ha0|ha0|ha0
    · exact (hia ha0).elim
    · rcases hall (a • u) (hmoveadj a ha u hβu) with ha1|ha1|ha1
      · exact (hiu ha1).elim
      · exact (hia' (ha0.trans ha1.symm)).elim
      · simpa only [ha0,ha1] using hm0
    · rcases hall (a • u) (hmoveadj a ha u hβu) with ha1|ha1|ha1
      · exact (hiu ha1).elim
      · simpa only [ha0,ha1] using hm1
      · exact (hia' (ha0.trans ha1.symm)).elim
  refine ⟨g,hg,hgt,hRc,?_⟩
  intro y hy hyne
  by_contra hJ
  obtain ⟨hZyC,x,hx,hxu,hxback,hxδ,hxΔ,hxQ⟩ := hcase y hy hyne hJ
  have hZu : Z F u=Z F β⊔Z F y := by
    obtain ⟨a,ha,hau⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) β ⟨α,hab.symm⟩ ⟨u,hβu⟩
    change a • α=u at hau
    have haβ : a • β=β := sylowGenerated_le _ ha
    have hyt : (graph F).Adj α (a⁻¹ • y) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F a⁻¹).map_adj_iff.mpr hy
      change (graph F).Adj (a⁻¹ • u) (a⁻¹ • y) at hh
      simpa only [←hau,inv_smul_smul] using hh
    have hytn : a⁻¹ • y≠β := by
      intro he
      have hh := congrArg (a • ·) he
      rw [smul_inv_smul,haβ] at hh
      exact hyne hh
    have hcenters : Z F α=Z F β⊔Z F (a⁻¹ • y) :=
      (c.central_neighbor_centers H (reduced_borel_core_sylow h)
        (reduced_vertex_sylow h) hb hactor hcentral hyt hytn).1
    have hh := congrArg (map (MulAut.conj a).toMonoidHom) hcenters
    rwa [Subgroup.map_sup,←Z_translate,←Z_translate,←Z_translate,hau,haβ,smul_inv_smul] at hh
  have hZuQ : ¬Z F u≤Q F δ := by
    intro hh
    have he : Z F u=Z F β := (inf_eq_left.mpr hh).symm.trans hinter
    have hm := congrArg (map ι) he
    have hZuc : Nat.card ((Z F u).map ι)=4 := by
      have ht := congrArg (fun A : Subgroup (G₀ L S) => Nat.card (A.map ι))
        (Z_translate F x α)
      rw [hxu,←image_conj,card_map_of_injective (f:=(MulAut.conj (ι x)).toMonoidHom) (MulAut.conj (ι x)).injective] at ht
      exact ht.trans hZa
    rw [hm,hZb] at hZuc
    contradiction
  have hZyδ : ¬Z F y≤Q F δ := by
    intro hh
    apply hZuQ
    rw [hZu]
    exact sup_le (graph_Z_le_Q_of_short H (reduced_kernel_sylow h)
      (by change (graph F).dist β δ<b F; rw [SimpleGraph.dist_eq_one_iff_adj.mpr hδ,hb]; decide)) hh
  obtain ⟨z,hz,hzn⟩ := SetLike.not_le_iff_exists.mp hZyδ
  have hZyZu : Z F y≤Z F u := hZu ▸ le_sup_right
  have hZyβ : Z F y≤Q F β := hZyZu.trans
    (graph_Z_le_Q_of_short H (reduced_kernel_sylow h)
      (by change (graph F).dist u β<b F; rw [SimpleGraph.dist_eq_one_iff_adj.mpr hβu.symm,hb]; decide))
  have hQβδ : Q F β≤stabilizer F δ :=
    (source_Z_Q_U H β).2.trans ((ballKernel_one_le_edge F hδ).trans inf_le_right)
  have hQβL : Q F β≤graphLocalGroup F β :=
    pGroup_le_sylowGenerated _ _ (Q_le_stabilizer F β) (isPGroup_pCoreIn 2 _)
  have hzE : z∈E := ⟨hQβL (hZyβ hz),hQβδ (hZyβ hz)⟩
  have hxE : x∈E := ⟨hx,hxδ⟩
  have hcorrect : ∃ z'∈Z F y, x*z'∈Q F δ := by
    by_cases hxδQ : x∈Q F δ
    · exact ⟨1,one_mem _,by simpa only [mul_one] using hxδQ⟩
    · refine ⟨z,hz,?_⟩
      have hh : (⟨x,hxE⟩:E)*⟨z,hzE⟩∈(Q F δ).subgroupOf E := by
        rw [mul_mem_iff_of_index_two hindex]
        change x∈Q F δ ↔ z∈Q F δ
        simp only [hxδQ,hzn]
      exact hh
  obtain ⟨z',hz',hxz⟩ := hcorrect
  have hxzC : ι (x*z')∈centralizer (Δ:Set G) := by
    rw [map_mul]
    exact (centralizer (Δ:Set G)).mul_mem hxΔ.2 (hZyC (mem_map_of_mem ι hz'))
  have hRne : R≠⊥ := by intro hh; rw [hh,card_bot] at hRc; contradiction
  obtain ⟨r,hr,hr1⟩ := R.bot_or_exists_ne_one.resolve_left hRne
  have hrδ : r∉(Q F δ).map ι := fun hh => hr1 (mem_bot.mp (hsep ▸ ⟨hr,hh⟩))
  have hxzQ : ι (x*z')∈Q₁ := hCbound r hr.1.1 hrδ
    ⟨mem_map_of_mem ι hxz,mem_centralizer_singleton_iff.mpr (hxzC r (mem_sup_left hr)).symm⟩
  apply hxQ
  have hz'Q : ι z'∈Q₁ := hQbm ▸ mem_map_of_mem ι (hZyβ hz')
  have hh := Q₁.mul_mem hxzQ (Q₁.inv_mem hz'Q)
  simpa only [map_mul,mul_inv_cancel_right] using hh

/-- DGS (10.8) for the binary beta quotient, covering both exceptional and
strict cores. The natural center action is constructed from the original
F1.11 hypotheses; no core equality or separation is an input. -/
theorem original_bTwo_binary_terminal_separation
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e : (L 1 ⧸ pCore 2 (L 1))≃*PSL(2,K)) (hK : Nat.card K=2) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      Nat.card R₀≤2 ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠β → R₀⊓(Q F y).map ι=⊥ := by
  classical
  by_cases hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι=(Z F α).map ι
  · have hab : (graph F).Adj α β :=
      ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
    obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
      reduced_bTwo_center_action_exists h hc hne hb hab hβu
    change BTwoCenterActionData F α β u k (Fin 2 → k) at c
    change c.actor=graphLocalGroup F α at hactor
    have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
    subst alg
    let : Algebra (ZMod 2) k := ZMod.algebra k 2
    have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
    obtain ⟨g,hgt,_,_,_,_,_,hiff⟩ := original_bTwo_residual_structure h hb c hactor
      hcentral (LinearEquiv.refl _ _) ht htne
    have hR := hiff.mp hD
    refine ⟨g,hactor ▸ g.property,hgt,?_,?_⟩
    · rw [hR,card_bot]
      decide
    · intro y hy hyne
      rw [hR,bot_inf_eq]
  · obtain ⟨g,hg,hgt,hRc,hsep⟩ := original_bTwo_binary_strict_terminal_separation
      h hc hne hb hβu ht htne e hK hD
    exact ⟨g,hg,hgt,hRc.le,hsep⟩

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
