module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourThirdRoot
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearNeighborOrbits
public import Theory.GroupTheory.CubicInvolutionNorm
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoNonbinaryTerminalReduction

/-!
# Terminal-core separation with binary alpha

The remaining field-four case in DGS (10.8) requires placing the tested
residual involution in the alpha core fixed by the terminal cubic. The
cubic moves the original alpha neighbor. A noncentral involution in that
neighbor's center and its two cubic conjugates have the same nontrivial
central commutator. Their product is cubic-fixed and has nontrivial square.

Inside the beta core, the new alpha core has index two. Its cubic-fixed
elements lie in the literal D subgroup by (10.7), hence square to one.
If the tested involution were outside this core, multiplying it by the
cubic-fixed product would contradict that exponent-two assertion. This
proves the missing placement and the existing third-root bound finishes
the contradiction.

The actual application retains the original completion inclusion, both
root factors, the full radius-one kernel and the same opposite-center
conjugator. Combining it with the previously proved other beta fields
and the exceptional residual-zero case gives terminal separation for
every binary-alpha branch. Nonbinary alpha and the remaining Chapter 10
residual, path and representation clauses are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.2), (10.7)--(10.8), printed pp.154,159--161; the involution-product
argument expands the core-placement inference on p.161.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
private theorem centralizes_of_index_two {A : Type*} [Group A]
    (N B : Subgroup A) (hidx : N.relIndex B=2)
    (a : A) (ha : a∈B) (hao : a∉N)
    (x : A) (hxN : x∈centralizer (N:Set A)) (hxa : Commute x a) :
    x∈centralizer (B:Set A) := by
  intro b hb
  by_cases hn : b∈N
  · exact hxN b hn
  have hh : (⟨b,hb⟩:B)*(⟨a,ha⟩:B)⁻¹∈N.subgroupOf B :=
    (mul_mem_iff_of_index_two hidx).mpr (by rw [inv_mem_iff]; exact iff_of_false hn hao)
  have hc : Commute (b*a⁻¹) x := hxN _ hh
  simpa only [inv_mul_cancel_right] using (hc.mul_left hxa.symm).eq

namespace Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
variable {k : Type u} [Field k] [Finite k] [CharP k 2]
local instance placementAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem moving_cubic_involution_core
    (h : HypothesisF11 L S) {u δ : Vertex F}
    (c : BTwoCenterActionData F α β u k (Fin 2 → k))
    (hactor : c.actor=graphLocalGroup F α) (hb : b F=2)
    (hc : IsCriticalPair F α u)
    (hcentral : Z F β≤centerIn (graphLocalGroup F β))
    (hk : Nat.card k=2)
    (e : (L 1⧸pCore 2 (L 1))≃*SL(2,K))
    (hder : ⁅Q F β,Q F β⁆=Z F β)
    (hδ : (graph F).Adj β δ) (hδα : δ≠α)
    (d : G₀ L S) (hd : d∈graphLocalGroup F β) (hd3 : d^3=1)
    (hdf : d • δ=δ) (hdmove : d • α≠α)
    (hfixed : ∀ z∈Q F δ, Commute z d → z^2=1)
    (x : G₀ L S) (hxβ : x∈Q F β) (hxα : x∈Q F α)
    (hx2 : x^2=1) (hxd : Commute x d) : x∈Q F δ := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  have hZa : Nat.card (Z F α)=4 := by
    have hh := c.central_center_card (LinearEquiv.refl _ _) hω
    change Nat.card (Z F α)=Nat.card k^2 at hh
    simpa [hk] using hh
  have hZb : Nat.card (Z F β)=2 :=
    (c.central_middle_center_card H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral (LinearEquiv.refl _ _)).trans hk
  have hZQ := (c.central_critical_intersections H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hcentral).1
  change Z F α⊓Q F u=Z F β at hZQ
  have hZC : Z F α⊓centralizer (Z F u:Set (G₀ L S))=Z F β :=
    c.centralizer_intersection.trans hZQ
  have hub : u≠α := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    contradiction
  have pair (v : Vertex F) (hv : (graph F).Adj β v) (hvα : v≠α) :
      Z F α⊓Q F v=Z F β ∧
      Z F α⊓centralizer (Z F v:Set (G₀ L S))=Z F β := by
    obtain ⟨g,hg,hgu⟩ := CommutingThreeProfile.ReducedLayer.linear_incident_core_transitive
      h true e c.middle.symm c.terminal hv hub hvα
    have hga : g • α=α := ((pCoreIn_le 2 _) hg).1
    have hgb : g • β=β := ((pCoreIn_le 2 _) hg).2
    have hq := congrArg (map (MulAut.conj g).toMonoidHom) hZQ
    have hz := congrArg (map (MulAut.conj g).toMonoidHom) hZC
    rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate,
      ←Z_translate,hga,hgb,hgu] at hq
    rw [←map_inf_centralizer_of_injective _ (MulAut.conj g).injective,
      ←Z_translate,←Z_translate,←Z_translate,hga,hgb,hgu] at hz
    exact ⟨hq,hz⟩
  have hdβ : d • β=β := sylowGenerated_le _ hd
  have hdα : (graph F).Adj β (d • α) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F d).map_adj_iff.mpr c.middle.symm
    change (graph F).Adj (d • β) (d • α) at hh
    rwa [hdβ] at hh
  obtain ⟨s,hs,hsδ⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) β ⟨α,c.middle.symm⟩ ⟨δ,hδ⟩
  change s • α=δ at hsδ
  have hsβ : s • β=β := sylowGenerated_le _ hs
  have hindex : (Q F α).relIndex (Q F β)=2 := by
    have hh := relIndex_ker (K := (Q F β).subgroupOf c.actor) c.quotient
    rw [c.kernel,relIndex_subgroupOf c.neighbor_core_le,c.neighbor_image] at hh
    exact hh.trans ((Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).toEquiv).symm.trans hk)
  have hi : (Q F δ).relIndex (Q F β)=2 := by
    have hh := relIndex_map_map_of_injective (f:=(MulAut.conj s).toMonoidHom)
      (Q F α) (Q F β) (MulAut.conj s).injective
    rwa [←Q_translate,←Q_translate,hsδ,hsβ,hindex] at hh
  have hab : (graph F).Adj α β := c.middle
  have hZab : Z F α≤Q F β := graph_Z_le_Q_of_short H (reduced_kernel_sylow h)
    (by change (graph F).dist α β<b F; rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab,hb]; decide)
  let : Finite (Z F β) := Nat.finite_of_card_ne_zero (by rw [hZb]; decide)
  obtain ⟨a,ha,hao⟩ := SetLike.not_le_iff_exists.mp
    (show ¬Z F α≤Z F β from fun hl => by
      have hh := Nat.card_le_card_of_injective (inclusion hl) (inclusion_injective hl)
      rw [hZa,hZb] at hh
      omega)
  have haδ : a∉Q F δ := fun haδ => hao ((pair δ hδ hδα).1 ▸ ⟨ha,haδ⟩)
  have ha2 : a^2=1 := by
    let : IsElementaryAbelian 2 (Z F α) := graph_Z_elementary H α
    exact elemPow_eq_one_of_isElementaryAbelian a ha
  let f : MulAut (Q F β) := (Q F β).normalizerMonoidHom
    ⟨d,CommutingNontrivial.stabilizer_normalizes_Q F β hdβ⟩
  let a₀ : Q F β := ⟨a,hZab ha⟩
  let x₀ : Q F β := ⟨x,hxβ⟩
  let I := (Q F δ).subgroupOf (Q F β)
  have hf3 : f^3=1 := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change ((MulAut.conj d)^3) z.val=z.val
    rw [←map_pow,hd3,map_one]
    rfl
  have hfI (z : Q F β) : f z∈I ↔ z∈I := by
    change d*z.val*d⁻¹∈Q F δ ↔ z.val∈Q F δ
    exact (mem_normalizer_iff.mp (CommutingNontrivial.stabilizer_normalizes_Q F δ hdf) z.val).symm
  have hfix (z : Q F β) (hz : z∈I) (hfz : f z=z) : z^2=1 := by
    apply Subtype.ext
    apply hfixed z.val hz
    have hh : d*z.val*d⁻¹=z.val := congrArg Subtype.val hfz
    exact (show Commute d z.val from mul_inv_eq_iff_eq_mul.mp hh).symm
  have hfx : f x₀=x₀ := Subtype.ext (by
    change d*x*d⁻¹=x
    rw [hxd.symm.eq,mul_inv_cancel_right])
  have hxa : Commute x₀ a₀ := Subtype.ext (graph_Q_centralizes_Z H α hxα a ha).symm
  have hfa : d*a*d⁻¹∈Z F (d • α) := by
    rw [Z_translate]
    exact mem_map_of_mem (MulAut.conj d).toMonoidHom ha
  have hfan : d*a*d⁻¹∉Z F β := by
    intro hh
    have hn := CommutingNontrivial.stabilizer_normalizes_Z F β hdβ
    exact hao ((mem_normalizer_iff.mp hn a).mpr hh)
  have hZi : (Z F β).relIndex (Z F (d • α))=2 := by
    have hzidx : (Z F β).relIndex (Z F α)=2 := by
      have hi := c.line_index (LinearEquiv.refl _ _)
      rw [←hZQ,inf_relIndex_left]
      exact hi.trans hk
    have hh := relIndex_map_map_of_injective (f:=(MulAut.conj d).toMonoidHom)
      (Z F β) (Z F α) (MulAut.conj d).injective
    rwa [←Z_translate,←Z_translate,hdβ,hzidx] at hh
  let z₀ : Q F β := ⁅a₀,f a₀⁆
  have hzmem : z₀.val∈Z F β := hder ▸
    commutator_mem_commutator a₀.property (f a₀).property
  have hzne : z₀≠1 := by
    intro he
    have hac : Commute a (d*a*d⁻¹) :=
      commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val he)
    have hcent : a∈centralizer (Z F (d • α):Set (G₀ L S)) :=
      centralizes_of_index_two (Z F β) (Z F (d • α)) hZi _ hfa hfan a
        (graph_Q_centralizes_Z H β a₀.property) hac
    exact hao ((pair (d • α) hdα hdmove).2 ▸ ⟨ha,hcent⟩)
  have hfz : f z₀=z₀ := Subtype.ext (by
    change d*z₀.val*d⁻¹=z₀.val
    rw [(hcentral hzmem).2 d hd,mul_inv_cancel_right])
  have hza : Commute z₀ (f a₀) :=
    Subtype.ext (graph_Q_centralizes_Z H β (f a₀).property z₀.val hzmem)
  exact cubic_fixed_involution_mem_index_two I hi f hf3 hfI hfix x₀ a₀ z₀
    (Subtype.ext hx2) hfx hxa (Subtype.ext ha2) haδ hzne rfl hfz hza

private theorem alpha_field_card
    {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (h : HypothesisF11 L S) {u : Vertex F}
    (c : BTwoCenterActionData F α β u k (Fin 2 → k))
    (hactor : c.actor=graphLocalGroup F α)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) : Nat.card k=Nat.card K₀ := by
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hc : pCore 2 c.actor=(Q F α).subgroupOf c.actor := by
    apply map_injective c.actor.subtype_injective
    rw [map_subgroupOf_eq_of_le c.core_le]
    change c.actor.pCoreIn 2=_
    rw [hactor]
    exact sylowGenerated_core (stabilizer F α)
  let ec : (c.actor⧸pCore 2 c.actor)≃*SL(2,k) :=
    (QuotientGroup.quotientMulEquivOfEq (hc.trans c.kernel.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto)
  let ea : (c.actor⧸pCore 2 c.actor)≃*SL(2,K₀) := by
    rw [hactor]
    exact (reduced_graphLinearQuotient h false e₀).trans
      (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K₀)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  exact Matrix.SL2.field_card_eq_of_equiv (ec.symm.trans ea)

/-- The field-four terminal separation, with the literal original residual
and one opposite-center conjugator. The cubic norm supplies the missing
core placement before the third-root contradiction is applied. -/
theorem original_bTwo_field_four_strict_terminal_separation
    {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K)) (hK : Nat.card K=4)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map (G₀ L S).subtype≠
      (Z F α).map (G₀ L S).subtype) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let ι := (G₀ L S).subtype
      let D₀ := (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      ∀ y : Vertex F, (graph F).Adj u y → y≠β → R₀⊓(Q F y).map ι=⊥ := by
  obtain ⟨g,hg,hgt,hW,hfour,hRne,hcubic⟩ :=
    original_bTwo_field_four_terminal_third_root_moving h hc hne hb hβu ht htne e₀ hK₀ e hK hD
  refine ⟨g,hg,hgt,?_⟩
  dsimp only
  intro y hy hyne
  apply bot_unique
  intro x hx
  by_contra hxne
  have hx1 : x≠1 := fun he => hxne (he ▸ one_mem _)
  obtain ⟨d,hd,hdo,_,_,hdx,δ,hδ,hδα,hdk,hdmove,hbound,hout,hact⟩ :=
    hcubic y hy hyne x hx hx1
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let ι := (G₀ L S).subtype
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  change BTwoCenterActionData F α β u k (Fin 2 → k) at c
  change c.actor=graphLocalGroup F α at hactor
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk : Nat.card k=2 := (alpha_field_card h c hactor e₀).trans hK₀
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  obtain ⟨_,_,hDQ,_,hDel,_⟩ := c.central_D_structure H (reduced_kernel_sylow h) hb hω ht htne
  change Q F β⊓Q F t≤Q F α at hDQ
  change IsElementaryAbelian 2 (↥(Q F β⊓Q F t)) at hDel
  have hQbm : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  obtain ⟨r,hr,hrx⟩ := show x∈(Q F β).map ι from hQbm.symm ▸ hx.1.1.1
  have hrt : r∈Q F t := by
    obtain ⟨z,hz,hzx⟩ := hx.1.1.2
    exact (G₀ L S).subtype_injective (hzx.trans hrx.symm) ▸ hz
  have hrα : r∈Q F α := hDQ ⟨hr,hrt⟩
  have hr2 : r^2=1 := by
    let := hDel
    exact elemPow_eq_one_of_isElementaryAbelian r (show r∈Q F β⊓Q F t from ⟨hr,hrt⟩)
  have hrd : Commute r d := by
    apply (G₀ L S).subtype_injective
    rw [map_mul,map_mul,hrx]
    exact (mem_centralizer_singleton_iff.mp hdx).symm
  obtain ⟨s,hs,hsδ⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) β ⟨α,hab.symm⟩ ⟨δ,hδ⟩
  change s • α=δ at hsδ
  have hsβ : s • β=β := sylowGenerated_le _ hs
  let ρ := s • t
  have hδρ : (graph F).Adj δ ρ := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F s).map_adj_iff.mpr ht
    change (graph F).Adj (s • α) (s • t) at hh
    rwa [hsδ] at hh
  have hDm : (Q F β⊓Q F t).map (MulAut.conj s).toMonoidHom=Q F β⊓Q F ρ := by
    rw [map_inf _ _ _ (MulAut.conj s).injective,←Q_translate,←Q_translate,hsβ]
  have hDeδ : IsElementaryAbelian 2 (↥(Q F β⊓Q F ρ)) := by
    let := hDel
    rw [←hDm]
    exact IsElementaryAbelian.map _
  have hfixed (z : G₀ L S) (hz : z∈Q F δ) (hzd : Commute z d) : z^2=1 := by
    have hh := (hact ρ hδρ).2 (ι z) (mem_map_of_mem ι hz) (by
      rw [←map_commutatorElement,commutatorElement_eq_one_iff_mul_comm.mpr hzd.eq,map_one]
      exact one_mem _)
    have hzβ : z∈Q F β := by
      obtain ⟨a,ha,he⟩ := hQbm.symm ▸ hh.1
      exact (G₀ L S).subtype_injective he ▸ ha
    have hzρ : z∈Q F ρ := by
      obtain ⟨a,ha,he⟩ := hh.2
      exact (G₀ L S).subtype_injective he ▸ ha
    let := hDeδ
    exact elemPow_eq_one_of_isElementaryAbelian z (show z∈Q F β⊓Q F ρ from ⟨hzβ,hzρ⟩)
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hder : ⁅Q F β,Q F β⁆=Z F β :=
    (c.beta_core_frattini_eq H (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
      hb hactor hcentral ht htne hcomm).2
  let eβ := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hrδ := moving_cubic_involution_core h c hactor hb hc hcentral hk eβ hder hδ hδα
    d hd (hdo ▸ pow_orderOf_eq_one d) ((ballKernel_le_stabilizer F δ 1) hdk)
    hdmove hfixed r hr hrα hr2 hrd
  exact hout (hrx ▸ mem_map_of_mem ι hrδ)

/-- Terminal separation in every binary-alpha branch, including the
nonbinary beta fields and the exceptional residual-zero case. -/
theorem original_bTwo_alpha_binary_terminal_separation
    {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K)) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let ι := (G₀ L S).subtype
      let D₀ := (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      ∀ y : Vertex F, (graph F).Adj u y → y≠β → R₀⊓(Q F y).map ι=⊥ := by
  classical
  by_cases hK : Nat.card K=4
  · by_cases hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map (G₀ L S).subtype=
        (Z F α).map (G₀ L S).subtype
    · have hab : (graph F).Adj α β :=
        ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
      obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
      change BTwoCenterActionData F α β u k (Fin 2 → k) at c
      change c.actor=graphLocalGroup F α at hactor
      have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
      subst alg
      let : Algebra (ZMod 2) k := ZMod.algebra k 2
      have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
      obtain ⟨g,hgt,_,_,_,_,_,hiff⟩ := original_bTwo_residual_structure h hb c hactor
        hcentral (LinearEquiv.refl _ _) ht htne
      have hR := hiff.mp hD
      refine ⟨g,hactor ▸ g.property,hgt,?_⟩
      dsimp only
      intro y hy hyne
      rw [hR,bot_inf_eq]
    · exact original_bTwo_field_four_strict_terminal_separation h hc hne hb hβu ht htne
        e₀ hK₀ e hK hD
  · exact original_bTwo_alpha_binary_terminal_separation_unless_four h hc hne hb hβu ht htne
      e₀ hK₀ e hK

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
