module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearModuleSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCentralApplication

/-!
# The original strict residual without nonsolvability

The source strict branch is D_alpha ≠ Z_alpha. Construct the marked
natural action, linear beta quotient and saturated core internally, then
choose one opposite-center lift. The same lift identifies the residual
with the four-core intersection and with C_Qalpha(W_alpha), and gives
D_alpha = Z_alpha × R_alpha by actual multiplication.

Unlike the nonsolvable specialization, this construction retains binary
fields: the exact strict source condition alone makes the residual
nontrivial. All original endpoint maps and the full reduced Borel
normalizers are preserved. The remaining (10.8) vanishing argument and
|R_alpha| = q_beta are still needed in the unrestricted strict branch.

Source: DGS, Groups and Graphs (1985), (10.4), (10.7)--(10.10),
printed pp.155--165. This extends the established nonsolvable calculation
in Assembly/BTwoResidual to the literal source case distinction.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

private theorem residual_base_adj : (graph F).Adj α β :=
  ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩

/-- The same opposite lift supplies the original residual, its whole-core
centralizer and direct product, and the exact original core-order formula. -/
theorem original_bTwo_strict_residual
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι ≠ (Z F α).map ι) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (_ : Algebra (ZMod 2) k),
      ∃ c : BTwoCenterActionData F α β u k (Fin 2 → k),
      c.actor = graphLocalGroup F α ∧ 1 < Nat.card k ∧
      ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
      (∃ r : ℕ, 0 < r ∧ 2^n = Nat.card k ^ r) ∧
      ∃ g : c.actor, (g : G₀ L S) • β = t ∧
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
      let Z₀ := (Z F α).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      W₀ ⊔ Q₀ = enlargedEndpoint L S 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F ((g : G₀ L S) • u)).map ι ∧
      Q₀ ⊓ centralizer (W₀ : Set G) = R₀ ∧
      R₀ ≠ ⊥ ∧ IsElementaryAbelian 2 D₀ ∧ IsElementaryAbelian 2 R₀ ∧
      D₀ = Z₀ ⊔ R₀ ∧ Disjoint Z₀ R₀ ∧
      (∃ e : Z₀ × R₀ ≃* D₀, ∀ z r, (e (z,r) : G) = (z : G) * (r : G)) ∧
      Nat.card Z₀ = Nat.card k ^ 2 ∧
      Nat.card D₀ = Nat.card k ^ 2 * Nat.card R₀ ∧
      Nat.card Q₀ = Nat.card k ^ 2 * (2^n)^2 * Nat.card R₀ ∧
      P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) := by
  obtain ⟨k,f,fin,ch,a,c,hactor,hext,n,hn,hm,hpow,hs,hnP,hnB,hN,hE,hcard⟩ :=
    DGS85.Reduction.original_bTwo_central_core_field h hc hne hb hβu ht htne
  change BTwoCenterActionData F α β u k (Fin 2 → k) at c
  change c.actor = graphLocalGroup F α at hactor
  have hk : 1 < Nat.card k := Finite.one_lt_card
  have ha : a = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst a
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb residual_base_adj hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb residual_base_adj hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β residual_base_adj
  let H := reduced_triple h
  have hS := reduced_kernel_sylow h
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift H ht htne
  obtain ⟨d,hd,hker⟩ := c.exists_oppositeGeometry H hS hb g hg hop
  have hωd : omegaCenterIn d.actor = ⊥ := hd.symm ▸ hω
  let W₁ := Z F u ⊔ Z F ((g : G₀ L S) • u)
  let R₁ := bTwoResidual F β t u ((g : G₀ L S) • u)
  have hres : d.residual = R₁ := d.residual_eq_source H hS hb hωd
  have hgen : W₁ ⊔ Q F α = c.actor := d.actor_generators.symm.trans hd
  have hdis : Disjoint d.residual (Z F α) := disjoint_iff.mpr
    (bot_unique (hker.trans hω.le))
  have hT : (c.sylow : Subgroup (stabilizer F α)).map (stabilizer F α).subtype ≤ d.actor :=
    hd.symm ▸ c.sylow_le_actor
  have hDel := d.elementary H hS hb c.sylow hT hdis
  have hdec : D F β t = Z F α ⊔ R₁ :=
    (d.decomposition H hS hb).trans (congrArg (Z F α ⊔ ·) hres)
  have hdisR : Disjoint (Z F α) R₁ := hres ▸ hdis.symm
  obtain ⟨e,he⟩ := d.direct_product H hS hb hωd
  have hz := c.central_center_card (LinearEquiv.refl _ _) hω
  obtain ⟨K,fK,finK,hK,⟨eK⟩⟩ := hm
  let := fK
  let := finK
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eβ := (reduced_graphLinearQuotient h true eK).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hwhole : Q F α ⊓ centralizer (W₁ : Set (G₀ L S)) = R₁ := by
    obtain ⟨hN',hE',σ,b,_,hglobal,_⟩ := c.linear_core_natural_copies H
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor
      hcentral ht htne hcomm.le hnot eβ
    let := hN'
    let := hE'
    have hWL : W₁ ≤ c.actor := le_sup_left.trans hgen.le
    have hfull : (W₁.subgroupOf c.actor).map c.quotient = ⊤ := by
      have hh := congrArg (fun A : Subgroup (G₀ L S) =>
        (A.subgroupOf c.actor).map c.quotient) hgen
      rw [subgroupOf_sup hWL c.core_le,Subgroup.map_sup,←c.kernel,
        Subgroup.map_ker_self,sup_bot_eq,subgroupOf_self,
        map_top_of_surjective _ c.onto] at hh
      exact hh
    apply le_antisymm ?_ (inf_le_inf_right _ d.separated)
    intro x hx
    refine ⟨?_,hx.2⟩
    have hfixed : (b.coordinates ⟨x,hx.1⟩).toAdd ∈ fixedSpace σ ⊤ := by
      intro y
      obtain ⟨z,hz',hy⟩ := (show y.val ∈ (W₁.subgroupOf c.actor).map c.quotient from
        hfull.symm ▸ mem_top _)
      change σ y.val (b.coordinates ⟨x,hx.1⟩).toAdd = _
      rw [←hy]
      apply (b.fixed_coordinate_iff_commutator_mem z ⟨x,hx.1⟩).mpr
      have hcommute : Commute x (z : G₀ L S) := (hx.2 z hz').symm
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcommute.eq]
      exact one_mem _
    have hx0 : (b.coordinates ⟨x,hx.1⟩).toAdd = 0 := by
      simpa only [hglobal,Submodule.mem_bot] using hfixed
    exact (b.coordinates_eq_one_iff ⟨x,hx.1⟩).mp (Multiplicative.toAdd.injective hx0)
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
  let Z₀ := (Z F α).map ι
  let W₀ := (Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι
  let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
  have hQm : (Q F α).map ι = Q₀ := reduced_base_Q_map h false
  have hDm : (D F β t).map ι = D₀ := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hRm : R₁.map ι = R₀ := by
    change ((D F β t ⊓ centralizer (W₁ : Set (G₀ L S))).map ι) = _
    rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,
      hDm,show W₁.map ι = W₀ from Subgroup.map_sup _ _ _]
  have hdec₀ : D₀ = Z₀ ⊔ R₀ := by
    have hh := congrArg (map ι) hdec
    rwa [hDm,Subgroup.map_sup,hRm] at hh
  have hRne : R₀ ≠ ⊥ := by
    intro hh
    exact hD (by simpa only [hh,sup_bot_eq] using hdec₀)
  have hDel₀ : IsElementaryAbelian 2 D₀ := by
    rw [←hDm]
    let : IsElementaryAbelian 2 (D F β t) := hDel
    exact IsElementaryAbelian.map _
  have hRel₀ : IsElementaryAbelian 2 R₀ := by
    let := hDel₀
    exact IsElementaryAbelian.of_injective (inclusion (show R₀ ≤ D₀ from inf_le_left))
      (inclusion_injective _)
  let eZ := (Z F α).equivMapOfInjective ι (G₀ L S).subtype_injective
  let eR : R₁ ≃* R₀ := (R₁.equivMapOfInjective ι (G₀ L S).subtype_injective).trans
    (MulEquiv.subgroupCongr hRm)
  let eD : D F β t ≃* D₀ := ((D F β t).equivMapOfInjective ι
    (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr hDm)
  let e₀ : Z₀ × R₀ ≃* D₀ := (eZ.symm.prodCongr eR.symm).trans (e.trans eD)
  have he₀ : ∀ z r, (e₀ (z,r) : G) = (z : G) * (r : G) := by
    intro z r
    change ι (e (eZ.symm z,eR.symm r)) = _
    have he' : (e (eZ.symm z,eR.symm r) : G₀ L S) =
        (eZ.symm z : G₀ L S) * (eR.symm r : G₀ L S) := he _ _
    rw [he', map_mul]
    have hZ : ι (eZ.symm z) = (z : G) := congrArg Subtype.val (eZ.apply_symm_apply z)
    have hR : ι (eR.symm r) = (r : G) := congrArg Subtype.val (eR.apply_symm_apply r)
    rw [hZ,hR]
  have hZcard : Nat.card Z₀ = Nat.card k ^ 2 := by
    rw [show Z₀ = (Z F α).map ι from rfl,card_map_of_injective (G₀ L S).subtype_injective]
    exact hz
  have hDcard : Nat.card D₀ = Nat.card k ^ 2 * Nat.card R₀ := by
    rw [←Nat.card_congr e₀.toEquiv,Nat.card_prod,hZcard]
  have hDQ : D₀ ≤ Q₀ := by
    rw [←hDm,←hQm]
    exact map_mono d.separated
  have hQcard : Nat.card Q₀ = Nat.card k ^ 2 * (2^n)^2 * Nat.card R₀ := by
    let := hN
    have hcount := card_eq_card_quotient_mul_card_subgroup (D₀.subgroupOf Q₀)
    rw [Nat.card_congr (subgroupOfEquivOfLe hDQ).toEquiv,hDcard] at hcount
    change Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^n)^2 at hcard
    rw [hcard] at hcount
    exact hcount.trans (by ring)
  refine ⟨k,f,fin,ch,inferInstance,c,hactor,hk,n,hn,⟨K,fK,finK,hK,⟨eK⟩⟩,
    hpow,g,hg,?_,?_,?_,hRne,hDel₀,hRel₀,hdec₀,?_,⟨e₀,he₀⟩,hZcard,hDcard,hQcard,hnP,hnB⟩
  · have hh := congrArg (map ι) hgen
    rw [Subgroup.map_sup,hQm,hactor,reduced_graphLocalGroup_image h false] at hh
    rw [show W₁.map ι = W₀ from Subgroup.map_sup _ _ _] at hh
    exact hh
  · have hh := congrArg (map ι) hres.symm
    change R₁.map ι = ((D F β t ⊓ Q F u) ⊓ Q F ((g : G₀ L S) • u)).map ι at hh
    rwa [hRm,map_inf _ _ _ (G₀ L S).subtype_injective,
      map_inf _ _ _ (G₀ L S).subtype_injective,hDm] at hh
  · have hh := congrArg (map ι) hwhole
    rwa [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,
      hQm,hRm,show W₁.map ι = W₀ from Subgroup.map_sup _ _ _] at hh
  · change Disjoint Z₀ R₀
    rw [←hRm]
    exact Subgroup.disjoint_map (G₀ L S).subtype_injective hdisR

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
