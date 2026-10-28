module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidualSeparationSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingCatalogue
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Endpoint-core pairing for the strict binary branch

The commutator pairing of the residual with the alpha endpoint-core quotient is
faithful once the residual has trivial intersection with the corresponding
centralizer.  In the original completion this gives the literal consequence
`R_alpha intersect C(Q_alpha intersect Q_beta) = 1`, retaining the full
endpoint cores and the reduced-to-original inclusion.  This is an input to the
remaining (10.8) local-action case split. The source application supplies its
markings and elementary core internally, then gives terminal displacement and
centralization for every continuation using this same residual. It does not
assert the vanishing of `R_alpha intersect Q_(alpha'+1)`.

Source: DGS (1985), (10.2)(c), (10.4), and the first pairing step in (10.8),
printed pp.154--160.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative MatrixGroups
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)
local instance pairingAlgebra {K : Type*} [Field K] [CharP K 2] :
    Algebra (ZMod 2) K := ZMod.algebra K 2

private theorem residual_centralizer_bot
    {H : Type*} [Group H] (L₀ Q I W R : Subgroup H) (g : H)
    (hL : L₀ = W ⊔ Q) (hg : g ∈ L₀)
    (hgen : I ⊔ I.conjBy g = Q)
    (hQI : Q ≤ normalizer (I : Set H))
    (hWQ : W ≤ normalizer (Q : Set H))
    (hRQ : R ≤ Q) (hRW : R ≤ centralizer (W : Set H))
    (hR2 : ∀ r ∈ R, r ^ 2 = 1) (hω : omegaCenterIn L₀ = ⊥) :
    R ⊓ centralizer (I : Set H) = ⊥ := by
  apply bot_unique
  intro r hr
  let C := centralizer ({r} : Set H)
  have hWC : W ≤ C := fun w hw =>
    mem_centralizer_singleton_iff.mpr (hRW hr.1 w hw)
  have hIC : I ≤ C := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hr.2 x hx)
  have hprod : g ∈ (W : Set H) * (Q : Set H) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hWQ, ← hL]
    exact hg
  obtain ⟨w, hw, q, hq, rfl⟩ := hprod
  have hJC : I.conjBy (w * q) ≤ C := by
    rintro x ⟨i, hi, rfl⟩
    have hqi : q * i * q⁻¹ ∈ I :=
      (mem_normalizer_iff.mp (hQI hq) i).mp hi
    have hh := C.mul_mem (C.mul_mem (hWC hw) (hIC hqi)) (C.inv_mem (hWC hw))
    change (w * q) * i * (w * q)⁻¹ ∈ C
    simpa only [mul_inv_rev, mul_assoc] using hh
  have hQC : Q ≤ C := hgen ▸ sup_le hIC hJC
  have hLC : L₀ ≤ C := hL ▸ sup_le hWC hQC
  have hrL : r ∈ L₀ := hL ▸ mem_sup_right (hRQ hr.1)
  have hrC : r ∈ centralizer (L₀ : Set H) := fun a ha =>
    mem_centralizer_singleton_iff.mp (hLC ha)
  exact hω ▸ (mem_omegaCenterIn_iff _ _).mpr ⟨hrL, hrC, hR2 r hr.1⟩

/-- The original endpoint residual has no nontrivial element centralizing the
two-core intersection of the two selected endpoints. -/
theorem original_bTwo_residual_endpoint_centralizer
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u)
    (hne : ⁅Z F α, Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    {k : Type u} [Field k] [Finite k] [CharP k 2]
    (c : BTwoCenterActionData F α β u k (Fin 2 → k))
    (hactor : c.actor = graphLocalGroup F α)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (eβ : (graphLocalGroup F β ⧸ pCore 2 (graphLocalGroup F β)) ≃* SL(2,K))
    (g : c.actor) (hg : (g : G₀ L S) • β = t)
    (hgen : ((Z F u).map ι ⊔
      (Z F ((g : G₀ L S) • u)).map ι) ⊔
      (parabolic L S 0).pCoreIn 2 = enlargedEndpoint L S 0)
    (hD : IsElementaryAbelian 2
      (↥((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι : Subgroup G))) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F t).map ι
    let W₀ := (Z F u).map ι ⊔
      (Z F ((g : G₀ L S) • u)).map ι
    let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
    R₀ ⊓ centralizer ((Q₀ ⊓ Q₁ : Subgroup G) : Set G) = ⊥ := by
  let H := reduced_triple h
  have hS := reduced_kernel_sylow h
  have hcentral := reduced_bTwo_middle_central h hc hne hb
    (by exact ⟨by change false ≠ true; decide,
      Subgroup.CosetGeometry.incident_base _ _ _⟩) hβu
  have hnot := reduced_graph_core_obstruction h α β
    (by exact ⟨by change false ≠ true; decide,
      Subgroup.CosetGeometry.incident_base _ _ _⟩)
  have hω := c.omega_eq_bot_of_central_neighbor H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hactor hcentral
  let I := Q F α ⊓ Q F β
  let A := Z F u ⊔ Z F ((g : G₀ L S) • u)
  let R := bTwoResidual F β t u ((g : G₀ L S) • u)
  have hgenL : c.actor = A ⊔ Q F α := by
    apply map_injective (G₀ L S).subtype_injective
    rw [Subgroup.map_sup, reduced_base_Q_map h false, hactor,
      reduced_graphLocalGroup_image h false]
    simpa only [A, Subgroup.map_sup, family, Bool.false_eq_true, ↓reduceIte,
      enlargedEndpoint] using hgen.symm
  have hAL : A ≤ c.actor := le_sup_left.trans hgenL.ge
  have hnQ : c.actor ≤ normalizer (Q F α : Set (G₀ L S)) :=
    c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F α)
  have hnI : Q F α ≤ normalizer (I : Set (G₀ L S)) :=
    (le_inf (Q F α).le_normalizer
      (((source_Z_Q_U H α).2.trans
        ((ballKernel_one_le_edge F c.middle).trans inf_le_right)).trans
          (CommutingNontrivial.stabilizer_normalizes_Q F β))).trans
      inf_normalizer_le_normalizer_inf
  have hs := (c.linear_seed_eq_core_and_index H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hS hb ht htne hnot eβ).1
  have hgv : (g : G₀ L S) • α = α := c.actor_le g.property
  have hgenQ : I ⊔ I.conjBy (g : G₀ L S) = Q F α := by
    dsimp only [I]
    rw [conjBy, map_inf _ _ _ (MulAut.conj (g : G₀ L S)).injective,
      ← Q_translate, ← Q_translate, hgv, hg]
    exact (c.seed_eq_core_intersections H hS hb ht htne).symm.trans hs
  obtain ⟨a, ha, hop⟩ := c.exists_opposite_lift H ht htne
  obtain ⟨d, _, _⟩ := c.exists_oppositeGeometry H hS hb a ha hop
  have hRQ : R ≤ Q F α := inf_le_left.trans d.separated
  have hRm : R.map ι =
      ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι) ⊓
        centralizer (((Z F u).map ι ⊔
          (Z F ((g : G₀ L S) • u)).map ι : Subgroup G) : Set G) := by
    change ((D F β t ⊓ centralizer (A : Set (G₀ L S))).map ι) = _
    rw [← map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,
      show D F β t = Q F β ⊓ Q F t from rfl,
      map_inf _ _ _ (G₀ L S).subtype_injective, reduced_base_Q_map h true,
      Subgroup.map_sup]
    rfl
  have hR2 (r : G₀ L S) (hr : r ∈ R) : r ^ 2 = 1 := by
    apply (G₀ L S).subtype_injective
    let _ := hD
    have hm := mem_map_of_mem ι hr.1
    change ι r ∈ (D F β t).map ι at hm
    change ι r ∈ (Q F β ⊓ Q F t).map ι at hm
    rw [map_inf _ _ _ (G₀ L S).subtype_injective, reduced_base_Q_map h true] at hm
    simp only [↓reduceIte] at hm
    simpa only [map_pow, map_one] using
      elemPow_eq_one_of_isElementaryAbelian (ι r) hm
  have hfix := residual_centralizer_bot c.actor (Q F α) I A R
    (g : G₀ L S) hgenL g.property hgenQ hnI (hAL.trans hnQ) hRQ
    inf_le_right hR2 hω
  have hm := congrArg (map ι) hfix
  rw [← map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,
    hRm, Subgroup.map_bot] at hm
  have hIm : I.map ι =
      (parabolic L S 0).pCoreIn 2 ⊓ (parabolic L S 1).pCoreIn 2 := by
    dsimp only [I]
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,
      reduced_base_Q_map h false, reduced_base_Q_map h true]
    rfl
  dsimp only
  simpa only [hIm] using hm

private theorem original_terminal_core_control
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α, Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    {R₀ : Subgroup G} (hRQ : R₀ ≤ (parabolic L S 1).pCoreIn 2)
    (hdis : Disjoint R₀ ((Z F u).map ι))
    {y : Vertex F} (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    let J₀ := R₀ ⊓ (Q F y).map ι
    let A₀ := ((pResidual 2 (graphLocalGroup F u)).map
      (graphLocalGroup F u).subtype).map ι
    let Z' := (Z F u).map ι
    J₀ ≤ (parabolic L S 1).pCoreIn 2 ⊓ (Q F y).map ι ∧
      Disjoint J₀ Z' ∧ ⁅J₀,A₀⁆ ≤ Z' ∧
      J₀ ≤ centralizer ((A₀ ⊓ normalizer (J₀ : Set G) : Subgroup G) : Set G) := by
  obtain ⟨k₀,f₀,n₀,ch₀,a₀,k₁,f₁,n₁,ch₁,a₁,c₀,c₁,ha₀,ha₁,_,_,_⟩ :=
    Reduction.reduced_bTwo_equal_field_profile_actions h hc hne hb
      (by exact ⟨by change false ≠ true; decide,
        Subgroup.CosetGeometry.incident_base _ _ _⟩) hβu
  have hmove := c₁.D_residual_commutator_le_center (reduced_triple h)
    (reduced_kernel_sylow h) hb hy hyne
  change ⁅D F β y, (pResidual 2 c₁.actor).map c₁.actor.subtype⁆ ≤ Z F u at hmove
  have hDm : (D F β y).map ι =
      (parabolic L S 1).pCoreIn 2 ⊓ (Q F y).map ι := by
    change (Q F β ⊓ Q F y).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective, reduced_base_Q_map h true]
    rfl
  have hA : ((pResidual 2 c₁.actor).map c₁.actor.subtype).map ι =
      ((pResidual 2 (graphLocalGroup F u)).map
        (graphLocalGroup F u).subtype).map ι := by
    rw [ha₁]
    rfl
  let J₀ := R₀ ⊓ (Q F y).map ι
  let A₀ := ((pResidual 2 (graphLocalGroup F u)).map
    (graphLocalGroup F u).subtype).map ι
  let Z' := (Z F u).map ι
  have hJD : J₀ ≤ (parabolic L S 1).pCoreIn 2 ⊓ (Q F y).map ι :=
    inf_le_inf_right _ hRQ
  have hJZ : Disjoint J₀ Z' := hdis.mono inf_le_left le_rfl
  have hcomm : ⁅J₀,A₀⁆ ≤ Z' := by
    have hh := map_mono (f := ι) hmove
    rw [map_commutator, hDm, hA] at hh
    exact (commutator_mono hJD le_rfl).trans hh
  refine ⟨hJD, hJZ, hcomm, ?_⟩
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  apply hJZ.le_bot.trans'
  exact le_inf (le_normalizer_iff_commutator_le_left.mp inf_le_right)
    ((commutator_mono le_rfl inf_le_left).trans hcomm)

/-- One original residual marking supplies the direct product and faithful
endpoint-core detection, together with terminal separation control for every
continuation of the critical path. All action, marking and elementary-abelian
inputs are derived from the original source hypotheses. -/
theorem original_strict_residual_detection
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α, Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ g : graphLocalGroup F α, (g : G₀ L S) • β = t ∧
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁ ⊓ (Q F t).map ι
      let Z₀ := (Z F α).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F ((g : G₀ L S) • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      W₀ ⊔ Q₀ = enlargedEndpoint L S 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F ((g : G₀ L S) • u)).map ι ∧
      Q₀ ⊓ centralizer (W₀ : Set G) = R₀ ∧
      R₀ ≠ ⊥ ∧ IsElementaryAbelian 2 D₀ ∧ IsElementaryAbelian 2 R₀ ∧
      D₀ = Z₀ ⊔ R₀ ∧ Disjoint Z₀ R₀ ∧
      (∃ e : Z₀ × R₀ ≃* D₀, ∀ z r, (e (z,r) : G) = (z : G) * (r : G)) ∧
      R₀ ⊓ centralizer ((Q₀ ⊓ Q₁ : Subgroup G) : Set G) = ⊥ ∧
      P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      ∀ y : Vertex F, (graph F).Adj u y → y ≠ β →
        let J₀ := R₀ ⊓ (Q F y).map ι
        let A₀ := ((pResidual 2 (graphLocalGroup F u)).map
          (graphLocalGroup F u).subtype).map ι
        let Z' := (Z F u).map ι
        J₀ ≤ Q₁ ⊓ (Q F y).map ι ∧
          Disjoint J₀ Z' ∧ ⁅J₀,A₀⁆ ≤ Z' ∧
          J₀ ≤ centralizer
            ((A₀ ⊓ normalizer (J₀ : Set G) : Subgroup G) : Set G) := by
  obtain ⟨k, f, fin, ch, a, c, hactor, _, _, _, _, _, g, hg,
    hgen, hfour, hwhole, hRne, hD, hR, hdec, hdis, hprod, _, _, _, hP, hB⟩ :=
    original_strict_residual h hc hne hb hβu ht htne hns
  have ha : a = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst a
  obtain ⟨n, hn, K, fK, finK, hK, ⟨eK⟩⟩ :=
    Reduction.reduced_bTwo_middle_quotient_linear h hc hne hb
      (by exact ⟨by change false ≠ true; decide,
        Subgroup.CosetGeometry.incident_base _ _ _⟩) hβu
  let _ := fK
  let _ := finK
  let _ : Fintype K := Fintype.ofFinite K
  let _ : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eβ := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  have hdet := original_bTwo_residual_endpoint_centralizer h hc hne hb hβu
    ht htne c hactor eβ g hg hgen hD
  have hcentral := reduced_bTwo_middle_central h hc hne hb
    (by exact ⟨by change false ≠ true; decide,
      Subgroup.CosetGeometry.incident_base _ _ _⟩) hβu
  have hcent := NoncommutingProfile.Reduction.original_bTwo_central_center_intersections
    h hb c hactor hcentral (LinearEquiv.refl _ _) ht htne
  dsimp only at hcent
  let R₀ := ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι) ⊓
    centralizer (((Z F u).map ι ⊔
      (Z F ((g : G₀ L S) • u)).map ι : Subgroup G) : Set G)
  have hRZ : Disjoint R₀ ((Z F u).map ι) := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hxQ : x ∈ (parabolic L S 0).pCoreIn 2 :=
      (show x ∈ (parabolic L S 0).pCoreIn 2 ⊓
        centralizer (((Z F u).map ι ⊔
          (Z F ((g : G₀ L S) • u)).map ι : Subgroup G) : Set G) from
          hwhole.symm ▸ hx.1).1
    have hxβ : x ∈ (Z F β).map ι :=
      hcent.2.1 ▸ (show x ∈ (Z F u).map ι ⊓ (parabolic L S 0).pCoreIn 2 from
        ⟨hx.2, hxQ⟩)
    have hxα : x ∈ (Z F α).map ι :=
      (show x ∈ (Z F α).map ι ⊓ (Z F u).map ι from hcent.2.2.1.symm ▸ hxβ).1
    exact hdis.le_bot ⟨hxα, hx.1⟩
  let g' : graphLocalGroup F α := ⟨g, hactor ▸ g.property⟩
  refine ⟨g', hg, hgen, hfour, hwhole, hRne, hD, hR, hdec, hdis, hprod,
    hdet, hP, hB, ?_⟩
  intro y hy hyne
  exact original_terminal_core_control h hc hne hb hβu
    (R₀ := R₀) (inf_le_left.trans inf_le_left) hRZ hy hyne

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
