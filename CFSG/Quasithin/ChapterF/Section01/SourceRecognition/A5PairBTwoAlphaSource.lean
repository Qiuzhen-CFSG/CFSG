module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoBetaSource
public import Theory.Representation.BinaryConjugationSection.FixedPointFree
public import Theory.Representation.BinaryConjugationSection.QuotientSection

/-!
# The original alpha factor covers the natural core section

The literal distance-two alpha core modulo D has the source-constructed
natural-copy action. A cubic matrix is fixed-point-free on that section,
so commutators with the actual alpha enlargement cover the section. The
enlargement is the original factor times its full parabolic core, and
core commutators lie in D. Thus the whole alpha core lies in L_alpha D.

This retains the original factor and the literal adjacent-core intersection.
It does not put the remaining D/Z residual in the original factor, and does
not assert alpha Frattini irreducibility or a completed containment branch.

Source: DGS, Groups and Graphs (1985), (10.7)--(10.10), pp.158--165;
Aschbacher--Smith F.1.12, pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

private theorem natural_copies_commutator_cover
    {X k M : Type*} [Group X] [Field k] [CharP k 2]
    [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (H Q D : Subgroup X) (q : H →* SL(2,k)) (hq : Function.Surjective q)
    (σ : Representation (ZMod 2) SL(2,k) M)
    (d : BinaryConjugationSection H Q D (σ.comp q))
    (hn : SL2SylowFixedRecognition.NaturalCoordinates σ) :
    Q = ⁅Q,H⁆ ⊔ D := by
  let z : SL(2,k) := ⟨!![0,1;1,1], by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩
  have hz : z ^ 3 = 1 := by
    apply Subtype.ext
    change (!![0,1;1,1] : Matrix (Fin 2) (Fin 2) k) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
  have hz1 : z ≠ 1 := by
    intro he
    have hh := congrArg (fun a : SL(2,k) => a.val 0 0) he
    simp [z] at hh
  obtain ⟨a,ha⟩ := hq z
  have hf := odd_fixed_eq_bot_of_natural_copies σ hn z (by decide : Odd 3) hz hz1
  apply d.section_eq_commutator_sup_of_fixedPointFree H le_rfl a a.property
  intro v hv
  have hv' : v ∈ fixedSpace σ (zpowers z) := by
    apply (mem_fixedSpace_zpowers_iff σ z v).mpr
    simpa only [MonoidHom.comp_apply,ha] using hv
  simpa only [hf,Submodule.mem_bot] using hv'

variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- The genuine A5 distance-two source covers the alpha core modulo its
literal D subgroup. The remaining residual layer is not discarded. -/
theorem HypothesisF11.a5_bTwo_alpha_core_le_local_sup_D
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β) :
    twoCore (parabolic L S 0) ≤ L 0 ⊔
      ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype) := by
  let H := reduced_triple h
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  let e (i : Fin 2) := (a i).some.trans e₄.symm
  let eβ := (reduced_graphLinearQuotient h true (e 1)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (GaloisField 2 2)).symm
  obtain ⟨hN,hE,σ,d,_,_,hnatural⟩ := c.linear_core_natural_copies H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor
    (reduced_bTwo_middle_central h hc hne hb hab hβu) ht htne
    (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2.le
    (reduced_graph_core_obstruction h α β hab) eβ
  let : ((D F β t).subgroupOf (Q F α)).Normal := hN
  let : IsElementaryAbelian 2 (Q F α ⧸ (D F β t).subgroupOf (Q F α)) := hE
  have hcover : Q F α = ⁅Q F α,c.actor⁆ ⊔ D F β t := by
    exact natural_copies_commutator_cover (k := k)
      (M := Additive (Q F α ⧸ (D F β t).subgroupOf (Q F α)))
      c.actor (Q F α) (D F β t) c.quotient c.onto σ d hnatural
  have hder : ⁅Q F α,Q F α⁆ ≤ D F β t := by
    apply commutator_le.mpr
    intro x hx y hy
    let y' : c.actor := ⟨y,c.core_le hy⟩
    have hqy : c.quotient y' = 1 := by
      change y' ∈ c.quotient.ker
      rw [c.kernel]
      exact hy
    apply (d.fixed_coordinate_iff_commutator_mem y' ⟨x,hx⟩).mp
    simp only [MonoidHom.comp_apply,hqy,map_one]
    rfl
  let ι := (G₀ L S).subtype
  let Q₀ := twoCore (parabolic L S 0)
  let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
  let A₀ := enlargedEndpoint L S 0
  have hQm : (Q F α).map ι = Q₀ := reduced_base_Q_map h false
  have hDm : (D F β t).map ι = D₀ := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hAm : c.actor.map ι = A₀ := by
    rw [hactor]
    exact reduced_graphLocalGroup_image h false
  have hcover₀ : Q₀ = ⁅Q₀,A₀⁆ ⊔ D₀ := by
    have hh := congrArg (map ι) hcover
    rwa [Subgroup.map_sup,map_commutator,hQm,hDm,hAm] at hh
  have hder₀ : ⁅Q₀,Q₀⁆ ≤ D₀ := by
    have hh := map_mono (f := ι) hder
    rwa [map_commutator,hQm,hDm] at hh
  have hnD : A₀ ≤ normalizer (D₀ : Set G) := by
    have hh := (map_mono (f := ι) d.kernel_normalized).trans ((D F β t).le_normalizer_map ι)
    rwa [hAm,hDm] at hh
  have hA : A₀ = Q₀ ⊔ L 0 := reduced_enlargedEndpoint_eq_starred_of_linear h 0 (e 0)
  have hAP : A₀ ≤ parabolic L S 0 := hA ▸ starredParabolic_le 0
  have hnL : A₀ ≤ normalizer (L 0 : Set G) := hAP.trans
    ((normal_subgroupOf_iff_le_normalizer
      (show L 0 ≤ parabolic L S 0 from le_sup_left.trans le_sup_left)).mp
      (h.local_normal_in_parabolic 0))
  have hn : A₀ ≤ normalizer ((L 0 ⊔ D₀ : Subgroup G) : Set G) :=
    (le_inf hnL hnD).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hcomm : ⁅Q₀,A₀⁆ ≤ L 0 ⊔ D₀ := by
    rw [commutator_comm,hA]
    apply commutator_sup_le_of_relative_normal A₀ Q₀ (L 0) Q₀ (L 0 ⊔ D₀)
      hn (hA ▸ le_sup_left) (hA ▸ le_sup_right)
    · exact hder₀.trans le_sup_right
    · exact (le_normalizer_iff_commutator_le_left.mp
        ((hA ▸ le_sup_left).trans hnL)).trans le_sup_left
  change Q₀ ≤ L 0 ⊔ D₀
  rw [hcover₀]
  exact sup_le hcomm le_sup_right

omit [Finite G] in
/-- The natural alpha center is already contained in the unchanged
original factor. No normalization assumption on S is added. -/
theorem HypothesisF11.a5_bTwo_alpha_center_le_local
    (h : HypothesisF11 L S)
    (a : (L 0 ⧸ pCore 2 (L 0)) ≃* alternatingGroup (Fin 5))
    {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u) :
    (Z F α).map (G₀ L S).subtype ≤ L 0 := by
  let H := reduced_triple h
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor
    (reduced_bTwo_middle_central h hc hne hb hab hβu)
  have hnatural := sl2_natural_copies c.representation c.imageSylow
    c.quadratic c.generated c.fixed_bot
  have hcover := natural_copies_commutator_cover c.actor (Z F α)
    (omegaCenterIn c.actor) c.quotient c.onto c.representation c.coordinates hnatural
  rw [hω,sup_bot_eq] at hcover
  let ι := (G₀ L S).subtype
  let Q₀ := twoCore (parabolic L S 0)
  let Z₀ := (Z F α).map ι
  let A₀ := enlargedEndpoint L S 0
  have hAm : c.actor.map ι = A₀ := by
    rw [hactor]
    exact reduced_graphLocalGroup_image h false
  have hcover₀ : Z₀ = ⁅Z₀,A₀⁆ := by
    have hh := congrArg (map ι) hcover
    rwa [map_commutator,hAm] at hh
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  have hA : A₀ = Q₀ ⊔ L 0 :=
    reduced_enlargedEndpoint_eq_starred_of_linear h 0 (a.trans e₄.symm)
  have hAP : A₀ ≤ parabolic L S 0 := hA ▸ starredParabolic_le 0
  have hnL : A₀ ≤ normalizer (L 0 : Set G) := hAP.trans
    ((normal_subgroupOf_iff_le_normalizer
      (show L 0 ≤ parabolic L S 0 from le_sup_left.trans le_sup_left)).mp
      (h.local_normal_in_parabolic 0))
  have hZA : Z₀ ≤ A₀ := by
    have hh := map_mono (f := ι) c.coordinates.section_le
    rwa [hAm] at hh
  have hQZ : ⁅Q₀,Z₀⁆ = ⊥ := by
    have hh := congrArg (map ι)
      (commutator_eq_bot_iff_le_centralizer.mpr (graph_Q_centralizes_Z H α))
    rw [map_commutator,Subgroup.map_bot] at hh
    change ⁅(Q F α).map ι,Z₀⁆ = ⊥ at hh
    have hQm : (Q F α).map ι = Q₀ := reduced_base_Q_map h false
    rwa [hQm] at hh
  change Z₀ ≤ L 0
  rw [hcover₀,commutator_comm,hA]
  exact commutator_sup_le_of_relative_normal A₀ Q₀ (L 0) Z₀ (L 0)
    hnL (hA ▸ le_sup_left) (hA ▸ le_sup_right) (hQZ.le.trans bot_le)
    (le_normalizer_iff_commutator_le_left.mp (hZA.trans hnL))

/-- The original alpha core is covered by the original factor and the
actual opposite-center residual. This records the exact remaining layer. -/
theorem HypothesisF11.a5_bTwo_alpha_core_residual_cover
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β) :
    ∃ g : graphLocalGroup F α, (g : G₀ L S) • β = t ∧
      let Q₀ := twoCore (parabolic L S 0)
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype
      let Z₀ := (Z F α).map (G₀ L S).subtype
      let W₀ := (Z F u).map (G₀ L S).subtype ⊔
        (Z F ((g : G₀ L S) • u)).map (G₀ L S).subtype
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      Q₀ ≤ L 0 ⊔ R₀ ∧ R₀ ≠ ⊥ ∧ IsElementaryAbelian 2 R₀ ∧
        D₀ = Z₀ ⊔ R₀ ∧ Disjoint Z₀ R₀ ∧
        Q₀ ⊓ centralizer (W₀ : Set G) = R₀ := by
  obtain ⟨g,hg,_,_,hcentral,hRne,_,hRelem,hdec,hdis,_⟩ :=
    DGS85.Assembly.BTwoSource.original_strict_residual_detection
      h hc hne hb hβu ht htne (h.a5_parabolic_not_solvable 0 (a 0).some)
  refine ⟨g,hg,?_,hRne,hRelem,hdec,hdis,hcentral⟩
  have hcover := h.a5_bTwo_alpha_core_le_local_sup_D a hc hne hb hβu ht htne
  rw [hdec,←sup_assoc,sup_eq_left.mpr
    (h.a5_bTwo_alpha_center_le_local (a 0).some hc hne hb hβu)] at hcover
  exact hcover

end CFSG.Quasithin.ChapterF.Source
