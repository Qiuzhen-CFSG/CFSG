module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourCoreSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaCoreSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalBinarySource
public import Theory.GroupTheory.PGroup.QuinticFrattini

/-!
# Recognition of the original field-four beta core

The original PSL₂(4) quotient supplies a quintic element in the full beta
parabolic. Characteristic two makes its conjugation action have order five
on the literal core and its Frattini quotient. The beta commutator identity
supplies noncommutativity, and the quadratic orbit calculation supplies the
rank bound. Thus all three extra premises of `BTwoFieldFourCoreSource` are
discharged and the actual beta core is the minus extraspecial model.

The endpoint element and its ambient conjugation formula are retained.
This is core recognition; splitting the beta extension and recognizing the
full J₂ parabolics remain further source arguments.
Source: DGS, Groups and Graphs (1985), (10.9), printed p.163.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourActorSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-- An actual original endpoint element induces order five on the original beta core and its Frattini quotient. -/
theorem original_field_four_beta_frattini_actor
    (h : HypothesisF11 L S)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 4) :
    ∃ x : parabolic L S 1, orderOf x = 5 ∧
      ∃ a : MulAut ((parabolic L S 1).pCoreIn 2), orderOf a = 5 ∧
        orderOf (quotientAut (frattini ((parabolic L S 1).pCoreIn 2)) a) = 5 ∧
        ∀ q, (a q : G) = (x : G) * (q : G) * (x : G)⁻¹ := by
  let P := parabolic L S 1
  let Q₁ := P.pCoreIn 2
  let : Finite P := h.finite_parabolic 1
  let : Finite (L 1) := h.finite_local 1
  let : Finite Q₁ := Finite.of_injective
    (inclusion (show Q₁ ≤ P from pCoreIn_le 2 _)) (inclusion_injective _)
  have hpsl : Nat.card PSL(2,K) = 60 := by
    let : Fintype K := Fintype.ofFinite K
    have hh := BenderSuzuki.External.huppert614_card_psl_mul_center (K := K)
    rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1), mul_one, hK] at hh
    exact hh
  have hd : 5 ∣ Nat.card P := by
    apply (show 5 ∣ Nat.card (L 1 ⧸ pCore 2 (L 1)) from ?_).trans
      ((card_quotient_dvd_card (pCore 2 (L 1))).trans (card_dvd_of_le (show L 1 ≤ P from le_sup_left.trans le_sup_left)))
    rw [Nat.card_congr e.toEquiv,hpsl]
    decide
  obtain ⟨x,hx,ha,_⟩ := QuinticFrattini.exists_core_actor
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two 1)) hd
  let eQ : pCore 2 P ≃* Q₁ := (pCore 2 P).equivMapOfInjective P.subtype P.subtype_injective
  let a := MulAut.congr eQ (MulAut.conjNormal (H := pCore 2 P) x)
  have hao : orderOf a = 5 := (MulAut.congr eQ).orderOf_eq _ |>.trans ha
  have haq : orderOf (quotientAut (frattini Q₁) a) = 5 :=
    ((quotientAut (frattini Q₁)).orderOf_map_eq_of_coprime_of_isPGroup_ker
      (isPGroup_quotientAut_frattini_kernel (isPGroup_pCoreIn 2 P)) a
      (by rw [hao]; decide)).trans hao
  refine ⟨x,hx,a,hao,haq,?_⟩
  intro q
  have he : (((eQ.symm q : pCore 2 P) : P) : G) = (q : G) :=
    congrArg (fun y : Q₁ => (y : G)) (eQ.apply_symm_apply q)
  change (x : G) * (((eQ.symm q : pCore 2 P) : P) : G) * (x : G)⁻¹ = _
  rw [he]

/-- The field-four beta core is the minus extraspecial model, with no actor, rank or noncommutativity premise. -/
theorem original_bTwo_field_four_beta_recognition
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    IsExtraspecial 2 ((parabolic L S 1).pCoreIn 2) ∧
      Nonempty ((parabolic L S 1).pCoreIn 2 ≃* MinusExtraspecial.Model) := by
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let _ : Finite (parabolic L S 1) := h.finite_parabolic 1
  let _ : Finite Q₁ := Finite.of_injective
    (inclusion (show Q₁ ≤ parabolic L S 1 from pCoreIn_le 2 _)) (inclusion_injective _)
  have hk := (original_bTwo_exceptional_fields_and_orders h hb c hactor hcentral
    ht hne hcomm hnot e hD E).1
  have hparam := (original_bTwo_exceptional_beta_parameters h hb c hactor hcentral
    ht hne hcomm hnot e hD E).1
  have hquot : Nat.card (Q₁ ⧸ frattini Q₁) = 16 := by
    simpa [Q₁, hk, hK] using hparam
  have horders := original_bTwo_exceptional_linear_core_orders h hb c hactor hcentral
    ht hne hcomm.le hnot e (by
      apply map_injective (G₀ L S).subtype_injective
      change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
      rw [map_inf _ _ _ (G₀ L S).subtype_injective, reduced_base_Q_map h true]
      exact hD) E
  have hcard : Nat.card Q₁ = 32 := by
    simpa [Q₁, hk, hK] using horders.2
  have hphi : Nat.card (frattini Q₁) = 2 := by
    have hh := (frattini Q₁).index_mul_card
    change Nat.card (Q₁ ⧸ frattini Q₁) * Nat.card (frattini Q₁) = Nat.card Q₁ at hh
    rw [hquot, hcard] at hh
    omega
  have hnon : ¬ IsMulCommutative Q₁ := by
    intro hm
    have hh := (original_bTwo_beta_core_frattini h hb c hactor hcentral ht hne hcomm).2
    rw [commutator_self_eq_bot_iff.mpr hm] at hh
    exact base_Z_ne_bot (reduced_triple h) true
      ((map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective).mp hh.symm)
  obtain ⟨_,_,a,ha,haq,_⟩ := original_field_four_beta_frattini_actor h e hK
  have hQ := isPGroup_pCoreIn 2 (parabolic L S 1)
  exact ⟨field_four_beta_extraspecial hQ hnon hphi hquot a haq,
    field_four_beta_minus_model hQ hnon hphi hquot a haq
      (QuinticFrattini.elementary_card_lt_eight hQ hnon hcard hphi a ha)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
