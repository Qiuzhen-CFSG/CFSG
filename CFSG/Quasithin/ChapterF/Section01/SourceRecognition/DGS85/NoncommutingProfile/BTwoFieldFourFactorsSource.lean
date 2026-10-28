module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourStructureSource
public import Theory.GroupTheory.PGroup.CubicAnisotropicPair

/-!
# Anisotropic factors in the original field-four alpha core

The actual beta core is extraspecial of order thirty-two. Its intersection
with the original alpha core has order sixteen, and the previously proved
involution constraint gives it one constant nonidentity square outside the
alpha center. No quaternion factor or coordinate model is assumed.

The original fixed-point-free alpha cubic carries this intersection to a
second anisotropic sixteen with a different square value. Their intersection
is the actual alpha center and their join is the whole alpha core. The second
factor is identified with the literal conjugate neighboring-core intersection,
using the ambient conjugation formula and the reduced-to-original inclusion.
The same cubic balances all three nonidentity central square fibers.

These facts provide the anisotropic-factor and square-fiber inputs to root
recognition. The factor-centralizer condition, invariant four-group complements
and full J₂ parabolic recognition remain separate source obligations.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985), proof of
(10.9), printed p.163, and the complement criterion (5.16), pp.116--117.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance factorsSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

private theorem cubic_factor_marking (h : HypothesisF11 L S) {u : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W) (a : c.actor)
    (φ : MulAut ((parabolic L S 0).pCoreIn 2))
    (hφ : ∀ x, (φ x : G) = ((a : G₀ L S) : G) * (x : G) * ((a : G₀ L S) : G)⁻¹) :
    ((((parabolic L S 1).pCoreIn 2).subgroupOf ((parabolic L S 0).pCoreIn 2)).map
      φ.toMonoidHom).map ((parabolic L S 0).pCoreIn 2).subtype =
        (Q F₀ ((a : G₀ L S) • β)).map (G₀ L S).subtype ⊓ (parabolic L S 0).pCoreIn 2 := by
  let ι := (G₀ L S).subtype
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let A := Q₁.subgroupOf Q₀
  let γ := (MulAut.conj ((a : G₀ L S) : G)).toMonoidHom
  let γ₀ := (MulAut.conj (a : G₀ L S)).toMonoidHom
  have hh : Q₀.subtype.comp φ.toMonoidHom = γ.comp Q₀.subtype := by
    ext x
    exact hφ x
  have he : γ.comp ι = ι.comp γ₀ := by
    ext x
    change ι (a : G₀ L S) * ι x * (ι (a : G₀ L S))⁻¹ =
      ι ((a : G₀ L S) * x * (a : G₀ L S)⁻¹)
    rw [map_mul,map_mul,map_inv]
  have hmap₀ : (Q F₀ α).map ι = Q₀ := reduced_base_Q_map h false
  have hmap₁ : (Q F₀ β).map ι = Q₁ := reduced_base_Q_map h true
  have hv : (a : G₀ L S) • α = α := c.actor_le a.property
  change (A.map φ.toMonoidHom).map Q₀.subtype = _
  calc
    _ = (Q₁ ⊓ Q₀).map γ := by
      rw [map_map,hh,←map_map,subgroupOf_map_subtype]
    _ = ((Q F₀ β ⊓ Q F₀ α).map γ₀).map ι := by
      rw [map_map,←he,←map_map,map_inf _ _ _ (G₀ L S).subtype_injective,hmap₁,hmap₀]
    _ = _ := by
      have ht : (Q F₀ β ⊓ Q F₀ α).map γ₀ = Q F₀ ((a : G₀ L S) • β) ⊓ Q F₀ α := by
        change (Q F₀ β ⊓ Q F₀ α).map (MulAut.conj (a : G₀ L S)).toMonoidHom = _
        rw [map_inf _ _ _ (MulAut.conj (a : G₀ L S)).injective,←Q_translate,←Q_translate,hv]
      rw [ht,map_inf _ _ _ (G₀ L S).subtype_injective,hmap₀]

/-- The original adjacent-core intersection has order sixteen and one
nontrivial square value outside the actual alpha center. -/
theorem original_bTwo_field_four_anisotropic_intersection
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
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let A := ((parabolic L S 1).pCoreIn 2).subgroupOf Q₀
    Nat.card A = 16 ∧ Nat.card (center Q₀) = 4 ∧
      commutator Q₀ ≤ center Q₀ ∧ center Q₀ ≤ A ∧
      ∃ z : center Q₀, z ≠ 1 ∧
        ∀ x ∈ A, x ∉ center Q₀ → x ^ 2 = (z : Q₀) := by
  let ι := (G₀ L S).subtype
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₀ := (Z F₀ α).map ι
  let A := Q₁.subgroupOf Q₀
  have hmap₀ : (Q F₀ α).map ι = Q₀ := reduced_base_Q_map h false
  have hmap₁ : (Q F₀ β).map ι = Q₁ := reduced_base_Q_map h true
  let : Finite (parabolic L S 0) := h.finite_parabolic 0
  let : Finite (parabolic L S 1) := h.finite_parabolic 1
  let : Finite Q₀ := Finite.of_injective (inclusion (pCoreIn_le 2 (parabolic L S 0)))
    (inclusion_injective _)
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 (parabolic L S 1)))
    (inclusion_injective _)
  obtain ⟨hQa,hZa,hder,hPhi,hsq⟩ := original_bTwo_field_four_structure
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  change Nat.card Q₀ = 64 at hQa
  change (center Q₀).map Q₀.subtype = Z₀ at hZa
  change ⁅Q₀,Q₀⁆ = Z₀ at hder
  change ∀ x ∈ Q₀ ⊓ Q₁, x ^ 2 = 1 ↔ x ∈ Z₀ at hsq
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  have hk := (original_bTwo_exceptional_fields_and_orders h hb c hactor hcentral
    ht hne hcomm hnot e hD E).1
  have hω := c.omega_eq_bot_of_central_neighbor (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hactor hcentral
  have hZcard : Nat.card (center Q₀) = 4 := by
    rw [←card_map_of_injective Q₀.subtype_injective,hZa]
    change Nat.card ((Z F₀ α).map ι) = 4
    rw [card_map_of_injective (G₀ L S).subtype_injective]
    have hc := c.central_center_card E hω
    change Nat.card (Z F₀ α) = Nat.card k ^ 2 at hc
    rw [hc,hk]
    norm_num
  have hmemZ (x : Q₀) : x ∈ center Q₀ ↔ (x : G) ∈ Z₀ := by
    rw [←hZa]
    constructor
    · exact mem_map_of_mem Q₀.subtype
    · rintro ⟨y,hy,he⟩
      exact Q₀.subtype_injective he ▸ hy
  have hD₀ : Q₁ ⊓ (Q F₀ t).map ι = Z₀ := hD
  have hZQ₁ : Z₀ ≤ Q₁ := hD₀.symm.le.trans inf_le_left
  have hZA : center Q₀ ≤ A := fun x hx => hZQ₁ ((hmemZ x).mp hx)
  have hclass : commutator Q₀ ≤ center Q₀ := by
    have heq : commutator Q₀ = center Q₀ := by
      apply map_injective Q₀.subtype_injective
      rw [map_subtype_commutator,hZa,hder]
    exact heq.le
  obtain ⟨hExtra,⟨emodel⟩⟩ := original_bTwo_field_four_beta_recognition h hb c hactor
    hcentral ht hne hcomm hnot e hD E hK
  let : IsExtraspecial 2 Q₁ := hExtra
  have hQb : Nat.card Q₁ = 32 := (Nat.card_congr emodel.toEquiv).trans MinusExtraspecial.card_model
  have hi := relIndex_ker (K := (Q F₀ β).subgroupOf c.actor) c.quotient
  rw [c.kernel,relIndex_subgroupOf c.neighbor_core_le,c.neighbor_image] at hi
  have hidx : Q₀.relIndex Q₁ = 2 := by
    rw [←hmap₀,←hmap₁,
      relIndex_map_map_of_injective (f := ι) (Q F₀ α) (Q F₀ β)
        (G₀ L S).subtype_injective]
    exact hi.trans
      ((Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).symm.toEquiv).trans hk)
  have hcore : Q₁ = (V F₀ β 1).map ι := original_bTwo_exceptional_beta_core h hb c ht hne hD'
  have hZb : (center Q₁).map Q₁.subtype = (Z F₀ β).map ι := by
    rw [←IsExtraspecial.commutator_eq_center (p := 2),map_subtype_commutator]
    calc
      ⁅Q₁,Q₁⁆ = (⁅V F₀ β 1,Q F₀ β⁆).map ι := by
        rw [map_commutator,hmap₁,←hcore]
      _ = _ := congrArg (map ι) hcomm
  have hZZ : Z F₀ β ≤ Z F₀ α := center_le_of_central_neighbor (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) c.middle hcentral
  obtain ⟨hA,z₀,hz₀,hs⟩ := Theory.GroupTheory.extraspecial_anisotropic_intersection
    Q₀ Q₁ hQb hidx
    (show (center Q₁).map Q₁.subtype ≤ (center Q₀).map Q₀.subtype from by
      rw [hZb,hZa]
      exact map_mono hZZ)
    (fun x hx hxx => hZa.symm ▸ (hsq x hx).mp hxx)
  exact ⟨hA,hZcard,hclass,hZA,z₀,hz₀,hs⟩


/-- The constructed cubic gives two actual neighboring-core factors with
distinct square values, exact intersection, generation and balanced square fibers. -/
theorem original_bTwo_field_four_anisotropic_pair
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
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let A := Q₁.subgroupOf Q₀
    Nat.card A = 16 ∧
      ∃ a : c.actor, orderOf ((a : G₀ L S) : G) = 3 ∧
        ∃ φ : MulAut Q₀, orderOf φ = 3 ∧
          (∀ x, (φ x : G) = ((a : G₀ L S) : G) * (x : G) * ((a : G₀ L S) : G)⁻¹) ∧
          (A.map φ.toMonoidHom).map Q₀.subtype =
            (Q F₀ ((a : G₀ L S) • β)).map (G₀ L S).subtype ⊓ Q₀ ∧
          ∃ z z' : center Q₀, z ≠ 1 ∧ z' ≠ 1 ∧ z ≠ z' ∧
            (∀ x ∈ A, x ∉ center Q₀ → x ^ 2 = (z : Q₀)) ∧
            (∀ x ∈ A.map φ.toMonoidHom, x ∉ center Q₀ → x ^ 2 = (z' : Q₀)) ∧
            Nat.card (A.map φ.toMonoidHom) = 16 ∧
            A ⊓ A.map φ.toMonoidHom = center Q₀ ∧
            A ⊔ A.map φ.toMonoidHom = ⊤ ∧
            (∀ z₁ z₂ : center Q₀, z₁ ≠ 1 → z₂ ≠ 1 →
              Nat.card {x : Q₀ // x ^ 2 = (z₁ : Q₀)} =
                Nat.card {x : Q₀ // x ^ 2 = (z₂ : Q₀)}) := by
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let A := ((parabolic L S 1).pCoreIn 2).subgroupOf Q₀
  let : Finite (parabolic L S 0) := h.finite_parabolic 0
  let : Finite Q₀ := Finite.of_injective (inclusion (pCoreIn_le 2 (parabolic L S 0)))
    (inclusion_injective _)
  obtain ⟨hA,hZcard,hclass,hZA,z₀,hz₀,hs⟩ :=
    original_bTwo_field_four_anisotropic_intersection h hb c hactor hcentral ht hne
      hcomm hnot e hD E hK
  have hQa := (original_bTwo_field_four_structure
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK).1
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  obtain ⟨a,ha,_,φ,hφ,hφapply,hfree⟩ := original_bTwo_exceptional_linear_cubic
    h hb c hactor hcentral ht hne hcomm.le hnot e hD'
  obtain ⟨z',hz',hne',hB,hI,hgen,hsB,hbal⟩ :=
    Theory.GroupTheory.anisotropic_pair_of_fixed_free_cubic hQa hZcard hclass φ
      (hφ ▸ pow_orderOf_eq_one φ) hfree A hA hZA z₀ hz₀ hs
  exact ⟨hA,a,ha,φ,hφ,hφapply,cubic_factor_marking h c a φ hφapply,z₀,z',hz₀,hz',hne',hs,hsB,hB,hI,hgen,hbal⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
