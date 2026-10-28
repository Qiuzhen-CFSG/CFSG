module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourOriginalSource


/-!
# The actual alpha core inside the field-four J₂ comparison

The alpha core has order sixty-four and exponent four. Inside the common
Sylow group it therefore maps to the native J₂ second core: that core is
characterized as the index-two subgroup of exponent four. Restricting the
existing beta/Borel/Sylow comparison gives the same alpha-core inclusion
and preserves conjugation by every element of the full reduced Borel.

The actual alpha valence is three, so the reduced Borel order 384 gives
full alpha order 1152 and two-core quotient order eighteen. These results
prepare recognition of the full second endpoint; they do not yet identify
that endpoint or supply its inclusion square.

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985),
(10.9), printed pp.162–163, and the reduction on pp.95–96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
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
local instance fieldFourAlphaAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

local notation "JQ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.q₂
local notation "JS" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.s
open Sporadic.LeechRelated.J2.ExceptionalParabolics in
private theorem sylow_equiv_maps_alpha_core
    {G : Type*} [Group G] (Q T : Subgroup G) (hQT : Q ≤ T)
    (f : T ≃* JS) (hQ : Nat.card Q = 64) (hT : Nat.card T = 128)
    (hfour : ∀ x ∈ Q, x ^ 4 = 1) :
    (Q.subgroupOf T).map f.toMonoidHom = (JQ).subgroupOf JS := by
  let H := (Q.subgroupOf T).map f.toMonoidHom
  have hi : (Q.subgroupOf T).index = 2 := by
    have hh := (Q.subgroupOf T).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hQT).toEquiv,hQ,hT] at hh
    omega
  have hH : H.index = 2 := (index_map_of_bijective f.bijective _).trans hi
  have hle : (JQ).subgroupOf JS ≤ H := PairNormalizer.q₂_le_of_index_two_exponent_four H hH (by
    rintro x ⟨y,hy,rfl⟩
    rw [←map_pow,show y ^ 4 = 1 from Subtype.ext (hfour y hy),map_one])
  apply le_antisymm _ hle
  have hc : Nat.card H = 64 := by
    rw [card_map_of_injective f.injective,Nat.card_congr (subgroupOfEquivOfLe hQT).toEquiv,hQ]
  have hq : Nat.card ((JQ).subgroupOf JS) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe PairNormalizer.q₂_le_s).toEquiv).trans PairNormalizer.card_q₂
  exact (eq_of_le_of_card_ge hle (by rw [hc,hq])).ge

private theorem alpha_core_restriction
    {G : Type*} [Group G] (Q T : Subgroup G) (hQT : Q ≤ T)
    (f : T ≃* JS) (hf : (Q.subgroupOf T).map f.toMonoidHom = (JQ).subgroupOf JS) :
    ∃ e : Q ≃* JQ, ∀ q : Q,
      (e q : Sporadic.LeechRelated.J2.Carrier) = (f (inclusion hQT q) : Sporadic.LeechRelated.J2.Carrier) := by
  let e := (subgroupOfEquivOfLe hQT).symm.trans
    ((f.subgroupMap (Q.subgroupOf T)).trans ((MulEquiv.subgroupCongr hf).trans
      (subgroupOfEquivOfLe Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.q₂_le_s)))
  exact ⟨e,fun _ => rfl⟩

local notation "Jβ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁
local notation "JB" => Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B

private theorem root_four (x : Matrix.PSL3Four.RootNormalizerModel.Root) : x ^ 4 = 1 := by
  change x ^ (2*2) = 1
  rw [pow_mul,pow_two,pow_two]
  apply Matrix.PSL3Four.SylowModel.U.ext <;> simp [CharTwo.add_self_eq_zero]

/-- Every Sylow comparison carries the original alpha core to the literal
J₂ second core, by its unique index-two exponent-four characterization. -/
theorem original_bTwo_field_four_alpha_core_image
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4)
    (fT : (commonBorel L S).pCoreIn 2 ≃* JS) :
    ((((parabolic L S 0).pCoreIn 2).subgroupOf ((commonBorel L S).pCoreIn 2)).map
      fT.toMonoidHom) = (JQ).subgroupOf JS := by
  have hQT : (parabolic L S 0).pCoreIn 2 ≤ (commonBorel L S).pCoreIn 2 := by
    rw [original_bTwo_borel_core_eq_product h c]
    exact le_sup_left
  have hQ := (original_bTwo_field_four_structure
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK).1
  have hT : Nat.card ((commonBorel L S).pCoreIn 2) = 128 :=
    (Nat.card_congr fT.toEquiv).trans
      Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.card_s
  obtain ⟨eQ⟩ := original_bTwo_field_four_alpha_root
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  apply sylow_equiv_maps_alpha_core _ _ hQT fT hQ hT
  intro x hx
  have hx4 : (⟨x,hx⟩ : (parabolic L S 0).pCoreIn 2)^4 = 1 := by
    apply eQ.injective
    rw [map_pow,root_four,map_one]
  exact congrArg Subtype.val hx4

/-- The already constructed endpoint and full reduced Borel comparison
carries the actual alpha core with the same inclusion square. -/
theorem original_bTwo_field_four_beta_borel_alpha_core_equiv
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
    let T := (commonBorel L S).pCoreIn 2
    let Q₀ := (parabolic L S 0).pCoreIn 2
    ∃ (hQT : Q₀ ≤ T) (f : P₀ L S 1 ≃* Jβ) (fB : B₀ L S ≃* JB)
      (fT : T ≃* JS) (fQ : Q₀ ≃* JQ),
      (∀ b : B₀ L S, (fB b : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion le_sup_right b) : Sporadic.LeechRelated.J2.Carrier)) ∧
      (∀ t : T, (fT t : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion (le_sup_right.trans le_sup_right) t) : Sporadic.LeechRelated.J2.Carrier)) ∧
      (∀ q : Q₀, (fQ q : Sporadic.LeechRelated.J2.Carrier) =
        (fT (inclusion hQT q) : Sporadic.LeechRelated.J2.Carrier)) ∧
      ∃ d : (Jβ ⧸ pCore 2 Jβ) ≃* PSL(2,K),
        ∀ x : L 1, d (QuotientGroup.mk' (pCore 2 Jβ)
          (f (inclusion ((local_le_starredParabolic 1).trans le_sup_left) x))) =
            e (QuotientGroup.mk' (pCore 2 (L 1)) x) := by
  obtain ⟨f,fB,fT,hfB,hfT,d,hd⟩ := original_bTwo_field_four_reduced_beta_borel_equiv
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hQT : (parabolic L S 0).pCoreIn 2 ≤ (commonBorel L S).pCoreIn 2 := by
    rw [original_bTwo_borel_core_eq_product h c]
    exact le_sup_left
  have hfQ := original_bTwo_field_four_alpha_core_image
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK fT
  obtain ⟨fQ,hfQ⟩ := alpha_core_restriction _ _ hQT fT hfQ
  exact ⟨hQT,f,fB,fT,fQ,hfB,hfT,hfQ,d,hd⟩

private theorem reduced_alpha_borel_index (h : HypothesisF11 L S) {u : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W) :
    (B₀ L S).relIndex (P₀ L S 0) = Nat.card k + 1 := by
  have hi := c.neighbor_card (reduced_triple h)
  change Nat.card ((graph F₀).neighborSet (base F₀ false)) = Nat.card k + 1 at hi
  rw [card_neighbor_base] at hi
  change ((P₀ L S 1).subgroupOf (G₀ L S)).relIndex
    ((P₀ L S 0).subgroupOf (G₀ L S)) = _ at hi
  rw [←inf_relIndex_left, (reduced_triple h).intersection,
    relIndex_subgroupOf (show P₀ L S 0 ≤ G₀ L S from le_sup_left)] at hi
  exact hi

/-- The full reduced alpha endpoint has order 1152 and core quotient order 18.
Its index over the complete reduced Borel is the actual valence three. -/
theorem original_bTwo_field_four_reduced_alpha_orders
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
    (B₀ L S).relIndex (P₀ L S 0) = 3 ∧
      Nat.card (P₀ L S 0) = 1152 ∧ Nat.card (P₀ L S 0 ⧸ pCore 2 (P₀ L S 0)) = 18 := by
  have hk := (original_bTwo_exceptional_fields_and_orders
    h hb c hactor hcentral ht hne hcomm hnot e hD E).1
  have hi := reduced_alpha_borel_index h c
  rw [hk] at hi
  obtain ⟨_,_,_,hB⟩ := original_bTwo_field_four_reduced_beta_equals_enlargement
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) (B₀ L S) (P₀ L S 0)
    bot_le le_sup_right
  rw [relIndex_bot_left,relIndex_bot_left,hB,hi] at hcard
  have hP : Nat.card (P₀ L S 0) = 1152 := by omega
  have hQ := (original_bTwo_field_four_structure
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK).1
  have hcore : Nat.card (pCore 2 (P₀ L S 0)) = 64 := by
    rw [←card_map_of_injective (P₀ L S 0).subtype_injective]
    change Nat.card ((P₀ L S 0).pCoreIn 2) = 64
    rw [P₀_core h 0]
    exact hQ
  have hx := (pCore 2 (P₀ L S 0)).card_mul_index
  rw [hcore,hP,index_eq_card] at hx
  exact ⟨hi,hP,by omega⟩

private theorem core_conjugation_of_marking
    {G H : Type*} [Group G] [Group H] {P B Q : Subgroup G}
    {M MB MQ : Subgroup H} (hBP : B ≤ P) (hQP : Q ≤ P)
    (hn : B ≤ normalizer (Q : Set G))
    (f : P ≃* M) (fB : B ≃* MB) (fQ : Q ≃* MQ)
    (hB : ∀ b : B, (fB b : H) = (f (inclusion hBP b) : H))
    (hQ : ∀ q : Q, (fQ q : H) = (f (inclusion hQP q) : H)) :
    ∀ (b : B) (q : Q),
      (fQ (Q.normalizerMonoidHom ⟨b,hn b.property⟩ q) : H) =
        (fB b : H) * (fQ q : H) * (fB b : H)⁻¹ := by
  intro b q
  rw [hQ,hB,hQ]
  change (f ((inclusion hBP b) * (inclusion hQP q) * (inclusion hBP b)⁻¹) : H) = _
  rw [map_mul,map_mul,map_inv]
  rfl

private theorem marked_action_of_core
    {G : Type*} [Group G] (P B T Q : Subgroup G)
    (hBP : B ≤ P) (hTP : T ≤ P) (hn : B ≤ normalizer (Q : Set G))
    (D : (P ≃* Jβ) → Prop)
    (hh : ∃ (hQT : Q ≤ T) (f : P ≃* Jβ) (fB : B ≃* JB)
      (fT : T ≃* JS) (fQ : Q ≃* JQ),
      (∀ b : B, (fB b : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion hBP b) : Sporadic.LeechRelated.J2.Carrier)) ∧
      (∀ t : T, (fT t : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion hTP t) : Sporadic.LeechRelated.J2.Carrier)) ∧
      (∀ q : Q, (fQ q : Sporadic.LeechRelated.J2.Carrier) =
        (fT (inclusion hQT q) : Sporadic.LeechRelated.J2.Carrier)) ∧ D f) :
    ∃ (hn : B ≤ normalizer (Q : Set G))
      (f : P ≃* Jβ) (fB : B ≃* JB) (fQ : Q ≃* JQ),
      (∀ b : B, (fB b : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion hBP b) : Sporadic.LeechRelated.J2.Carrier)) ∧
      (∀ (b : B) (q : Q),
        (fQ (Q.normalizerMonoidHom ⟨b,hn b.property⟩ q) : Sporadic.LeechRelated.J2.Carrier) =
          (fB b : Sporadic.LeechRelated.J2.Carrier) * (fQ q : Sporadic.LeechRelated.J2.Carrier) *
            (fB b : Sporadic.LeechRelated.J2.Carrier)⁻¹) ∧ D f := by
  obtain ⟨hQT,f,fB,fT,fQ,hfB,hfT,hfQ,hd⟩ := hh
  have hQP : Q ≤ P := hQT.trans hTP
  have hmark (q : Q) : (fQ q : Sporadic.LeechRelated.J2.Carrier) =
      (f (inclusion hQP q) : Sporadic.LeechRelated.J2.Carrier) :=
    (hfQ q).trans (hfT (inclusion hQT q))
  exact ⟨hn,f,fB,fQ,hfB,core_conjugation_of_marking hBP hQP hn f fB fQ hfB hmark,hd⟩

/-- The source alpha-core comparison preserves conjugation by the entire
reduced Borel and retains the literal original beta quotient marking. -/
theorem original_bTwo_field_four_beta_borel_alpha_action
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
    ∃ (hn : B₀ L S ≤ normalizer (Q₀ : Set G))
      (f : P₀ L S 1 ≃* Jβ) (fB : B₀ L S ≃* JB) (fQ : Q₀ ≃* JQ),
      (∀ b : B₀ L S, (fB b : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion le_sup_right b) : Sporadic.LeechRelated.J2.Carrier)) ∧
      (∀ (b : B₀ L S) (q : Q₀),
        (fQ (Q₀.normalizerMonoidHom ⟨b,hn b.property⟩ q) : Sporadic.LeechRelated.J2.Carrier) =
          (fB b : Sporadic.LeechRelated.J2.Carrier) * (fQ q : Sporadic.LeechRelated.J2.Carrier) *
            (fB b : Sporadic.LeechRelated.J2.Carrier)⁻¹) ∧
      ∃ d : (Jβ ⧸ pCore 2 Jβ) ≃* PSL(2,K),
        ∀ x : L 1, d (QuotientGroup.mk' (pCore 2 Jβ)
          (f (inclusion ((local_le_starredParabolic 1).trans le_sup_left) x))) =
            e (QuotientGroup.mk' (pCore 2 (L 1)) x) := by
  apply marked_action_of_core (P₀ L S 1) (B₀ L S)
    ((commonBorel L S).pCoreIn 2) ((parabolic L S 0).pCoreIn 2)
    le_sup_right (le_sup_right.trans le_sup_right)
    (((B₀_le h).trans (commonBorel_le_parabolic 0)).trans
      ((parabolic L S 0).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (parabolic L S 0)))))
  exact original_bTwo_field_four_beta_borel_alpha_core_equiv
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
