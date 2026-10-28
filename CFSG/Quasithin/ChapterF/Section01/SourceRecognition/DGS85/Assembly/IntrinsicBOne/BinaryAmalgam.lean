module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.IntrinsicBOne.BinaryEndpoints
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.BinaryLinear.Rigidity
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour.BinaryRigidity

/-!
# The full binary b=1 reduced amalgam

The natural SL₂(2) Sylow normalizer has order two. Once the intrinsic actor
is the full reduced endpoint, its neighbor stabilizer therefore equals the
product of the two vertex cores. This identifies the entire reduced Borel
and proves that it is Sylow in each endpoint.

The synchronized Chapter 10 core orders give either S₄–D₈–S₄ or
(C₂ × S₄)–(C₂ × D₈)–(C₂ × S₄). Faithfulness supplies the compatible
isomorphism to the concrete PSL₃(2) or full Sp₄(2) flag. Transport through
the original reduced-completion inclusion retains both endpoint squares.
The completion itself need not be finite. The original S is not identified
with the Borel two-core, and original extension restoration is separate.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.156–157 and
(14.13),(14.15), pp.218–220; AS F.1.12(I)(1–2), pp.262–263.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne
open Reduction OriginalExtension NoncommutingProfile
variable {G k W : Type*} [Group G] [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
/-- At the binary parameter the Sylow normalizer in the natural SL₂ quotient
is itself Sylow. Since the actor is the full endpoint, this identifies the
entire reduced Borel, including any initially possible odd part. -/
theorem binary_borel_eq_core_product
    (h : HypothesisF11 L S) (i : Bool)
    (d : BOneActionData F (base F i) (base F (!i)) k W)
    (he : d.actor = stabilizer F (base F i))
    (hneighbor : Q F (base F (!i)) = Z F (base F (!i))) (hk : Nat.card k=2) :
    (B₀ L S).subgroupOf (G₀ L S) = Q F (base F (!i)) ⊔ Q F (base F i) := by
  let B := (B₀ L S).subgroupOf (G₀ L S)
  have hedge : stabilizer F (base F i) ⊓ stabilizer F (base F (!i)) = B := by
    have hstab (j : Bool) : stabilizer F (base F j) = F j :=
      Subgroup.CosetGeometry.stabilizer_base F j
    rw [hstab,hstab]
    cases i
    · exact (reduced_triple h).intersection
    · exact (inf_comm _ _).trans (reduced_triple h).intersection
  have hn : B ≤ normalizer (d.actor : Set (G₀ L S)) := by
    rw [he]
    exact (hedge ▸ inf_le_left).trans (stabilizer F (base F i)).le_normalizer
  have hnorm : normalizer ((d.imageSylow : Subgroup SL(2,k)) : Set SL(2,k)) = (d.imageSylow : Subgroup SL(2,k)) := by
    have hcS : Nat.card d.imageSylow=2 := by
      rw [←Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 d.imageSylow).toEquiv]
      exact (Nat.card_congr (Multiplicative.toAdd : Multiplicative k ≃ k)).trans hk
    have hcN : Nat.card (normalizer ((d.imageSylow : Subgroup SL(2,k)) : Set SL(2,k)))=2 := by
      rw [Matrix.SpecialLinearGroup.card_sylow_normalizer_even,hk]
    exact (eq_of_le_of_card_ge (d.imageSylow : Subgroup SL(2,k)).le_normalizer
      (by rw [hcN,hcS])).symm
  have hpre : (d.imageSylow : Subgroup SL(2,k)).comap d.quotient =
      (Q F (base F (!i)) ⊔ Q F (base F i)).subgroupOf d.actor :=
    neighbor_core_product_preimage d hneighbor
  apply le_antisymm
  · intro x hx
    let a : d.actor := ⟨x,he.symm ▸ ((hedge ▸ inf_le_left) hx)⟩
    have hfix : (a : G₀ L S) • base F (!i) = base F (!i) := (hedge ▸ inf_le_right) hx
    have hm := (base_actor_fixes_neighbor_iff (reduced_triple h) i d hn hneighbor a).mpr hfix
    change d.quotient a ∈ normalizer ((d.imageSylow : Subgroup SL(2,k)) : Set SL(2,k)) at hm
    rw [hnorm] at hm
    have hp : a ∈ (d.imageSylow : Subgroup SL(2,k)).comap d.quotient := hm
    rw [hpre] at hp
    exact hp
  · apply sup_le
    · have hh : Q F (base F (!i)) ≤ stabilizer F (base F (!i)) ⊓ stabilizer F (base F i) :=
        (source_Z_Q_U (reduced_triple h) _).2.trans
          (ballKernel_one_le_edge F d.adjacent.symm)
      rw [inf_comm] at hh
      exact hh.trans hedge.le
    · have hh : Q F (base F i) ≤ stabilizer F (base F i) ⊓ stabilizer F (base F (!i)) :=
        (source_Z_Q_U (reduced_triple h) _).2.trans
          (ballKernel_one_le_edge F d.adjacent)
      simpa only [hedge] using hh

private def graphAmalgam (L : Fin 2 → Subgroup G) (S : Subgroup G) :=
  ofSubgroups (reducedFamily L S false) ((B₀ L S).subgroupOf (G₀ L S))
    (reducedFamily L S true) (comap_mono le_sup_right) (comap_mono le_sup_right)

private def subgroupPairCongr {X : Type*} [Group X]
    {P B R P' B' R' : Subgroup X} (hP : P=P') (hB : B=B') (hR : R=R')
    (h₀ : B≤P) (h₁ : B≤R) (h₀' : B'≤P') (h₁' : B'≤R') :
    Iso (ofSubgroups P B R h₀ h₁) (ofSubgroups P' B' R' h₀' h₁') := by
  subst P' B' R'
  exact Iso.refl _

private def subgroupOfPairIso {X : Type*} [Group X]
    (P B R T : Subgroup X) (h₀ : B≤P) (h₁ : B≤R)
    (hP : P≤T) (hB : B≤T) (hR : R≤T) :
    Iso (ofSubgroups P B R h₀ h₁)
      (ofSubgroups (P.subgroupOf T) (B.subgroupOf T) (R.subgroupOf T)
        (comap_mono h₀) (comap_mono h₁)) where
  left := (subgroupOfEquivOfLe hP).symm
  middle := (subgroupOfEquivOfLe hB).symm
  right := (subgroupOfEquivOfLe hR).symm
  left_commutes _ := rfl
  right_commutes _ := rfl

private def sourceGraphIso (h : HypothesisF11 L S) : Iso (reducedAmalgam L S) (graphAmalgam L S) :=
  (subgroupPairCongr (P₀_eq_source h 0).symm (B₀_eq_source h).symm (P₀_eq_source h 1).symm
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1) le_sup_right le_sup_right).trans
      (subgroupOfPairIso _ _ _ (G₀ L S) le_sup_right le_sup_right
        le_sup_left (le_sup_right.trans le_sup_left) le_sup_right)

private theorem graphAmalgam_faithful (h : HypothesisF11 L S) : Faithful (graphAmalgam L S) :=
  faithful_ofSubgroups_of_completion _ _ _ _ _ (reduced_triple h).generate (reduced_triple h).faithful

private def centralEquiv : Multiplicative (ZMod 2) ≃* ℤˣ :=
  mulEquivOfPrimeCardEq (p := 2) (by simp) (by rw [Nat.card_eq_fintype_card]; decide)

private theorem graph_left_sylow (h : HypothesisF11 L S)
    {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (p : C2Source.Profile L S k₀ k₁ W₀ W₁)
    (hB : (B₀ L S).subgroupOf (G₀ L S) = Q F (base F true) ⊔ Q F (base F false)) :
    ∃ T : Sylow 2 (F false), (T : Subgroup (F false)) = (graphAmalgam L S).left.range := by
  have hh := (paired_core_product_sylow (reduced_triple h) p.left p.right).1
  rw [sup_comm] at hh
  obtain ⟨T,hT⟩ : ∃ T : Sylow 2 (F false), (T : Subgroup (F false)).map (F false).subtype =
      Q F (base F true) ⊔ Q F (base F false) := hh
  refine ⟨T,?_⟩
  apply map_injective (F false).subtype_injective
  rw [hT,←hB]
  change _ = ((Subgroup.inclusion (show (B₀ L S).subgroupOf (G₀ L S) ≤ F false from
    comap_mono le_sup_right)).range).map (F false).subtype
  rw [inclusion_range]
  exact (map_subgroupOf_eq_of_le (show (B₀ L S).subgroupOf (G₀ L S) ≤ F false from
    comap_mono le_sup_right)).symm

/-- Binary source recognition preserves the full reduced Borel and both
endpoint maps. The elementary-eight branch uses full Sp₄(2). -/
theorem binary_reduced_comparison
    {k₀ k₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    (h : HypothesisF11 L S)
    (p : letI : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
      letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      C2Source.Profile L S k₀ k₁ (Fin 2 → k₀) (Fin 2 → k₁))
    (hk : Nat.card k₀ = 2) :
    Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam (ZMod 2) false)) ∨
      Nonempty (Iso (reducedAmalgam L S) (SymplecticNative.amalgam (ZMod 2) true)) := by
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  have hk₁ : Nat.card k₁=2 :=
    (paired_field_orders_eq (reduced_triple h) p.left p.right p.natural).symm.trans hk
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions (reduced_triple h) p.left p.right
  have hn₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (p.left.actor : Set (G₀ L S)) := by
    rw [p.left_actor]
    exact reduced_borel_normalizes_source_actor h 0
  have hn₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (p.right.actor : Set (G₀ L S)) := by
    rw [p.right_actor]
    exact reduced_borel_normalizes_source_actor h 1
  have horders := paired_core_product_order_dichotomy (reduced_triple h) p.left p.right
    p.natural (LinearEquiv.refl (ZMod 2) _) hn₀ hn₁
  have hcases : (Nat.card (Q F (base F false))=4 ∧ Nat.card (Q F (base F true))=4) ∨
      (Nat.card (Q F (base F false))=8 ∧ Nat.card (Q F (base F true))=8) := by
    rcases horders with ⟨_,_,h₀,h₁,_⟩ | ⟨_,_,h₀,h₁,_⟩
    · have h₀' : Nat.card (Q F (base F false)) = Nat.card k₀^2 := h₀
      have h₁' : Nat.card (Q F (base F true)) = Nat.card k₁^2 := h₁
      exact Or.inl ⟨h₀'.trans (by norm_num [hk]),h₁'.trans (by norm_num [hk₁])⟩
    · have h₀' : Nat.card (Q F (base F false)) = Nat.card k₀^3 := h₀
      have h₁' : Nat.card (Q F (base F true)) = Nat.card k₁^3 := h₁
      exact Or.inr ⟨h₀'.trans (by norm_num [hk]),h₁'.trans (by norm_num [hk₁])⟩
  have hsmall₀ : Nat.card (Q F (base F false))=4 ∨ Nat.card (Q F (base F false))=8 :=
    hcases.imp And.left And.left
  have hsmall₁ : Nat.card (Q F (base F true))=4 ∨ Nat.card (Q F (base F true))=8 :=
    hcases.imp And.right And.right
  have hcards : Nat.card (Q F (base F true))=Nat.card (Q F (base F false)) := by
    rcases hcases with hh | hh <;> exact hh.2.trans hh.1.symm
  have he₀ := binary_actor_eq_stabilizer h false p.left p.left_actor hc₀ hc₁ p.natural hk hsmall₀ hcards
  have he₁ := binary_actor_eq_stabilizer h true p.right p.right_actor hc₁ hc₀
    (LinearEquiv.refl (ZMod 2) _) hk₁ hsmall₁ hcards.symm
  have hB := binary_borel_eq_core_product h false p.left he₀ hc₁ hk
  obtain ⟨T,hT⟩ := graph_left_sylow h p hB
  have h₀ := binary_endpoint_models h false p.left he₀ hc₀ hk
  have h₁ := binary_endpoint_models h true p.right he₁ hc₁ hk₁
  let a := sourceGraphIso h
  let A := graphAmalgam L S
  have hi : Function.Injective A.left := ofSubgroups_left_injective ..
  have hj : Function.Injective A.right := ofSubgroups_right_injective ..
  have hf : Faithful A := graphAmalgam_faithful h
  rcases hcases with hc | hc
  · obtain ⟨f₀⟩ := h₀.1 hc.1
    obtain ⟨f₁⟩ := h₁.1 hc.2
    let e₀ : F false ≃* Equiv.Perm (Fin 4) :=
      (MulEquiv.subgroupCongr (Subgroup.CosetGeometry.stabilizer_base F false)).symm.trans f₀
    let e₁ : F true ≃* Equiv.Perm (Fin 4) :=
      (MulEquiv.subgroupCongr (Subgroup.CosetGeometry.stabilizer_base F true)).symm.trans f₁
    obtain ⟨_,eB,_⟩ := exists_normalized_endpoint A.left MixedEight.square hi
      MixedEight.square_injective T hT MixedEight.squareSylow rfl e₀
    obtain ⟨e⟩ := GreenBook.LieModels.BinaryLinear.iso_of_faithful_symmetric_four_pair A hi hj hf e₀ eB e₁
    exact Or.inl ⟨a.trans e⟩
  · obtain ⟨f₀⟩ := h₀.2 hc.1
    obtain ⟨f₁⟩ := h₁.2 hc.2
    let e₀ : F false ≃* SplitSymmetricFourPair.L :=
      ((MulEquiv.subgroupCongr (Subgroup.CosetGeometry.stabilizer_base F false)).symm.trans f₀).trans
        (MulEquiv.prodCongr centralEquiv (MulEquiv.refl _))
    let e₁ : F true ≃* SplitSymmetricFourPair.L :=
      ((MulEquiv.subgroupCongr (Subgroup.CosetGeometry.stabilizer_base F true)).symm.trans f₁).trans
        (MulEquiv.prodCongr centralEquiv (MulEquiv.refl _))
    obtain ⟨_,eB,_⟩ := exists_normalized_endpoint A.left MixedSixteen.left hi
      MixedSixteen.left_injective T hT MixedSixteen.leftSylow rfl e₀
    obtain ⟨e⟩ := GreenBook.LieModels.SymplecticFour.BinaryRigidity.iso_of_faithful_split_symmetric_four_pair
      A hi hj hf e₀ eB e₁
    exact Or.inr ⟨a.trans e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne
