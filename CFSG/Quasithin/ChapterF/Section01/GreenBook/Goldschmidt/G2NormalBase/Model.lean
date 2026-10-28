module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.G2
public import Theory.GroupTheory.Amalgam.AutomorphismTransport
public import Theory.GroupTheory.Amalgam.NormalBaseAction

/-!
# The marked binary G₂ model in the normal-base extension step

The existing compatible-automorphism count transports to the source's
derived amalgam. Conjugation by the full Borel acts faithfully on that
amalgam and has order 64, so it exhausts the compatible automorphism group.
All three action formulas retain the original full-group elements.

The embedded derived endpoints meet the full Borel in the embedded derived
Borel. Their joins with the full Borel are the full endpoints, by the
already proved orders 96, 64 and 192. The embedded derived Borel has index
two in the full Borel. These are the model inputs for Goldschmidt (1980),
§3.7, and the binary G₂ alternatives of Aschbacher--Smith F.1.12,
printed pp.263--264; no new finite enumeration is used.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.G2NormalBase.Model
open Theory.GroupTheory Subgroup
open ExceptionalModels.G2
open Atlas.G2.BinaryParabolicPair Atlas.G2.LieAutomorphismExtensions

theorem first_invariant (b : fullB) :
    derivedL₁.map (automorphismEquiv b.val).toMonoidHom = derivedL₁ :=
  Subgroup.subgroupOf_map_conjNormal Derived fullL₁ b.val (commonSylow_le_first b.property)

theorem second_invariant (b : fullB) :
    derivedL₂.map (automorphismEquiv b.val).toMonoidHom = derivedL₂ :=
  Subgroup.subgroupOf_map_conjNormal Derived fullL₂ b.val (commonSylow_le_second b.property)

theorem overlap_invariant (b : fullB) :
    derivedB.map (automorphismEquiv b.val).toMonoidHom = derivedB := by
  rw [derived_marking.2.2]
  exact Subgroup.subgroupOf_map_conjNormal Derived fullB b.val b.property

/-- The original full Borel acts on the source's literal derived inclusion amalgam. -/
def fullBorelAction (b : fullB) : RankTwoAmalgam.Iso simpleAmalgam simpleAmalgam :=
  RankTwoAmalgam.ofSubgroupsIso (automorphismEquiv b.val)
    derivedSylow_le_first derivedSylow_le_second derivedSylow_le_first derivedSylow_le_second
    (first_invariant b) (overlap_invariant b) (second_invariant b)

@[simp] theorem fullBorelAction_left_apply (b : fullB) (x : derivedL₁) :
    ((fullBorelAction b).left x).val.val = b.val * x.val.val * b.val⁻¹ :=
  automorphismEquiv_apply b.val x.val

@[simp] theorem fullBorelAction_middle_apply (b : fullB) (x : derivedB) :
    ((fullBorelAction b).middle x).val.val = b.val * x.val.val * b.val⁻¹ :=
  automorphismEquiv_apply b.val x.val

@[simp] theorem fullBorelAction_right_apply (b : fullB) (x : derivedL₂) :
    ((fullBorelAction b).right x).val.val = b.val * x.val.val * b.val⁻¹ :=
  automorphismEquiv_apply b.val x.val

theorem fullBorelAction_injective : Function.Injective fullBorelAction := by
  intro b c h
  apply Subtype.ext
  apply automorphismEquiv.injective
  have hL (x : derivedL₁) : automorphismEquiv b.val x.val = automorphismEquiv c.val x.val :=
    congrArg (fun e : RankTwoAmalgam.Iso simpleAmalgam simpleAmalgam => (e.left x).val) h
  have hR (x : derivedL₂) : automorphismEquiv b.val x.val = automorphismEquiv c.val x.val :=
    congrArg (fun e : RankTwoAmalgam.Iso simpleAmalgam simpleAmalgam => (e.right x).val) h
  have he : derivedL₁ ⊔ derivedL₂ ≤
      (automorphismEquiv b.val).toMonoidHom.eqLocus (automorphismEquiv c.val).toMonoidHom :=
    sup_le (fun x hx => hL ⟨x, hx⟩) (fun x hx => hR ⟨x, hx⟩)
  rw [derived_generation] at he
  exact MulEquiv.ext (fun x => he (Subgroup.mem_top x))

/-- The established word-amalgam bound transfers through the existing marked comparison. -/
theorem card_simpleAmalgamAut_le :
    Nat.card (RankTwoAmalgam.Iso simpleAmalgam simpleAmalgam) ≤ 64 := by
  rw [← Nat.card_congr
    (RankTwoAmalgam.automorphismConjEquiv ExceptionalRigidity.G2.derivedWordIso).toEquiv]
  exact card_binaryAmalgamAut_le

theorem card_fullB : Nat.card fullB = 64 := card_unipotent_binary
theorem card_derivedB : Nat.card derivedB = 32 := card_derivedSylow

theorem fullBorelAction_bijective : Function.Bijective fullBorelAction := by
  let : Finite (RankTwoAmalgam.Iso simpleAmalgam simpleAmalgam) :=
    Finite.of_equiv BinaryAmalgamAut
      (RankTwoAmalgam.automorphismConjEquiv ExceptionalRigidity.G2.derivedWordIso).toEquiv
  apply fullBorelAction_injective.bijective_of_nat_card_le
  rw [card_fullB]
  exact card_simpleAmalgamAut_le

/-- Conjugation is a homomorphism into compatible automorphisms with the usual composition order. -/
def fullBorelActionHom : fullB →* RankTwoAmalgam.Iso simpleAmalgam simpleAmalgam where
  toFun := fullBorelAction
  map_one' := by
    apply RankTwoAmalgam.Iso.ext
    all_goals
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change automorphismEquiv 1 (x : Derived) = (x : Derived)
      rw [map_one]
      rfl
  map_mul' b c := by
    apply RankTwoAmalgam.Iso.ext
    all_goals
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change automorphismEquiv (b.val * c.val) (x : Derived) =
        automorphismEquiv b.val (automorphismEquiv c.val (x : Derived))
      rw [map_mul]
      rfl

/-- The full Borel is the full compatible automorphism group of the marked derived amalgam. -/
def fullBorelActionEquiv : fullB ≃* RankTwoAmalgam.Iso simpleAmalgam simpleAmalgam :=
  MulEquiv.ofBijective fullBorelActionHom fullBorelAction_bijective

theorem action_left (b : fullB) (x : derivedL₁) :
    ((fullBorelActionEquiv b).left x).val.val = b.val * x.val.val * b.val⁻¹ :=
  fullBorelAction_left_apply b x

theorem action_middle (b : fullB) (x : derivedB) :
    ((fullBorelActionEquiv b).middle x).val.val = b.val * x.val.val * b.val⁻¹ :=
  fullBorelAction_middle_apply b x

theorem action_right (b : fullB) (x : derivedL₂) :
    ((fullBorelActionEquiv b).right x).val.val = b.val * x.val.val * b.val⁻¹ :=
  fullBorelAction_right_apply b x

/-- The first derived parabolic in the actual full carrier. -/
def innerP0 : Subgroup Full := derivedL₁.map Derived.subtype
/-- The second derived parabolic in the actual full carrier. -/
def innerP1 : Subgroup Full := derivedL₂.map Derived.subtype
/-- The common derived Borel in the actual full carrier. -/
def innerB : Subgroup Full := derivedB.map Derived.subtype

theorem innerP0_eq : innerP0 = fullL₁ ⊓ Derived := Subgroup.subgroupOf_map_subtype _ _
theorem innerP1_eq : innerP1 = fullL₂ ⊓ Derived := Subgroup.subgroupOf_map_subtype _ _
theorem innerB_eq : innerB = fullB ⊓ Derived := by
  rw [innerB, derived_marking.2.2, Subgroup.subgroupOf_map_subtype]

theorem innerP0_le_fullL₁ : innerP0 ≤ fullL₁ := innerP0_eq ▸ inf_le_left
theorem innerP1_le_fullL₂ : innerP1 ≤ fullL₂ := innerP1_eq ▸ inf_le_left
theorem innerB_le_fullB : innerB ≤ fullB := innerB_eq ▸ inf_le_left

theorem innerP0_inf_fullB : innerP0 ⊓ fullB = innerB := by
  rw [innerP0_eq, innerB_eq]
  ext x
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨commonSylow_le_first h.1, h.2⟩, h.1⟩⟩

theorem innerP1_inf_fullB : innerP1 ⊓ fullB = innerB := by
  rw [innerP1_eq, innerB_eq]
  ext x
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨commonSylow_le_second h.1, h.2⟩, h.1⟩⟩

theorem card_innerP0 : Nat.card innerP0 = 96 := by
  rw [innerP0, Subgroup.card_map_of_injective Derived.subtype_injective]
  exact card_derivedFirst

theorem card_innerP1 : Nat.card innerP1 = 96 := by
  rw [innerP1, Subgroup.card_map_of_injective Derived.subtype_injective]
  exact card_derivedSecond

private theorem join_fullB_eq (P Q : Subgroup Full) (hPQ : P ≤ Q) (hBQ : fullB ≤ Q)
    (hP : Nat.card P = 96) (hQ : Nat.card Q = 192) : P ⊔ fullB = Q := by
  apply Subgroup.eq_of_le_of_card_ge (sup_le hPQ hBQ)
  have h96 := Subgroup.card_dvd_of_le (show P ≤ P ⊔ fullB from le_sup_left)
  have h64 := Subgroup.card_dvd_of_le (show fullB ≤ P ⊔ fullB from le_sup_right)
  rw [hP] at h96
  rw [card_fullB] at h64
  have hd := Nat.lcm_dvd h96 h64
  norm_num at hd
  rw [hQ]
  exact Nat.le_of_dvd Nat.card_pos hd

theorem fullL₁_eq_innerP0_sup_fullB : fullL₁ = innerP0 ⊔ fullB :=
  (join_fullB_eq innerP0 fullL₁ innerP0_le_fullL₁ commonSylow_le_first
    card_innerP0 card_firstParabolic).symm

theorem fullL₂_eq_innerP1_sup_fullB : fullL₂ = innerP1 ⊔ fullB :=
  (join_fullB_eq innerP1 fullL₂ innerP1_le_fullL₂ commonSylow_le_second
    card_innerP1 Atlas.G2.BinaryCore.secondParabolic_card).symm

/-- The literal inclusion of the original derived Borel into the full Borel. -/
def innerBEmbedding : derivedB →* fullB where
  toFun b := ⟨b.val.val, by
    exact (show derivedB ≤ fullB.subgroupOf Derived from derived_marking.2.2.le) b.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem innerBEmbedding_apply (b : derivedB) : (innerBEmbedding b : Full) = b.val.val := rfl

theorem innerBEmbedding_injective : Function.Injective innerBEmbedding := by
  intro b c h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : fullB => (x : Full)) h

theorem innerBEmbedding_range_image : innerBEmbedding.range.map fullB.subtype = innerB := by
  rw [MonoidHom.map_range]
  change (Derived.subtype.comp derivedB.subtype).range = derivedB.map Derived.subtype
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem innerBEmbedding_range_index : innerBEmbedding.range.index = 2 := by
  have hc : Nat.card innerBEmbedding.range = 32 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective innerBEmbedding_injective).toEquiv]
    exact card_derivedB
  have h := innerBEmbedding.range.card_mul_index
  rw [hc, card_fullB] at h
  omega

theorem intermediate_fullB_eq (K : Subgroup fullB) (h : innerBEmbedding.range ≤ K) :
    K = innerBEmbedding.range ∨ K = ⊤ := by
  have hd := Subgroup.index_dvd_of_le h
  rw [innerBEmbedding_range_index] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact Or.inr (Subgroup.index_eq_one.mp he)
  · left
    apply (Subgroup.eq_of_le_of_card_ge h ?_).symm
    have hK := K.card_mul_index
    have hI := innerBEmbedding.range.card_mul_index
    rw [he] at hK
    rw [innerBEmbedding_range_index] at hI
    omega

end CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.G2NormalBase.Model
