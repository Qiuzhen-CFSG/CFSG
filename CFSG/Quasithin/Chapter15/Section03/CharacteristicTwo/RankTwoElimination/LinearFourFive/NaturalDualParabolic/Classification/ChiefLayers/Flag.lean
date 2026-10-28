module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.RadicalLayer

/-!
# The ordered coordinate flag of the natural-plus-dual point parabolic

In the original coordinates on U_L, the three subgroups are the images of
⟨x⟩ × 0, V × 0, and V × ann(x). Their invariance proves relative normality
in P, and their orders distinguish the first two intervals. The genuine
radical quotient of order eight distinguishes O₂(L) from O₂(P). In particular
this construction does not replace W_L by a split model or remove its centre.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130.
-/

@[expose] public section
open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra.BinaryFivePointStabilizer
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- A subspace transported through the given embedding, in the original group. -/
def coordinateSubgroup (h : NaturalDual d L)
    (S : Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4))) : Subgroup G :=
  S.toAddSubgroup.toSubgroup.map (embed h)

/-- The actual coordinate isomorphism onto the embedded subgroup. -/
noncomputable def coordinateEquiv (h : NaturalDual d L)
    (S : Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4))) :
    Multiplicative S ≃* coordinateSubgroup h S :=
  S.toAddSubgroup.toSubgroup.equivMapOfInjective (embed h) (embed_injective h)

@[simp] theorem coordinateEquiv_apply (h : NaturalDual d L)
    (S : Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4)))
    (v : Multiplicative S) :
    (coordinateEquiv h S v : G) = embed h (Multiplicative.ofAdd v.toAdd.val) := rfl

@[simp] theorem embed_mem_coordinateSubgroup (h : NaturalDual d L)
    (S : Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4)))
    (v : Space 4 × Module.Dual (ZMod 2) (Space 4)) :
    embed h (Multiplicative.ofAdd v) ∈ coordinateSubgroup h S ↔ v ∈ S :=
  mem_map_iff_mem (embed_injective h)

theorem coordinateSubgroup_le_module (h : NaturalDual d L)
    (S : Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4))) :
    coordinateSubgroup h S ≤ spanCommutator d L := by
  rintro _ ⟨v, _, rfl⟩
  exact embed_mem h v.toAdd

theorem coordinateSubgroup_mono (h : NaturalDual d L)
    {S T : Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4))}
    (hST : S ≤ T) : coordinateSubgroup h S ≤ coordinateSubgroup h T :=
  map_mono hST

/-- Coordinate invariance is relative normalization by the actual parabolic. -/
theorem coordinateSubgroup_normalized (h : NaturalDual d L) (x : Space 4)
    (S : Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4)))
    (hS : ∀ (g : pointStabilizer x) (v : Space 4 × Module.Dual (ZMod 2) (Space 4)),
      v ∈ S → BinaryLinear.NaturalDualFlag.action g.val v ∈ S) :
    point h x ≤ normalizer (coordinateSubgroup h S : Set G) := by
  apply le_normalizer_iff.mpr
  rintro p hp _ ⟨v, hv, rfl⟩
  have he := embed_conj h (⟨p, point_le h x hp⟩ : L) v.toAdd
  change p * embed h v * p⁻¹ = _ at he
  rw [he]
  exact (embed_mem_coordinateSubgroup h S _).mpr (hS (pointActor h x ⟨p, hp⟩) v.toAdd hv)

/-- The marked fixed line, as a subspace of the original direct sum. -/
def lineSpace (x : Space 4) :
    Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4)) :=
  (line x).prod ⊥

/-- The original natural summand. -/
def naturalSpace : Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4)) :=
  (⊤ : Submodule (ZMod 2) (Space 4)).prod ⊥

/-- The natural summand together with the annihilator of the marked point. -/
def mixedSpace (x : Space 4) :
    Submodule (ZMod 2) (Space 4 × Module.Dual (ZMod 2) (Space 4)) :=
  (⊤ : Submodule (ZMod 2) (Space 4)).prod (annihilator x)

/-- A = image(⟨x⟩ × 0). -/
def lineSubgroup (h : NaturalDual d L) (x : Space 4) : Subgroup G :=
  coordinateSubgroup h (lineSpace x)

/-- B = image(V × 0). -/
def naturalSubgroup (h : NaturalDual d L) : Subgroup G :=
  coordinateSubgroup h naturalSpace

/-- C = image(V × ann(x)). -/
def mixedSubgroup (h : NaturalDual d L) (x : Space 4) : Subgroup G :=
  coordinateSubgroup h (mixedSpace x)

/-- Forgetting the zero dual coordinate identifies the first space with the line. -/
def lineSpaceEquiv (x : Space 4) : lineSpace x ≃ₗ[ZMod 2] line x where
  toFun v := ⟨v.val.1, v.property.1⟩
  invFun v := ⟨(v.val, 0), v.property, Submodule.zero_mem _⟩
  left_inv v := by apply Subtype.ext; exact Prod.ext rfl (show v.val.2 = 0 from v.property.2).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinates on the actual natural summand. -/
def naturalSpaceEquiv : naturalSpace ≃ₗ[ZMod 2] Space 4 where
  toFun v := v.val.1
  invFun v := ⟨(v, 0), Submodule.mem_top, Submodule.zero_mem _⟩
  left_inv v := by apply Subtype.ext; exact Prod.ext rfl (show v.val.2 = 0 from v.property.2).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinates on the mixed space, retaining the actual annihilator. -/
def mixedSpaceEquiv (x : Space 4) : mixedSpace x ≃ₗ[ZMod 2] (Space 4 × annihilator x) where
  toFun v := (v.val.1, ⟨v.val.2, v.property.2⟩)
  invFun v := ⟨(v.1, v.2.val), Submodule.mem_top, v.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lineSubgroup_le_natural (h : NaturalDual d L) (x : Space 4) :
    lineSubgroup h x ≤ naturalSubgroup h :=
  coordinateSubgroup_mono h (fun _ hv => ⟨Submodule.mem_top, hv.2⟩)

theorem naturalSubgroup_le_mixed (h : NaturalDual d L) (x : Space 4) :
    naturalSubgroup h ≤ mixedSubgroup h x :=
  coordinateSubgroup_mono h (fun v hv => ⟨hv.1, by
    rw [show v.2 = 0 from hv.2]
    exact Submodule.zero_mem _⟩)

theorem lineSubgroup_card (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    Nat.card (lineSubgroup h x) = 2 := by
  unfold lineSubgroup
  rw [← Nat.card_congr (coordinateEquiv h (lineSpace x)).toEquiv]
  change Nat.card (lineSpace x) = 2
  rw [Nat.card_congr (lineSpaceEquiv x).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_span_singleton hx, Nat.card_zmod, pow_one]

theorem naturalSubgroup_card (h : NaturalDual d L) : Nat.card (naturalSubgroup h) = 16 := by
  unfold naturalSubgroup
  rw [← Nat.card_congr (coordinateEquiv h naturalSpace).toEquiv]
  change Nat.card naturalSpace = 16
  rw [Nat.card_congr naturalSpaceEquiv.toEquiv]
  simp [Space, Nat.card_eq_fintype_card]

theorem mixedSubgroup_card (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    Nat.card (mixedSubgroup h x) = 128 := by
  unfold mixedSubgroup
  rw [← Nat.card_congr (coordinateEquiv h (mixedSpace x)).toEquiv]
  change Nat.card (mixedSpace x) = 128
  rw [Nat.card_congr (mixedSpaceEquiv x).toEquiv, Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := annihilator x),
    Nat.card_zmod, annihilator_finrank hx]
  simp [Space, Nat.card_eq_fintype_card]

theorem lineSubgroup_normalized (h : NaturalDual d L) (x : Space 4) :
    point h x ≤ normalizer (lineSubgroup h x : Set G) := by
  apply coordinateSubgroup_normalized
  intro g v hv
  refine ⟨?_, ?_⟩
  · rw [BinaryLinear.NaturalDualFlag.action_fst, fixes_line x g v.1 hv.1]
    exact hv.1
  · apply LinearMap.ext
    intro y
    rw [BinaryLinear.NaturalDualFlag.action_snd, show v.2 = 0 from hv.2]
    rfl

theorem naturalSubgroup_normalized (h : NaturalDual d L) (x : Space 4) :
    point h x ≤ normalizer (naturalSubgroup h : Set G) := by
  apply coordinateSubgroup_normalized
  intro g v hv
  refine ⟨Submodule.mem_top, ?_⟩
  apply LinearMap.ext
  intro y
  rw [BinaryLinear.NaturalDualFlag.action_snd, show v.2 = 0 from hv.2]
  rfl

theorem mixedSubgroup_normalized (h : NaturalDual d L) (x : Space 4) :
    point h x ≤ normalizer (mixedSubgroup h x : Set G) := by
  apply coordinateSubgroup_normalized
  intro g v hv
  refine ⟨Submodule.mem_top, ?_⟩
  change (BinaryLinear.NaturalDualFlag.action g.val v).2 x = 0
  rw [BinaryLinear.NaturalDualFlag.action_snd, show g.val.symm x = x from (g⁻¹).property]
  exact hv.2

instance lineSubgroup_normal (h : NaturalDual d L) (x : Space 4) :
    ((lineSubgroup h x).subgroupOf (point h x)).Normal :=
  normal_subgroupOf_of_le_normalizer (lineSubgroup_normalized h x)

instance naturalSubgroup_normal (h : NaturalDual d L) (x : Space 4) :
    ((naturalSubgroup h).subgroupOf (point h x)).Normal :=
  normal_subgroupOf_of_le_normalizer (naturalSubgroup_normalized h x)

instance mixedSubgroup_normal (h : NaturalDual d L) (x : Space 4) :
    ((mixedSubgroup h x).subgroupOf (point h x)).Normal :=
  normal_subgroupOf_of_le_normalizer (mixedSubgroup_normalized h x)

instance module_normal (h : NaturalDual d L) (x : Space 4) :
    ((spanCommutator d L).subgroupOf (point h x)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((point_le h x).trans (normalizer_commutator_ge_right _ _))

instance componentCore_normal (h : NaturalDual d L) (x : Space 4) :
    ((L.pCoreIn 2).subgroupOf (point h x)).Normal :=
  normal_subgroupOf_of_le_normalizer ((point_le h x).trans
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))))

instance pointCore_normal (h : NaturalDual d L) (x : Space 4) :
    (((point h x).pCoreIn 2).subgroupOf (point h x)).Normal :=
  normal_subgroupOf_of_le_normalizer ((point h x).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (point h x) (pCore 2 (point h x))))

/-- The strict last interval follows from its genuine order-eight quotient. -/
theorem componentCore_lt_pointCore [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) : L.pCoreIn 2 < (point h x).pCoreIn 2 := by
  refine lt_of_le_not_ge (componentCore_le_pointCore h x) ?_
  intro he
  have ht : oldCoreInCore h x = ⊤ := by
    apply top_unique
    intro q _
    exact he (mem_map.mpr ⟨q.val, q.property, rfl⟩)
  have hc := coreQuotient_card h hx
  rw [ht] at hc
  have h1 : Nat.card (pCore 2 (point h x) ⧸ (⊤ : Subgroup (pCore 2 (point h x)))) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
  omega

/-- The ordered configuration in the original ambient group. -/
theorem ordered_flag [Finite G] (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    lineSubgroup h x < naturalSubgroup h ∧
      naturalSubgroup h < mixedSubgroup h x ∧
      mixedSubgroup h x ≤ spanCommutator d L ∧
      spanCommutator d L ≤ L.pCoreIn 2 ∧ L.pCoreIn 2 < (point h x).pCoreIn 2 := by
  refine ⟨lt_of_le_of_ne (lineSubgroup_le_natural h x) ?_,
    lt_of_le_of_ne (naturalSubgroup_le_mixed h x) ?_,
    coordinateSubgroup_le_module h (mixedSpace x), module_le_componentCore h x hU,
    componentCore_lt_pointCore h hx⟩
  · intro he
    have hh := congrArg (fun S : Subgroup G => Nat.card S) he
    rw [lineSubgroup_card h hx, naturalSubgroup_card h] at hh
    omega
  · intro he
    have hh := congrArg (fun S : Subgroup G => Nat.card S) he
    rw [naturalSubgroup_card h, mixedSubgroup_card h hx] at hh
    omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
end
