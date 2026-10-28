module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The full linear action on a marked flag subspace

The marking is the actual conjugation representation of L on the elementary
abelian subgroup V. Surjectivity on V extends every automorphism of a flag
subspace, using the two-block action of its linear stabilizer. This proves
N_L(V_i) induces GL(V_i), and the literal ambient centralizer factorization.

Source: Aschbacher–Smith, Lemma 12.8.5(2), printed p.850 (PDF p.867).
The full natural action is the earlier input 12.8.3(1).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.NormalGeometry
variable {G : Type*} [Group G] {V L : Subgroup G} [IsElementaryAbelian 2 V]

/-- A marking of the genuine natural action, including its actual two-core kernel. -/
structure NaturalAction (L V : Subgroup G) [IsElementaryAbelian 2 V] where
  action : L →* BinaryLinear.GL (Additive V)
  surjective : Function.Surjective action
  conjugation : ∀ (l : L) (v : Additive V),
    ((action l v).toMul : G) = (l : G) * (v.toMul : G) * (l : G)⁻¹
  kernel : action.ker = pCore 2 L

/-- The actual subspace A∩V, with the canonical binary structure. -/
def space (A : Subgroup G) : Submodule (ZMod 2) (Additive V) :=
  AddSubgroup.toZModSubmodule 2 (A.subgroupOf V).toAddSubgroup

@[simp] theorem mem_space (A : Subgroup G) (v : Additive V) :
    v ∈ space (V := V) A ↔ (v.toMul : G) ∈ A := Iff.rfl

/-- The conjugation marking detects the actual relative normalizer. -/
theorem action_mem_parabolic_iff (d : NaturalAction L V) (A : Subgroup G)
    (hAV : A ≤ V) (l : L) :
    d.action l ∈ BinaryLinear.parabolic (space (V := V) A) ↔
      (l : G) ∈ normalizer (A : Set G) := by
  constructor
  · intro h
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have := (h (Additive.ofMul ⟨a, hAV ha⟩)).mpr ha
      change ((d.action l (Additive.ofMul ⟨a, hAV ha⟩)).toMul : G) ∈ A at this
      rwa [d.conjugation] at this
    · intro ha
      have hi := (BinaryLinear.parabolic (space (V := V) A)).inv_mem h
      have := (hi (Additive.ofMul ⟨_, hAV ha⟩)).mpr ha
      change (((d.action l)⁻¹ (Additive.ofMul ⟨_, hAV ha⟩)).toMul : G) ∈ A at this
      rw [← map_inv, d.conjugation] at this
      simpa [mul_assoc] using this
  · intro h v
    change ((d.action l v).toMul : G) ∈ A ↔ (v.toMul : G) ∈ A
    rw [d.conjugation]
    exact (mem_normalizer_iff.mp h _).symm

/-- The representation really normalizes the original ambient seed. -/
theorem natural_normalizes (d : NaturalAction L V) : L ≤ normalizer (V : Set G) := by
  intro l hl
  apply (action_mem_parabolic_iff d V le_rfl ⟨l, hl⟩).mp
  intro v
  exact iff_of_true (d.action ⟨l, hl⟩ v).toMul.property v.toMul.property

/-- The intrinsic automorphism of the subspace from an ambient normalizer element. -/
def normalizerLinear (A : Subgroup G) (hAV : A ≤ V)
    (g : normalizer (A : Set G)) : BinaryLinear.GL (space (V := V) A) := by
  let e : Additive A ≃+ space (V := V) A :=
    { toFun a := ⟨Additive.ofMul ⟨a.toMul, hAV a.toMul.property⟩, a.toMul.property⟩
      invFun v := Additive.ofMul ⟨v.val.toMul, v.property⟩
      left_inv a := rfl
      right_inv v := rfl
      map_add' _ _ := rfl }
  let f := e.symm.trans (((Subgroup.normalizerMonoidHom A) g).toAdditive.trans e)
  exact { f with map_smul' := ZMod.map_smul f }

@[simp] theorem normalizerLinear_apply (A : Subgroup G) (hAV : A ≤ V)
    (g : normalizer (A : Set G)) (v : space (V := V) A) :
    (((normalizerLinear A hAV g v).val).toMul : G) =
      (g : G) * (v.val.toMul : G) * (g : G)⁻¹ := rfl

/-- All linear automorphisms of the actual subspace are induced by N_L(A). -/
theorem normalizer_full_action (d : NaturalAction L V) (A : Subgroup G)
    (hAV : A ≤ V) (a : BinaryLinear.GL (space (V := V) A)) :
    ∃ l : L, (l : G) ∈ normalizer (A : Set G) ∧
      ∀ v : space (V := V) A, d.action l v = a v := by
  obtain ⟨b, hb⟩ := BinaryLinear.SmallParabolicLevi.blockAction_surjective
    (space (V := V) A) (a, 1)
  obtain ⟨l, hl⟩ := d.surjective b.val
  refine ⟨l, (action_mem_parabolic_iff d A hAV l).mp (hl ▸ b.property), ?_⟩
  intro v
  have hs := congrArg Prod.fst hb
  have hv := congrArg (fun f : BinaryLinear.GL (space (V := V) A) => (f v).val) hs
  change b.val v = (a v : Additive V) at hv
  rw [hl]
  exact hv

/-- Any ambient normalizer induces the same conjugation on A as an element of N_L(A). -/
theorem normalizer_action_image (d : NaturalAction L V) (A : Subgroup G)
    (hAV : A ≤ V) :
    ∀ g ∈ normalizer (A : Set G), ∃ l ∈ L ⊓ normalizer (A : Set G),
      ∀ a ∈ A, g * a * g⁻¹ = l * a * l⁻¹ := by
  intro g hg
  obtain ⟨l, hl, he⟩ := normalizer_full_action d A hAV (normalizerLinear A hAV ⟨g, hg⟩)
  refine ⟨l, ⟨l.property, hl⟩, ?_⟩
  intro a ha
  have h := congrArg (fun v : Additive V => (v.toMul : G))
    (he ⟨Additive.ofMul ⟨a, hAV ha⟩, ha⟩)
  rw [d.conjugation] at h
  exact h.symm

/-- Literal ambient multiplication in the normalizer factorization. -/
theorem normalizer_factorization (d : NaturalAction L V) (A : Subgroup G)
    (hAV : A ≤ V) :
    (normalizer (A : Set G) : Set G) =
      (centralizer (A : Set G) : Set G) * (L ⊓ normalizer (A : Set G) : Subgroup G) := by
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨l, hl, he⟩ := normalizer_action_image d A hAV g hg
    have hc : l⁻¹ * g ∈ centralizer (A : Set G) := by
      intro a ha
      have h := congrArg (fun x : G => l⁻¹ * x * l) (he a ha)
      have h' : (l⁻¹ * g) * a * (l⁻¹ * g)⁻¹ = a := by
        simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
          inv_mul_cancel, mul_one] using h
      exact (mul_inv_eq_iff_eq_mul.mp h').symm
    have hc' : g * l⁻¹ ∈ centralizer (A : Set G) := by
      have hnorm := ((normal_subgroupOf_iff_le_normalizer
        (centralizer_le_normalizer (A : Set G))).mp inferInstance) hl.2
      have hmem := (mem_normalizer_iff.mp hnorm (l⁻¹ * g)).mp hc
      simpa only [mul_inv_cancel_left] using hmem
    exact ⟨g * l⁻¹, hc', l, hl, inv_mul_cancel_right g l⟩
  · rintro g ⟨c, hc, l, hl, rfl⟩
    exact (normalizer (A : Set G)).mul_mem (centralizer_le_normalizer _ hc) hl.2

end CFSG.Quasithin.Chapter12.Section08.NormalGeometry
