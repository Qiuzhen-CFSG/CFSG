module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.Basic
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.SingerExclusion
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.LinearFrame.Clifford
public import Theory.SpecificGroups.SL3.SplitMonomial.InvariantBasis

/-!
# Faithful special-linear realization of the unitary frame problem

The determinant-one equation realizes each special-unitary matrix as an SL₃
matrix. This is injective, agrees with the original natural action, and sends
the actual join to the join with the image of the given involution. Pulling
back an abelian relatively normal subgroup preserves normality and
commutativity. If the pullback acted scalarly, its image would be central
in the whole SL₃ group, which contradicts noncentrality of the supplied image.
Thus the abelian-normal frame construction applies without losing scalars.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

public section
open Matrix BenderSuzuki.MatrixGroups Representation Subgroup
open scoped IsMulCommutative
namespace UnitaryThree.OddTorusNormalizer.NonabelianFrame
variable {E : Type*} [Field E]

/-- The determinant-one realization in SL₃, without quotienting any scalars. -/
@[expose] def specialLinearEmbedding (J : HermitianForm 3 E) :
    J.specialSubgroup →* SpecialLinearGroup (Fin 3) E where
  toFun a := ⟨a.val.val, congrArg Units.val ((J.mem_specialSubgroup_iff a.val).mp a.property).2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The realization retains every special-unitary matrix. -/
theorem specialLinearEmbedding_injective (J : HermitianForm 3 E) :
    Function.Injective (specialLinearEmbedding J) := by
  intro a b h
  exact Subtype.ext (Units.ext (congrArg Subtype.val h))

/-- The SU₃ and SL₃ realizations act by exactly the same linear map. -/
theorem specialLinearEmbedding_natural (J : HermitianForm 3 E) (a : J.specialSubgroup) :
    specialLinearNatural 3 (specialLinearEmbedding J a) = naturalRepresentation J a := rfl

/-- The actual normalized join maps to the join with the actual image of t. -/
theorem specialLinearEmbedding_map_join (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (t : J.specialSubgroup) :
    (H ⊔ zpowers t).map (specialLinearEmbedding J) =
      H.map (specialLinearEmbedding J) ⊔ zpowers (specialLinearEmbedding J t) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]

/-- A noncentral abelian normal subgroup of the SL₃ image pulls back to a
nonscalar abelian normal subgroup of the original SU₃ join. Clifford theory
then produces the required frame over E. -/
theorem exists_preserved_linear_frame_of_specialLinear_abelian_normal [Finite E]
    (J : HermitianForm 3 E) (n : ℕ) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (hna : ¬ IsMulCommutative H) (t : J.specialSubgroup) (ht : orderOf t = 2)
    (hA : SL3.SplitMonomial.HasNoncentralAbelianNormal
      ((H ⊔ zpowers t).map (specialLinearEmbedding J))) :
    ∃ C : GL (Fin 3) E, PreservesLines J (H ⊔ zpowers t) C := by
  let f := specialLinearEmbedding J
  have hf : Function.Injective f := specialLinearEmbedding_injective J
  let K := H ⊔ zpowers t
  obtain ⟨B, hB, hBn, hBc, hBs⟩ := hA
  let : IsMulCommutative B := hBc
  let A := B.comap f
  have hK : (K.map f).comap f = K := comap_map_eq_self (by rw [f.ker_eq_bot hf]; exact bot_le)
  have hAK : A ≤ K := hK ▸ (comap_mono hB)
  have hAn : (A.subgroupOf K).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hAK).mpr
    intro g hg
    exact B.le_normalizer_comap f
      (((normal_subgroupOf_iff_le_normalizer hB).mp hBn) (mem_map_of_mem f hg))
  have hAc : IsMulCommutative A := B.comap_injective_isMulCommutative hf
  have hAs : ¬ ∀ a : A, ∃ c : E, naturalRepresentation J a.val = c • LinearMap.id := by
    intro hs
    apply hBs
    intro b hb
    obtain ⟨a, ha, he⟩ := hB hb
    obtain ⟨c, hc⟩ := hs ⟨a, by change f a ∈ B; rwa [he]⟩
    have hc' : specialLinearNatural 3 b = c • LinearMap.id := by
      rw [← he]
      exact hc
    rw [Subgroup.mem_center_iff]
    intro z
    apply specialLinearNatural_injective 3
    simp only [map_mul, hc']
    ext v
    simp [Module.End.mul_apply]
  exact exists_preserved_linear_frame_of_abelian_normal J n hcard H hodd hna t ht
    A hAK hAn hAc hAs

end UnitaryThree.OddTorusNormalizer.NonabelianFrame
