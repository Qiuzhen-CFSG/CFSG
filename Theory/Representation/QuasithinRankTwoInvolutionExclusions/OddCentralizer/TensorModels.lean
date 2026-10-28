module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.TensorModels.Common
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.TensorModels.Orthogonal
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.TensorModels.Natural

/-!
# The two tensor models in G.11.2(9)

The actual natural binary S₃ plane is tensored with each of the distinct
four-dimensional modules: the five-point orthogonal A₅ core, extended to S₅,
and the scalar-restricted natural L₂(4) module with its specified Frobenius
extension. The latter extension is identified with S₅ by its action on five
F₄-lines, and the two extended representations are proved inequivalent.

On the orthogonal tensor, rank two occurs precisely for a transposition of
S₅ and identity in S₃. The S₃×A₅ subproduct has no such involution. Every
nonidentity involution on the natural tensor has rank four, including both
mixed-factor and outer involutions. The explicit cubic in S₃ is fixed-point
free on the surviving moved plane and makes its setwise stabilizer transitive.

The source-order APIs use an actual tensor-commuting equivalence together
with the product-group isomorphism. The calculations apply to all involutions;
no extra restriction on the elementary subgroup X is needed. They discharge
the case-(9) representation calculation in the parent's 6.2.19 assembly,
which retains transport from the original ambient action.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, G.11.2(9),
printed p.364 (PDF p.375), and 6.2.19, printed p.691 (PDF p.708).
-/

@[expose] public section

open scoped TensorProduct
namespace Representation.RankTwo.TensorModels
open BinaryPermutation.ThreeTensor

abbrev OrthogonalTensorSpace := Orthogonal.Space ⊗[ZMod 2] Plane
noncomputable def orthogonalTensor : Representation (ZMod 2) (Orthogonal.S5 × S3)
    OrthogonalTensorSpace := action Orthogonal.representation
abbrev NaturalTensorSpace := Natural.Space ⊗[ZMod 2] Plane
noncomputable def naturalTensor : Representation (ZMod 2) (Natural.GroupModel × S3)
    NaturalTensorSpace := action Natural.representation

lemma finrank_orthogonalTensorSpace : Module.finrank (ZMod 2) OrthogonalTensorSpace = 8 :=
  finrank_tensor Orthogonal.finrank_space
lemma finrank_naturalTensorSpace : Module.finrank (ZMod 2) NaturalTensorSpace = 8 :=
  finrank_tensor Natural.finrank_space

/-- Precisely the pure transpositions of S₅ have rank two on the orthogonal tensor. -/
lemma orthogonal_rank_two_iff (g : Orthogonal.S5 × S3) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (movedSpace orthogonalTensor g) = 2 ↔
      g.2 = 1 ∧ g.1.IsSwap := by
  constructor
  · intro hr
    have hs := first_factor_of_rank_two Orthogonal.representation Orthogonal.finrank_space g hr
    refine ⟨hs, ?_⟩
    have he : g = (g.1, 1) := Prod.ext rfl hs
    rw [he] at hr
    have hd : Module.finrank (ZMod 2) (movedSpace orthogonalTensor (g.1, 1)) =
        2 * Module.finrank (ZMod 2) (LinearMap.range (Orthogonal.representation g.1 - 1)) :=
      displacement_first Orthogonal.representation g.1
    have hh := hd.symm.trans hr
    apply (Orthogonal.rank_one_iff_swap g.1 (congrArg Prod.fst hg)).mp
    omega
  · rintro ⟨hs, hp⟩
    have he : g = (g.1, 1) := Prod.ext rfl hs
    rw [he]
    have hd : Module.finrank (ZMod 2) (movedSpace orthogonalTensor (g.1, 1)) =
        2 * Module.finrank (ZMod 2) (LinearMap.range (Orthogonal.representation g.1 - 1)) :=
      displacement_first Orthogonal.representation g.1
    exact hd.trans (by rw [Orthogonal.finrank_swap g.1 hp])

/-- The alternating subproduct has no rank-two involutions. -/
lemma orthogonal_alternating_not_rank_two (g : Orthogonal.S5 × S3)
    (hg : g * g = 1) (ha : g.1 ∈ alternatingGroup (Fin 5)) :
    Module.finrank (ZMod 2) (movedSpace orthogonalTensor g) ≠ 2 := by
  intro hr
  have hp := ((orthogonal_rank_two_iff g hg).mp hr).2.sign_eq
  rw [Equiv.Perm.mem_alternatingGroup.mp ha] at hp
  exact (by decide : (1 : ℤˣ) ≠ -1) hp

/-- In the natural L₂(4) extension every nonidentity tensor involution has rank four. -/
lemma natural_rank_four (g : Natural.GroupModel × S3) (hg : g * g = 1) (hne : g ≠ 1) :
    Module.finrank (ZMod 2) (movedSpace naturalTensor g) = 4 := by
  by_cases hs : g.2 = 1
  · have he : g = (g.1, 1) := Prod.ext rfl hs
    have hn : g.1 ≠ 1 := fun h => hne (Prod.ext h hs)
    rw [he]
    have hd : Module.finrank (ZMod 2) (movedSpace naturalTensor (g.1, 1)) =
        2 * Module.finrank (ZMod 2) (LinearMap.range (Natural.representation g.1 - 1)) :=
      displacement_first Natural.representation g.1
    exact hd.trans (by rw [Natural.finrank_involution g.1 (congrArg Prod.fst hg) hn])
  · exact finrank_mixed_involution Natural.representation Natural.finrank_space g hg hs

lemma natural_not_rank_two (g : Natural.GroupModel × S3) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (movedSpace naturalTensor g) ≠ 2 := by
  by_cases h : g = 1
  · subst g
    have hz : movedSpace naturalTensor (1 : Natural.GroupModel × S3) = ⊥ :=
      LinearMap.range_eq_bot.mpr (sub_eq_zero.mpr (map_one naturalTensor))
    have hd : Module.finrank (ZMod 2) (movedSpace naturalTensor (1 : Natural.GroupModel × S3)) = 0 :=
      Submodule.finrank_eq_zero.mpr hz
    exact fun hr => (by decide : (0 : ℕ) ≠ 2) (hd.symm.trans hr)
  · rw [natural_rank_four g hg h]
    decide

/-- The concrete order-three element in the S₃ factor centralizes every rank-two actor,
and has no nonzero fixed vectors even on the whole tensor space. -/
lemma orthogonal_rank_two_cubic (g : Orthogonal.S5 × S3) (hg : g * g = 1)
    (hr : Module.finrank (ZMod 2) (movedSpace orthogonalTensor g) = 2) :
    ∃ c : Orthogonal.S5 × S3, c.1 = 1 ∧ orderOf c = 3 ∧ Commute c g ∧
      (∀ z : OrthogonalTensorSpace, orthogonalTensor c z = z → z = 0) ∧
      StabilizerTransitive orthogonalTensor (movedSpace orthogonalTensor g) := by
  have hs := ((orthogonal_rank_two_iff g hg).mp hr).1
  have he : g = (g.1, 1) := Prod.ext rfl hs
  refine ⟨(1, cubicElement), rfl, ?_, ?_, cubic_fixed_free Orthogonal.representation, ?_⟩
  · simp only [Prod.orderOf, orderOf_one, cubicElement_order, Nat.lcm_one_left]
  · rw [he]
    change (1, cubicElement) * (g.1, 1) = (g.1, 1) * (1, cubicElement)
    simp
  · rw [he] at hr ⊢
    exact stabilizerTransitive_first Orthogonal.representation g.1 hr

/-- The actual A₅ tensor is the restriction along the first factor's subgroup embedding. -/
noncomputable def orthogonalAlternatingTensor :
    Representation (ZMod 2) (Imprimitive.OrthogonalA5.Alternating × S3) OrthogonalTensorSpace :=
  action Imprimitive.OrthogonalA5.representation

lemma orthogonalAlternating_not_rank_two (g : Imprimitive.OrthogonalA5.Alternating × S3)
    (hg : g * g = 1) :
    Module.finrank (ZMod 2) (movedSpace orthogonalAlternatingTensor g) ≠ 2 := by
  have h1 : g.1.val * g.1.val = 1 :=
    congrArg (fun x : Imprimitive.OrthogonalA5.Alternating × S3 => x.1.val) hg
  have h2 : g.2 * g.2 = 1 := congrArg (fun x : Imprimitive.OrthogonalA5.Alternating × S3 => x.2) hg
  exact orthogonal_alternating_not_rank_two (g.1.val, g.2) (Prod.ext h1 h2) g.1.property

/-- The natural L₂(4) tensor with no outer extension, on the original SL₂ carrier. -/
noncomputable def naturalBaseTensor :
    Representation (ZMod 2) (SL2FourNatural.SL × S3) NaturalTensorSpace :=
  action (Natural.representation.comp Natural.inclusion)

lemma naturalBase_not_rank_two (g : SL2FourNatural.SL × S3) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (movedSpace naturalBaseTensor g) ≠ 2 := by
  have h1 : g.1 * g.1 = 1 := congrArg Prod.fst hg
  have h2 : g.2 * g.2 = 1 := congrArg Prod.snd hg
  apply natural_not_rank_two (Natural.inclusion g.1, g.2)
  apply Prod.ext
  · change Natural.inclusion g.1 * Natural.inclusion g.1 = 1
    rw [← map_mul, h1, map_one]
  · exact h2
section SourceOrder
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- The source order of both the group factors and the tensor factors. -/
noncomputable def sourceTensor (ρ : Representation (ZMod 2) H W) :
    Representation (ZMod 2) (S3 × H) (Plane ⊗[ZMod 2] W) :=
  Representation.tprod
    ((BinaryPermutation.coreRepresentation (Fin 3)).comp (MonoidHom.fst _ _))
    (ρ.comp (MonoidHom.snd _ _))

/-- Commuting the tensor factors intertwines the literal product-group isomorphism. -/
noncomputable def sourceTensorEquiv (ρ : Representation (ZMod 2) H W) :
    Representation.Equiv (sourceTensor ρ)
      ((action ρ).comp ((MulEquiv.prodComm : (S3 × H) ≃* (H × S3))).toMonoidHom) where
  toLinearEquiv := _root_.TensorProduct.comm (ZMod 2) Plane W
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul n w =>
      change _root_.TensorProduct.comm (ZMod 2) Plane W
        (BinaryPermutation.coreRepresentation (Fin 3) g.1 n ⊗ₜ[ZMod 2] ρ g.2 w) =
        action ρ (g.2, g.1) (_root_.TensorProduct.comm (ZMod 2) Plane W (n ⊗ₜ[ZMod 2] w))
      simp
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

lemma sourceTensor_rank (ρ : Representation (ZMod 2) H W) (g : S3 × H) :
    Module.finrank (ZMod 2) (movedSpace (sourceTensor ρ) g) =
      Module.finrank (ZMod 2) (movedSpace (action ρ) (g.2, g.1)) :=
  finrank_movedSpace_transport (sourceTensor ρ) (action ρ) ((MulEquiv.prodComm : (S3 × H) ≃* (H × S3)))
    (sourceTensorEquiv ρ).toLinearEquiv
    (fun a z => LinearMap.congr_fun ((sourceTensorEquiv ρ).isIntertwining' a) z) g
end SourceOrder

/-- The exact rank-two classification with S₃ and its natural module first, as in G.11.2(9). -/
lemma source_orthogonal_rank_two_iff (g : S3 × Orthogonal.S5) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (movedSpace (sourceTensor Orthogonal.representation) g) = 2 ↔
      g.1 = 1 ∧ g.2.IsSwap := by
  rw [sourceTensor_rank]
  exact orthogonal_rank_two_iff (g.2, g.1)
    (Prod.ext (congrArg Prod.snd hg) (congrArg Prod.fst hg))

/-- The natural L₂(4) tensor, with the source order of factors, has no rank-two involution. -/
lemma source_natural_not_rank_two (g : S3 × Natural.GroupModel) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (movedSpace (sourceTensor Natural.representation) g) ≠ 2 := by
  rw [sourceTensor_rank]
  exact natural_not_rank_two (g.2, g.1)
    (Prod.ext (congrArg Prod.snd hg) (congrArg Prod.fst hg))

/-- The surviving model has the required transitive moved-plane stabilizer. This is
exactly the case-(9) input consumed by the final 6.2.19 exclusion. -/
lemma source_orthogonal_stabilizerTransitive (g : S3 × Orthogonal.S5) (hg : g * g = 1)
    (hr : Module.finrank (ZMod 2)
      (movedSpace (sourceTensor Orthogonal.representation) g) = 2) :
    StabilizerTransitive (sourceTensor Orthogonal.representation)
      (movedSpace (sourceTensor Orthogonal.representation) g) := by
  apply stabilizerTransitive_transport (sourceTensor Orthogonal.representation) orthogonalTensor
    ((MulEquiv.prodComm : (S3 × Orthogonal.S5) ≃* (Orthogonal.S5 × S3))) (sourceTensorEquiv Orthogonal.representation).toLinearEquiv
    (fun a z => LinearMap.congr_fun ((sourceTensorEquiv Orthogonal.representation).isIntertwining' a) z)
  have hs : (g.2, g.1) * (g.2, g.1) = 1 :=
    Prod.ext (congrArg Prod.snd hg) (congrArg Prod.fst hg)
  obtain ⟨c, _, _, _, _, hc⟩ := orthogonal_rank_two_cubic (g.2, g.1) hs
    ((sourceTensor_rank Orthogonal.representation g).symm.trans hr)
  exact hc

end Representation.RankTwo.TensorModels

namespace Representation.RankTwo.TensorModels
/-- The two S₅ extensions are inequivalent: a marked transposition has ranks one and two. -/
lemma extensions_inequivalent :
    ¬ Nonempty (Representation.Equiv Orthogonal.representation
      (Natural.representation.comp Natural.groupEquiv.symm.toMonoidHom)) := by
  rintro ⟨e⟩
  let p : Orthogonal.S5 := Equiv.swap 3 4
  have horth : Module.finrank (ZMod 2) (movedSpace Orthogonal.representation p) = 1 :=
    Orthogonal.finrank_swap p ⟨3, 4, by decide, rfl⟩
  have hnat : Module.finrank (ZMod 2)
      (movedSpace (Natural.representation.comp Natural.groupEquiv.symm.toMonoidHom) p) = 2 := by
    have he : (Natural.representation.comp Natural.groupEquiv.symm.toMonoidHom) p =
        SL2FourNatural.frobeniusLinear.toLinearMap := by
      change Natural.representation (Natural.groupEquiv.symm (Equiv.swap 3 4)) = _
      rw [← Natural.marked_field, MulEquiv.symm_apply_apply, Natural.representation_field]
    rw [movedSpace, he]
    exact Natural.finrank_frobenius
  have he := finrank_movedSpace_transport Orthogonal.representation
    (Natural.representation.comp Natural.groupEquiv.symm.toMonoidHom)
    (MulEquiv.refl Orthogonal.S5) e.toLinearEquiv
    (fun g z => LinearMap.congr_fun (e.isIntertwining' g) z) p
  have he' : Module.finrank (ZMod 2) (movedSpace Orthogonal.representation p) =
      Module.finrank (ZMod 2)
        (movedSpace (Natural.representation.comp Natural.groupEquiv.symm.toMonoidHom) p) := he
  exact (by decide : (1 : ℕ) ≠ 2) ((horth.symm.trans he').trans hnat)
end Representation.RankTwo.TensorModels