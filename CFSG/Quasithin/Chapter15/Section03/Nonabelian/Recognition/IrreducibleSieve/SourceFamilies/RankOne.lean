module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.Components
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.SourceAction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases.RankOne
public import CFSG.Quasithin.ChapterG.Section09.Basic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.ClassicalModels

/-!
# The actual binary rank-one branch of the source irreducible action

The original actor bounds the automorphism rank of the normal component.
The complete small-degree SL₂ classification then gives the natural,
Hermitian or exceptional triple tensor action. The source quadratic form
excludes the natural action. The marked central Sylow involution belongs to
the component, and its displacement rank excludes both tensor actions.
This avoids any extra comparison with a minus orthogonal group.

Source: Aschbacher--Smith, G.9.3(6),(7),(16) and15.3.58,
printed pp.354--357 and1149.
-/

public section

open Subgroup Representation
open scoped MatrixGroups MonoidAlgebra IsMulCommutative
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
open Representation.SL2

attribute [local instance] BinarySmall.fixedBinaryAlgebra BinarySmall.spaceBinaryModule

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- Every binary SL₂ component is incompatible with the actual source action. -/
theorem SourceData.not_binary_rankOne_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (n : ℕ) (hn : 2 ≤ n)
    (e : K ≃* SL(2,GaloisField 2 n)) : False := by
  let : Representation.IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  have hnorm : X ≤ normalizer (K : Set H) := by
    rw [normalizer_eq_top_iff.mpr hK.normal]
    exact le_top
  have hm : s + 1 ≤ n := by
    have hr := h.setup.rank_le_automorphisms hnorm
    have hb : primeRank 2 (MulAut K) ≤ n := by
      rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)]
      exact Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn
        (GaloisField.card 2 n (by omega))
    exact hr.trans hb
  let : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ _
  let σ : Representation (ZMod 2) _ W := (ρ.comp K.subtype).comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp K.subtype)).mpr hK.irreducible
  have hf : Function.Injective σ := h.faithful.comp (K.subtype_injective.comp e.symm.injective)
  have hv : v ∈ K := TensorCases.marked_mem_sl2_component h hK e
  let g := e ⟨v, hv⟩
  have hg : orderOf g = 2 := by
    rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
    exact h.involution
  have hgdim : Module.finrank (ZMod 2) (LinearMap.range (σ g - LinearMap.id)) = 2 := by
    change Module.finrank (ZMod 2) (displacement ρ (e.symm (e ⟨v, hv⟩))) = 2
    rw [e.symm_apply_apply]
    exact h.displacement_rank
  have hd := h.dimension
  rcases binary_small_faithful_classification σ hf n hn
    (GaloisField.card 2 n (by omega)) (by omega) with hnat | hherm | htriple
  · obtain ⟨f⟩ := hnat.2.2
    apply h.not_natural_rankOne K (F := GaloisField 2 n)
    refine ⟨e, f.toLinearEquiv, ?_⟩
    intro k w
    have he := congrArg (fun t => t w) (f.isIntertwining' (e k))
    change f.toLinearEquiv (σ (e k) w) =
      BinarySmall.natural (e k) (f.toLinearEquiv w) at he
    change f.toLinearEquiv (ρ (e.symm (e k) : H) w) = _ at he
    rw [e.symm_apply_apply] at he
    exact he
  · obtain ⟨hrn, hdim, hr, φ, ⟨f⟩⟩ := hherm
    let r := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,GaloisField 2 n)] σ.asModule)
    let : NeZero r := ⟨hr.ne'⟩
    have hr2 : 2 ≤ r := by have := h.positive; dsimp [r]; omega
    have hm_inj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) φ.toRingHom) := by
      intro a b hab
      apply Subtype.ext
      ext i j
      apply φ.injective
      exact congrArg (fun c : SL(2,OrthogonalFourMinus.FiniteModel.Field r) => c.val i j) hab
    have horder : orderOf (Matrix.SpecialLinearGroup.map φ.toRingHom g) = 2 :=
      (orderOf_injective _ hm_inj g).trans hg
    have ht := (RankTwo.Imprimitive.displacementRangeEquiv f.toLinearEquiv (σ g)
      ((BinarySmall.hermitian r).comp (Matrix.SpecialLinearGroup.map φ.toRingHom) g)
      (fun w => ((congrArg (fun t => t w) (f.isIntertwining' g))).symm)).finrank_eq
    change Module.finrank (ZMod 2) (LinearMap.range (σ g - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range
        (((BinarySmall.hermitian r).comp (Matrix.SpecialLinearGroup.map φ.toRingHom)) g -
          LinearMap.id)) at ht
    have hbound := BinarySmall.HermitianInvolution.rank_ge r
      (Matrix.SpecialLinearGroup.map φ.toRingHom g) horder
    change 2 * r ≤ Module.finrank (ZMod 2)
      (LinearMap.range (((BinarySmall.hermitian r).comp
        (Matrix.SpecialLinearGroup.map φ.toRingHom)) g - LinearMap.id)) at hbound
    have htwo : 2 * r ≤ 2 := hbound.trans_eq (ht.symm.trans hgdim)
    omega
  · have hn3 := htriple.2.1
    subst n
    apply TensorCases.not_tripleCase h hK
    exact ⟨e, htriple.2.2.2.1, htriple.2.2.1, by omega⟩

/-- Transport the literal Bender linear model to the canonical binary field. -/
theorem SourceData.not_binary_rankOne_model (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (n : ℕ) (hn : 2 ≤ n)
    (he : ClassicalGroup.IsPSL K 2 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let eF : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF,
      GaloisField.card 2 n (by omega)])
  exact h.not_binary_rankOne_component hK n hn
    ((e.trans (Atlas.fieldEquivPSL 2 eF)).trans
      (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n)).symm)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
variable {G : Type*} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass} {v : ActorQuotient Z} {s : ℕ}

/-- The binary rank-one branch is impossible for the original actor on U/Z. -/
theorem EarlierActionInputs.not_irreducible_binary_rankOne
    {d : EarlierSourceInputs Z ZS V M C v s} (a : EarlierActionInputs d)
    {K : Subgroup (ActorQuotient Z)}
    (hK : MinimalNormalConclusion C d.kernel K v s)
    (hi : Representation.IsIrreducible ((actorRepresentation Z ZS d.kernel).comp K.subtype))
    (n : ℕ) (hn : 2 ≤ n) (e : K ≃* SL(2,GaloisField 2 n)) : False :=
  a.sieveData.not_binary_rankOne_component (hK.componentData hi) n hn e

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
