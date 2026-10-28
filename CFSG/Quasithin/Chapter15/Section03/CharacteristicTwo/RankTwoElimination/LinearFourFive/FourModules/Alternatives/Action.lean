module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.ModuleCases
public import Theory.ThreeSubgroups
public import Mathlib.RepresentationTheory.Coinvariants
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The actual commutator representation in the L₄ branch

Conjugation on `U_L = [W_L,L]` descends through the literal two-core
quotient. Elementarity passes from `W_L` to `U_L`. The earlier equality
`L = [L,Y₊]` and `Y₊ ≤ L` make `L` perfect, and the three-subgroups
lemma proves `[U_L,L] = U_L`. Identifying linear differences with ambient
commutators then gives the full coinvariant kernel required by B.5.1.
The actual PSL₄(2) isomorphism and nontriviality of `U_L` make this
representation faithful. No module recognition is used in these arguments.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.24,
printed p.1129, and the hypotheses of B.5.1, printed p.99.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives

variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)

/-- The earlier full Y₊-commutator makes the contained component perfect. -/
theorem component_perfect {I : Subgroup G} (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L) : Group.IsPerfect c.L := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm ((Subgroup.commutator_le_sup c.L c.L).trans (sup_idem _).le)
  exact c.commutator_eq.le.trans (commutator_mono le_rfl hYL)

/-- An outside component cannot centralize its conjugate span. -/
theorem commutator_ne_bot {I : Subgroup G} (c : ComponentWitness d I)
    (hC : centralizer (d.V : Set G) ≤ d.M) : spanCommutator d c.L ≠ ⊥ := by
  intro h
  exact c.outside ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)).trans
    ((centralizer_le (le_conjugateSpanBy d.V c.L)).trans hC))

/-- Elementarity of the source span gives a binary commutator module. -/
theorem commutator_elementary [IsElementaryAbelian 2 (d.componentSpan L)] :
    IsElementaryAbelian 2 (spanCommutator d L) := by
  have h := spanCommutator_le_span d L
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact le_centralizer_iff_isMulCommutative.mp
      (h.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le h)))
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro u
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) (h u.property)

variable [IsElementaryAbelian 2 (spanCommutator d L)]
  (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))

/-- The action is on the whole original `U_L` and factors through `L/O₂(L)`. -/
noncomputable def coreRepresentation :
    Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (spanCommutator d L)) where
  toFun g := (commutatorQuotientAction d L hcore hR g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul (commutatorQuotientAction d L hcore hR 1 u.toMul) = u
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul (commutatorQuotientAction d L hcore hR (g * h) u.toMul) = _
    rw [map_mul]
    rfl

/-- The quotient action retains the ambient conjugation convention. -/
theorem coreRepresentation_apply (l : L) (u : Additive (spanCommutator d L)) :
    ((coreRepresentation d L hcore hR (QuotientGroup.mk' _ l) u).toMul : G) =
      (l : G) * u.toMul * (l : G)⁻¹ := rfl

/-- On a representative, the binary action is precisely the original group action. -/
theorem coreRepresentation_mk (l : L) (u : spanCommutator d L) :
    coreRepresentation d L hcore hR (QuotientGroup.mk' _ l) (Additive.ofMul u) =
      Additive.ofMul (commutatorAction d L l u) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact coreRepresentation_apply d L hcore hR l (Additive.ofMul u)

omit [IsElementaryAbelian 2 (spanCommutator d L)] in
/-- Perfectness and the three-subgroups lemma give `[U_L,L] = U_L`. -/
theorem commutator_full [IsElementaryAbelian 2 (d.componentSpan L)] [Group.IsPerfect L] :
    ⁅spanCommutator d L, L⁆ = spanCommutator d L := by
  apply le_antisymm
    (le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right _ _))
  have h : ⁅⁅L, L⁆, d.componentSpan L⁆ ≤ ⁅spanCommutator d L, L⁆ :=
    commutator_commutator_le_of_rotate_of_le_normalizer
      (normalizer_commutator_ge_right _ _) (normalizer_commutator_ge_right _ _)
      (((le_centralizer_iff_isMulCommutative.mpr inferInstance :
        d.componentSpan L ≤ centralizer (d.componentSpan L : Set G)).trans
        (centralizer_le ((le_normalizer_iff_commutator_le_left.mp
          (normalizer_commutator_ge_right _ _)).trans (spanCommutator_le_span d L)))).trans
        (Subgroup.centralizer_le_normalizer _))
      (by rw [commutator_comm L (d.componentSpan L)]) le_rfl
  simpa only [L.commutator_eq_self, commutator_comm L (d.componentSpan L)] using h

/-- The `U` in B.5.1 is the entire module supplied to the classifier. -/
theorem coreRepresentation_full [IsElementaryAbelian 2 (d.componentSpan L)] [Group.IsPerfect L] :
    Representation.Coinvariants.ker
      ((coreRepresentation d L hcore hR).comp (⊤ : Subgroup (L ⧸ pCore 2 L)).subtype) = ⊤ := by
  let ρ := coreRepresentation d L hcore hR
  let C := Representation.Coinvariants.ker
    (ρ.comp (⊤ : Subgroup (L ⧸ pCore 2 L)).subtype)
  let D : Subgroup G := C.toAddSubgroup.toSubgroup'.map (spanCommutator d L).subtype
  have hUD : spanCommutator d L ≤ D := by
    rw [← commutator_full d L, commutator_comm]
    apply commutator_le.mpr
    intro l hl u hu
    let v : Additive (spanCommutator d L) := Additive.ofMul ⟨u, hu⟩
    have hv : ρ (QuotientGroup.mk' _ ⟨l, hl⟩) v - v ∈ C :=
      Representation.Coinvariants.sub_mem_ker
        (ρ := ρ.comp (⊤ : Subgroup (L ⧸ pCore 2 L)).subtype)
        ⟨QuotientGroup.mk' _ ⟨l, hl⟩, mem_top _⟩ v
    have hm := mem_map_of_mem (spanCommutator d L).subtype
      (show (ρ (QuotientGroup.mk' _ ⟨l, hl⟩) v - v).toMul ∈
        C.toAddSubgroup.toSubgroup' from hv)
    change (((ρ (QuotientGroup.mk' _ ⟨l, hl⟩) v - v).toMul : spanCommutator d L) : G) ∈ D at hm
    simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hm
    rw [coreRepresentation_apply] at hm
    exact hm
  apply top_unique
  intro v _
  obtain ⟨w, hw, he⟩ := hUD v.toMul.property
  have he' : Additive.ofMul w = v := by
    apply Additive.toMul.injective
    exact Subtype.ext he
  exact he' ▸ hw

/-- Simplicity of the actual quotient eliminates the action kernel. -/
theorem coreRepresentation_faithful [IsElementaryAbelian 2 (d.componentSpan L)]
    [Group.IsPerfect L] (model : (L ⧸ pCore 2 L) ≃* Projective 4)
    (hne : spanCommutator d L ≠ ⊥) :
    Function.Injective (coreRepresentation d L hcore hR) := by
  let _ : IsSimpleGroup (Projective 4) := Atlas.psl_simple_high_rank 4 (by decide)
  let _ : IsSimpleGroup (L ⧸ pCore 2 L) := model.isSimpleGroup
  let a := commutatorQuotientAction d L hcore hR
  have hk : a.ker = ⊥ := (inferInstance : a.ker.Normal).eq_bot_or_eq_top.resolve_right (by
    intro htop
    have hb : ⁅spanCommutator d L, L⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro u hu l hl
      have ha : a (QuotientGroup.mk' _ ⟨l, hl⟩) = 1 := by
        change QuotientGroup.mk' _ ⟨l, hl⟩ ∈ a.ker
        rw [htop]
        trivial
      have he := congrArg (fun f : MulAut (spanCommutator d L) => (f ⟨u, hu⟩ : G)) ha
      change l * u * l⁻¹ = u at he
      exact mul_inv_eq_iff_eq_mul.mp he
    exact hne ((commutator_full d L).symm.trans hb))
  have hi : Function.Injective a := (MonoidHom.ker_eq_bot_iff a).mp hk
  intro x y hxy
  apply hi
  apply MulEquiv.ext
  intro u
  exact congrArg (fun f : Module.End (ZMod 2) (Additive (spanCommutator d L)) =>
    (f (Additive.ofMul u)).toMul) hxy

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives
end
