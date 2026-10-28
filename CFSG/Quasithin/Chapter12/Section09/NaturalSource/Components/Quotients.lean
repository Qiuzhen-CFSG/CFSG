module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Stages
public import CFSG.Quasithin.Chapter12.Section08.Setup.Completion
public import Theory.GroupTheory.SolvableResidual.PerfectFactor
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The literal flag residuals and their linear actions

The marked action maps N_L(Vᵢ) onto its two-block parabolic quotient.
At the end nodes O² preserves the perfect factor; at the two middle
nodes for n=5 the solvable residual removes the solvable GL₂(2) factor.
This identifies each original Lᵢ/O₂(Lᵢ) with GL₃(2) or GL₄(2), retaining
the exceptional residual convention. At i≥3, Lᵢ induces all automorphisms
of Vᵢ. Membership applies these facts to construct the local components.

Source: Aschbacher--Smith, Notation 12.8.2 and the first paragraph of
12.9.3, printed pp.849 and858 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 V]

private instance (d : ℕ) : Finite (LinearGroup d) :=
  Finite.of_injective (fun g : LinearGroup d => (g : Space d → Space d)) DFunLike.coe_injective

theorem flag_space_finrank (F : InvariantFlag T V n) (i : ℕ) (hi : i ≤ n) :
    Module.finrank (ZMod 2) (space (V := V) (F.Vi i)) = i := by
  have hc : Nat.card (space (V := V) (F.Vi i)) = Nat.card (F.Vi i) := by
    let e : space (V := V) (F.Vi i) ≃ F.Vi i :=
      { toFun x := ⟨x.val.toMul,x.property⟩
        invFun x := ⟨Additive.ofMul ⟨x,F.le_seed i x.property⟩,x.property⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    exact Nat.card_congr e
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, F.card i hi] at hc
  exact Nat.pow_right_injective (by decide) hc

/-- The two-block quotient of the actual relative normalizer N_L(Vᵢ). -/
theorem exists_flag_block_action (F : InvariantFlag T V n)
    {hLV : L ≤ normalizer (V : Set G)} (A : AmbientNaturalMarking L hLV n)
    (i : ℕ) (hi : i ≤ n) :
    ∃ f : (L ⊓ F.Gi i : Subgroup G) →* LinearGroup i × LinearGroup (n-i),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let W := space (V := V) (F.Vi i)
  let d := A.geometryAction
  let f₀ := d.action.comp (inclusion (show L ⊓ F.Gi i ≤ L from inf_le_left))
  let f₁ : (L ⊓ F.Gi i : Subgroup G) →* BinaryLinear.parabolic W :=
    f₀.codRestrict _ (fun x =>
      (action_mem_parabolic_iff d _ (F.le_seed i) (inclusion inf_le_left x)).mpr ((inf_le_right : L ⊓ F.Gi i ≤ F.Gi i) x.property))
  have hf₁ : Function.Surjective f₁ := by
    intro g
    obtain ⟨l,hl⟩ := d.surjective g.val
    refine ⟨⟨l,l.property,?_⟩,Subtype.ext hl⟩
    exact (action_mem_parabolic_iff d _ (F.le_seed i) l).mp (hl ▸ g.property)
  have hk₁ : IsPGroup 2 f₁.ker := by
    change IsPGroup 2 (f₀.codRestrict _ _).ker
    rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker, d.kernel]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hW : Module.finrank (ZMod 2) W = i := flag_space_finrank F i hi
  have hQ : Module.finrank (ZMod 2) (Additive V ⧸ W) = n-i := by
    have he := W.finrank_quotient_add_finrank
    have hv := A.coordinates.finrank_eq
    simp only [Module.finrank_fin_fun] at hv
    omega
  let a := (Module.finBasisOfFinrankEq (ZMod 2) W hW).equivFun
  let b := (Module.finBasisOfFinrankEq (ZMod 2) (Additive V ⧸ W) hQ).equivFun
  let e := quotientTwoCoreEquivOfCoordinates W a b
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 (BinaryLinear.parabolic W))).comp f₁)
  refine ⟨f,e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hf₁),?_⟩
  dsimp only [f]
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker,
    QuotientGroup.ker_mk']
  exact pCore_isPGroup.comap_of_ker_isPGroup f₁ hk₁

private theorem perfect_pResidual {Y : Type*} [Group Y] [Finite Y]
    [Group.IsPerfect Y] : pResidual 2 Y = ⊤ := by
  apply (pResidual_eq_top_iff 2 Y).mpr
  intro N hn hp
  let := hn
  by_contra hne
  let : Nontrivial (Y ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isNilpotent (Y ⧸ N) hp.isNilpotent

private theorem exists_pResidual_action {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] [Group.IsPerfect Y]
    (f : X →* Y) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    ∃ g : pResidual 2 X →* Y, Function.Surjective g ∧ IsPGroup 2 g.ker := by
  let g := f.comp (pResidual 2 X).subtype
  have hm : (pResidual 2 X).map f = ⊤ := by
    rw [map_pResidual_of_surjective 2 f hf, perfect_pResidual]
  refine ⟨g,?_,?_⟩
  · intro y
    obtain ⟨x,hx,he⟩ := mem_map.mp (hm.symm ▸ mem_top y)
    exact ⟨⟨x,hx⟩,he⟩
  · rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective _ Subtype.val_injective

/-- Indices of the local components in the source statement of 12.9.3. -/
def ComponentIndex (n i : ℕ) : Prop :=
  (n = 5 ∧ 1 ≤ i ∧ i < 5) ∨ (n = 4 ∧ (i = 1 ∨ i = 3))

private instance linear_one_unique : Unique (LinearGroup 1) :=
  { default := 1
    uniq := fun _ => (slEquivLinear 1).symm.injective (Subsingleton.elim _ _) }

private theorem linear_two_solvable : Group.IsSolvable (LinearGroup 2) := by
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  exact Group.isSolvable_of_isSolvable_injective
    (f := linearTwoEquivSymmetricThree.toMonoidHom) linearTwoEquivSymmetricThree.injective

/-- The literal Lᵢ has a binary linear quotient by a two-group kernel.
The middle two nodes use the solvable residual, exactly as in Notation 12.8.2. -/
theorem exists_Li_linear_action (F : InvariantFlag T V n)
    {hLV : L ≤ normalizer (V : Set G)} (A : AmbientNaturalMarking L hLV n)
    (i : ℕ) (hi : ComponentIndex n i) :
    ∃ d : ℕ, d = max i (n-i) ∧ (d = 3 ∨ d = 4) ∧
      ∃ f : F.Li L i →* LinearGroup d, Function.Surjective f ∧ IsPGroup 2 f.ker := by
  have hin : i ≤ n := by rcases hi with ⟨rfl,_,_⟩ | ⟨rfl,h⟩ <;> omega
  obtain ⟨f,hf,hk⟩ := exists_flag_block_action F A i hin
  by_cases hm : n = 5 ∧ (i = 2 ∨ i = 3)
  · have hd : n = 5 := hm.1
    subst n
    let : Group.IsSolvable (LinearGroup 2) := linear_two_solvable
    let : Group.IsPerfect (LinearGroup 3) := BinaryLinear.linearGroup_isPerfect 3 (by decide)
    let e : F.Li L i ≃* solvableResidual (L ⊓ F.Gi i : Subgroup G) := by
      rw [Li, if_pos hm]
      exact ((solvableResidual (L ⊓ F.Gi i : Subgroup G)).equivMapOfInjective _
        (L ⊓ F.Gi i).subtype_injective).symm
    rcases hm.2 with rfl | rfl
    · let g := f.solvableResidualPerfectFactor.comp e.toMonoidHom
      refine ⟨3,by decide,Or.inl rfl,g,?_,?_⟩
      · exact (f.solvableResidualPerfectFactor_surjective hf).comp e.surjective
      · rw [← MonoidHom.comap_ker]
        exact (f.solvableResidualPerfectFactor_ker_isPGroup hk).comap_of_injective _ e.injective
    · let f' := (MulEquiv.prodComm (M := LinearGroup 3) (N := LinearGroup 2)).toMonoidHom.comp f
      have hf' : Function.Surjective f' := (MulEquiv.prodComm (M := LinearGroup 3) (N := LinearGroup 2)).surjective.comp hf
      have hk' : IsPGroup 2 f'.ker := by
        rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.prodComm (M := LinearGroup 3) (N := LinearGroup 2)).injective]
        exact hk
      let g := f'.solvableResidualPerfectFactor.comp e.toMonoidHom
      refine ⟨3,by decide,Or.inl rfl,g,?_,?_⟩
      · exact (f'.solvableResidualPerfectFactor_surjective hf').comp e.surjective
      · rw [← MonoidHom.comap_ker]
        exact (f'.solvableResidualPerfectFactor_ker_isPGroup hk').comap_of_injective _ e.injective
  · have hedge : i = 1 ∨ i = n-1 := by
      rcases hi with ⟨hn,hlo,hhi⟩ | ⟨hn,he⟩ <;> omega
    have hd : n-1 = 3 ∨ n-1 = 4 := by rcases hi with ⟨hn,_,_⟩ | ⟨hn,_⟩ <;> omega
    let : Group.IsPerfect (LinearGroup (n-1)) := BinaryLinear.linearGroup_isPerfect _ (by omega)
    have hf' : ∃ f' : (L ⊓ F.Gi i : Subgroup G) →* LinearGroup (n-1),
        Function.Surjective f' ∧ IsPGroup 2 f'.ker := by
      rcases hedge with hi | hi
      · subst i
        let e' : LinearGroup 1 × LinearGroup (n-1) ≃* LinearGroup (n-1) := MulEquiv.uniqueProd
        exact ⟨e'.toMonoidHom.comp f,e'.surjective.comp hf,by
          rw [MonoidHom.ker_comp_of_injective _ _ e'.injective]; exact hk⟩
      · have hn : n-i = 1 := by omega
        let e' : LinearGroup i × LinearGroup (n-i) ≃* LinearGroup (n-1) := by
          rw [hn,hi]
          exact MulEquiv.prodUnique
        exact ⟨e'.toMonoidHom.comp f,e'.surjective.comp hf,by
          rw [MonoidHom.ker_comp_of_injective _ _ e'.injective]; exact hk⟩
    obtain ⟨f',hf',hk'⟩ := hf'
    obtain ⟨g,hg,hkg⟩ := exists_pResidual_action f' hf' hk'
    let e : F.Li L i ≃* pResidual 2 (L ⊓ F.Gi i : Subgroup G) := by
      rw [Li,if_neg hm]
      exact ((pResidual 2 (L ⊓ F.Gi i : Subgroup G)).equivMapOfInjective _
        (L ⊓ F.Gi i).subtype_injective).symm
    refine ⟨n-1,by rcases hedge with he | he <;> omega,hd,g.comp e.toMonoidHom,hg.comp e.surjective,?_⟩
    rw [← MonoidHom.comap_ker]
    exact hkg.comap_of_injective _ e.injective

/-- The intrinsic two-core quotients of all source residuals are the actual
GL₃(2) or GL₄(2) carriers. -/
theorem Li_core_linear (F : InvariantFlag T V n)
    {hLV : L ≤ normalizer (V : Set G)} (A : AmbientNaturalMarking L hLV n)
    (i : ℕ) (hi : ComponentIndex n i) :
    ∃ d : ℕ, d = max i (n-i) ∧ (d = 3 ∨ d = 4) ∧
      Nonempty ((F.Li L i ⧸ pCore 2 (F.Li L i)) ≃* LinearGroup d) := by
  obtain ⟨d,hdi,hd,f,hf,hk⟩ := exists_Li_linear_action F A i hi
  exact ⟨d,hdi,hd,⟨(f.pCoreQuotientEquiv hf hk).trans
    ((QuotientGroup.quotientMulEquivOfEq linearGroup_twoCore_eq_bot).trans
      QuotientGroup.quotientBot)⟩⟩

/-- Quasisimplicity needed for the actual local-family membership. -/
theorem Li_core_quasisimple (F : InvariantFlag T V n)
    {hLV : L ≤ normalizer (V : Set G)} (A : AmbientNaturalMarking L hLV n)
    (i : ℕ) (hi : ComponentIndex n i) :
    IsQuasisimple (F.Li L i ⧸ pCore 2 (F.Li L i)) := by
  obtain ⟨d,_,hd,⟨e⟩⟩ := Li_core_linear F A i hi
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := {
    toIsPerfect := Atlas.sl_perfect _ (by omega)
    simple := Atlas.psl_simple_high_rank _ (by omega) }
  exact IsQuasisimple.of_mulEquiv (((slEquivLinear d).trans e.symm))

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 V]

noncomputable def flagLinearAction (F : InvariantFlag T V n) (i : ℕ) :
    F.Gi i →* BinaryLinear.GL (space (V := V) (F.Vi i)) where
  toFun g := normalizerLinear (F.Vi i) (F.le_seed i) g
  map_one' := by
    ext v
    change (1 : G) * (v.val.toMul : G) * (1 : G)⁻¹ = (v.val.toMul : G)
    simp only [one_mul,inv_one,mul_one]
  map_mul' a b := by
    ext v
    change ((a : G) * (b : G)) * (v.val.toMul : G) * ((a : G) * (b : G))⁻¹ =
      (a : G) * ((b : G) * (v.val.toMul : G) * (b : G)⁻¹) * (a : G)⁻¹
    simp only [mul_inv_rev,mul_assoc]

omit [Finite G] in
private theorem flagLinearAction_surjective (F : InvariantFlag T V n)
    {hLV : L ≤ normalizer (V : Set G)} (A : AmbientNaturalMarking L hLV n) (i : ℕ) :
    Function.Surjective ((flagLinearAction F i).comp
      (inclusion (show L ⊓ F.Gi i ≤ F.Gi i from inf_le_right))) := by
  intro a
  obtain ⟨l,hl,he⟩ := normalizer_full_action A.geometryAction (F.Vi i) (F.le_seed i) a
  refine ⟨⟨l,l.property,hl⟩,?_⟩
  ext v
  exact (A.geometryAction.conjugation l v.val).symm.trans
    (congrArg (fun w : Additive V => (w.toMul : G)) (he v))

/-- At indices at least three the literal residual induces the full linear
 action on the flag space, for either source residual convention. -/
theorem Li_flagLinearAction_surjective (F : InvariantFlag T V n)
    {hLV : L ≤ normalizer (V : Set G)} (A : AmbientNaturalMarking L hLV n)
    (i : ℕ) (hi : 3 ≤ i) (hin : i ≤ n) :
    Function.Surjective ((flagLinearAction F i).comp
      (inclusion ((F.Li_le L i).trans inf_le_right))) := by
  let Y := BinaryLinear.GL (space (V := V) (F.Vi i))
  let e := (Module.finBasisOfFinrankEq (ZMod 2) _ (flag_space_finrank F i hin)).equivFun
  let eG : Y ≃* LinearGroup i := BinaryLinear.SmallParabolicLevi.linearGroupCongr e
  let : Finite Y := Finite.of_injective eG eG.injective
  let : Group.IsPerfect (LinearGroup i) := BinaryLinear.linearGroup_isPerfect i hi
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective (f := eG.symm.toMonoidHom) eG.symm.surjective
  let f := (flagLinearAction F i).comp
    (inclusion (show L ⊓ F.Gi i ≤ F.Gi i from inf_le_right))
  have hf : Function.Surjective f := flagLinearAction_surjective F A i
  intro a
  by_cases hm : n = 5 ∧ (i = 2 ∨ i = 3)
  · have he : (solvableResidual (L ⊓ F.Gi i : Subgroup G)).map f = ⊤ := by
      rw [map_solvableResidual_eq f hf, solvableResidual_eq_top]
    obtain ⟨x,hx,he⟩ := mem_map.mp (he.symm ▸ mem_top a)
    refine ⟨⟨x,?_⟩,he⟩
    rw [Li,if_pos hm]
    exact mem_map_of_mem (L ⊓ F.Gi i).subtype hx
  · have he : (pResidual 2 (L ⊓ F.Gi i : Subgroup G)).map f = ⊤ := by
      rw [map_pResidual_of_surjective 2 f hf, perfect_pResidual]
    obtain ⟨x,hx,he⟩ := mem_map.mp (he.symm ▸ mem_top a)
    refine ⟨⟨x,?_⟩,he⟩
    rw [Li,if_neg hm]
    exact mem_map_of_mem (L ⊓ F.Gi i).subtype hx

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
