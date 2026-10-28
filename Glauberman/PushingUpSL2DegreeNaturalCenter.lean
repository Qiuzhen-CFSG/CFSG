module
public import Glauberman.PushingUpSL2DegreeCovering
public import Theory.Representation.SL2.SharpNaturalQuotient

/-!
# The original-degree Niles natural core center

The sharp fixed indices of the actual conjugate Sylows recognize the
literal central quotient of Ω₁Z(O₂(G)) as one natural module over the
original field. The intersection diagram identifies Ω₁Z(O₂(G)) with
Z(O₂(G)); its entire ambient-fixed subspace remains the quotient kernel.
The coordinates intertwine the original SL₂ marking, without a field
restriction or an unspecified action twist.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 2.9 and
Proposition 5.5, pp.33,51--52. The upper noncentral factor and subsequent
structure/commutator conclusion remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Coordinates on the literal full-fixed quotient of the original core center. -/
@[expose] def NilesCenterCoordinates
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) : Prop :=
  omegaCenterIn (pCore 2 G) = centerIn (pCore 2 G) ∧
    ∃ E : (Additive (omegaCenterIn (pCore 2 G)) ⧸ fixedSpace (omegaAction G) ⊤)
        ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (fixedQuotient (omegaAction G) ⊤ g v) =
        Matrix.mulVec (e (QuotientGroup.mk' (pCore 2 G) g)).val (E v)

/-- The exact original SL₂ action on the full core-center quotient is natural. -/
theorem original_sl2_natural_center
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesCenterCoordinates e := by
  obtain ⟨x,hx,hgen,hinter,hnum⟩ := original_sl2_numerical_pair e hn hF S α hfit hno
  let T := S.mapSurjective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).surjective
  let V := omegaCenterIn (pCore 2 G)
  let _ : V.Normal := omegaCenterIn_normal_of_normal _
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hc : f.ker = centralizer (V : Set G) := hk.trans
    (sl2_core_omega_centralizer e hn hF S hfit hno.noCharacteristicNormal).symm
  let ρ := NormalElementaryQuotient.representation V f hf hc
  let R := S.mapSurjective hf
  let T' := T.mapSurjective hf
  have hgen' : (R : Subgroup SL(2,F)) ⊔ T' = ⊤ := by
    change (S : Subgroup G).map f ⊔ (T : Subgroup G).map f = ⊤
    have hg : (S : Subgroup G) ⊔ (T : Subgroup G) = ⊤ := hgen
    rw [←Subgroup.map_sup,hg,map_top_of_surjective f hf]
  obtain ⟨hiS,hiT⟩ := hnum.omega_fixed_indices
  rw [hinter,inf_relIndex_left] at hiS hiT
  have hdim (A : Subgroup G) (hi : (centralizer (A : Set G)).relIndex V = Nat.card F) :
      fixedCodim ρ (A.map f) = n := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim V f hf hc,hF] at hi
    exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hi
  have hR : fixedCodim ρ R = n := hdim S hiS
  have hT : fixedCodim ρ T' = n := hdim T hiT
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra! he
    have hfixed : fixedSpace ρ R = ⊤ := by
      apply top_unique
      intro v _ r
      change ρ (r : Matrix.SpecialLinearGroup (Fin 2) F) v = v
      rw [he]
      rfl
    have hz : fixedCodim ρ R = 0 := by
      have hh := fixedCodim_add_finrank ρ (R : Subgroup _)
      rw [hfixed,finrank_top] at hh
      omega
    omega
  have hρ : ρ.comp f = omegaAction G := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply V f hf hc g v).trans
      (omegaAction_apply G g v).symm
  have hfixed : fixedSpace (omegaAction G) ⊤ = fixedSpace ρ ⊤ := by
    rw [←hρ,fixedSpace_comp_map,map_top_of_surjective f hf]
  obtain ⟨E₀,hE₀⟩ := Representation.SL2.sharp_sylow_natural_quotient
    ρ hnt hn hF R T' hgen' hR hT
  have hω := hnum.omegaCenters_eq_centers.2.2
  rw [hinter] at hω
  refine ⟨hω,(Submodule.quotEquivOfEq _ _ hfixed).trans E₀,?_⟩
  intro g v
  obtain ⟨w,rfl⟩ := (fixedSpace (omegaAction G) ⊤).mkQ_surjective v
  change E₀ ((fixedSpace ρ ⊤).mkQ (omegaAction G g w)) =
    Matrix.mulVec (f g).val (E₀ ((fixedSpace ρ ⊤).mkQ w))
  have hact : omegaAction G g w = ρ (f g) w := by rw [←hρ]; rfl
  rw [hact]
  exact hE₀ (f g) ((fixedSpace ρ ⊤).mkQ w)

end Glauberman
