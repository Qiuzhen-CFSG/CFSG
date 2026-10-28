module
public import Theory.Representation.G2NaturalNormalizerOffenders
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.PrimeResidual

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.G2Odd
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.OddField

/-!
# Odd-prime actors on the full original G₂ automizer

The actual binary normalizer is scalar times inner-field. A nontrivial field
part moves at least two thirds of the six-space. In the coefficient kernel,
prime order forces the scalar factor to have prime order too, unless it is one.
Such a scalar would make the prime divide q−1; the exact source 11.0.4 residual
then puts the original actor in the component image. The inner calculation
therefore applies in every case. Projection from the original module keeps
all central attachments and does not require a splitting or same-order lifts.

Source: Aschbacher--Smith 11.0.4 and 11.2.2(2), printed pp.760,768.
The Source endpoint consumes this bound in FixedCodimensions and the literal
prime-to-two residual centralizer statement.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Atlas.G2
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.G2Odd
attribute [local instance] ZMod.algebra
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private theorem scalar_factor_pow (hq : 2 < Nat.card F) {p : ℕ}
    (t : linearNormalizer (Natural.Normalizer.binary F)) (ht : t ^ p = 1)
    (z : Model F ⋊[LieAutomorphismExtensions.fieldAction] (F ≃+* F))
    (hz : LieAutomorphismExtensions.semilinearAction z = Natural.Normalizer.normalizerAutomorphism F t)
    (hσ : z.right = 1) :
    ∃ c : F, c ^ p = 1 ∧ ∀ v : Natural.Space F,
      t.val.val v = c • Natural.action F z.left v := by
  have hzpow : z ^ p = 1 := by
    apply LieAutomorphismExtensions.semilinearAction_injective hq
    rw [map_pow,hz,← map_pow,ht,map_one,map_one]
  have hz0 : z = SemidirectProduct.inl z.left := by
    apply SemidirectProduct.ext
    · rfl
    · exact hσ
  have hgp : z.left ^ p = 1 := by
    apply SemidirectProduct.inl_injective (φ := LieAutomorphismExtensions.fieldAction)
    rw [map_pow,← hz0,hzpow,map_one]
  obtain ⟨c,hc⟩ := Natural.Normalizer.normalizer_scalar_factor F t z.left z.right hz.symm
  have htv (v : Natural.Space F) : t.val.val v = c • Natural.action F z.left v := by
    have hf : Natural.BinarySemilinear.fieldEquivalence F z.right v = v := by
      rw [hσ]
      apply (Natural.BinarySemilinear.coordinatesEquiv F).injective
      exact (Natural.BinarySemilinear.coordinatesEquiv F).apply_symm_apply _
    simpa only [hf] using hc v
  have hpow (i : ℕ) (v : Natural.Space F) :
      (t ^ i).val.val v = c ^ i • Natural.action F (z.left ^ i) v := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ']
      change t.val.val ((t ^ i).val.val v) = _
      rw [htv,ih,map_smul,smul_smul,← Module.End.mul_apply,← map_mul]
      simp only [pow_succ']
  have hs (v : Natural.Space F) : c ^ p • v = v := by
    have hh := hpow p v
    rw [ht,hgp,map_one] at hh
    exact hh.symm
  have hcp : c ^ p = 1 := by
    have he := congrArg (fun v : Natural.Space F => Restricted.NaturalCoordinates.equiv F v 0)
      (hs ((Restricted.NaturalCoordinates.equiv F).symm (Pi.single 0 1)))
    simpa only [map_smul,LinearEquiv.apply_symm_apply,Pi.smul_apply,
      smul_eq_mul,Pi.single_eq_same,mul_one] using he
  exact ⟨c,hcp,htv⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.G2Odd


open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource Atlas.G2
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Every odd-prime actor in the actual original G₂ automizer moves at
least 4n dimensions. The source prime residual excludes scalar actors;
no splitting of the original central extension is used. -/
theorem g2_odd_prime_lower
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    letI := D.elementary
    ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V, orderOf a = p →
      4 * S.field.degree ≤ fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro p hp ho a ha
  let : Fact p.Prime := ⟨hp⟩
  let c := Coordinates.g2 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  let : Nontrivial c.Space := Module.nontrivial_of_finrank_pos
    (by change 0 < Module.finrank S.field.Carrier (Natural.Space S.field.Carrier)
        rw [Natural.finrank_space]; decide)
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let := layer_normal D S
  let : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra S.field.Carrier 2
  let : Nontrivial (Natural.Space S.field.Carrier) := Module.nontrivial_of_finrank_pos
    (by rw [Natural.finrank_space]; decide :
      0 < Module.finrank S.field.Carrier (Natural.Space S.field.Carrier))
  let f : c.Space →+ Natural.Space S.field.Carrier := {
    toFun := id
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  let E : c.Space ≃ₗ[ZMod 2] Natural.Space S.field.Carrier :=
    LinearEquiv.ofBijective (f.toZModLinearMap 2) Function.bijective_id
  let τ : Representation (ZMod 2) (Automizer V) (Natural.Space S.field.Carrier) :=
    E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (a : Automizer V) (v : c.Space) : E (ρ a v) = τ a (E v) := by
    change E (ρ a v) = E (ρ a (E.symm (E v)))
    rw [E.symm_apply_apply]
  let eL : inducedAutomizer V L ≃* Model S.field.Carrier := layerEquiv D S c
  have hres' (b : inducedAutomizer V L) (v : Natural.Space S.field.Carrier) :
      τ b v = Natural.action S.field.Carrier (eL b) v := by
    change E (ρ b (E.symm v)) = _
    rw [hres]
    change Natural.action S.field.Carrier (eL b) (E (E.symm v)) = _
    rw [E.apply_symm_apply]
  let ν := Natural.Normalizer.binary S.field.Carrier
  have hnat (b : inducedAutomizer V L) :
      τ.asGroupHom b = ν.asGroupHom (eL b) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change τ b v = ν (eL b) v
    exact (hres' b v).trans (LinearMap.congr_fun
      (Natural.Normalizer.binary_apply S.field.Carrier (eL b)) v).symm
  have himage : actionImage (τ.comp (inducedAutomizer V L).subtype) = actionImage ν := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨eL b,(hnat b).symm⟩
    · rintro ⟨g,rfl⟩
      refine ⟨eL.symm g,?_⟩
      exact (hnat (eL.symm g)).trans
        (congrArg ν.asGroupHom (eL.apply_symm_apply g))
  let k : Automizer V →* linearNormalizer ν := τ.asGroupHom.codRestrict _ (fun a => by
    change τ.asGroupHom a ∈ normalizer (actionImage ν : Set _)
    rw [← himage]
    exact actionImage_le_linearNormalizer τ (inducedAutomizer V L) ⟨a,rfl⟩)
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary
  let e := MulEquiv.ofBijective (LieAutomorphismExtensions.semilinearAction (F := S.field.Carrier))
    ⟨LieAutomorphismExtensions.semilinearAction_injective hq,
      LieAutomorphismExtensions.semilinearAction_surjective hq⟩
  let ψ := e.symm.toMonoidHom.comp ((Natural.Normalizer.normalizerAutomorphism S.field.Carrier).comp k)
  let π := SemidirectProduct.rightHom.comp ψ
  have hψ (a : Automizer V) : LieAutomorphismExtensions.semilinearAction (ψ a) =
      Natural.Normalizer.normalizerAutomorphism S.field.Carrier (k a) := e.apply_symm_apply _
  have hsemi : ∀ a (r : S.field.Carrier) v, τ a (r • v) = π a r • τ a v := by
    intro a r v
    obtain ⟨b,hb⟩ := Natural.Normalizer.normalizer_scalar_factor S.field.Carrier
      (k a) (ψ a).left (ψ a).right (hψ a).symm
    change (k a).val.val (r • v) = (ψ a).right r • (k a).val.val v
    rw [hb,hb,Natural.Normalizer.field_smul,map_smul,smul_comm]
  by_cases hs : π a = 1
  · have hka : k a ^ p = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one,map_one]
    obtain ⟨b,hbp,hb⟩ := G2Odd.scalar_factor_pow hq (k a) hka (ψ a) (hψ a) hs
    have haL : a ∈ inducedAutomizer V L := by
      by_cases hb1 : b = 1
      · have heq : a = eL.symm (ψ a).left := hρ (by
          apply LinearMap.ext
          intro v
          apply E.injective
          rw [hτ,hτ,hres',eL.apply_symm_apply]
          exact (hb (E v)).trans (by rw [hb1,one_smul]))
        rw [heq]
        exact (eL.symm (ψ a).left).property
      · have hb0 : b ≠ 0 := by
          intro hh
          rw [hh,zero_pow hp.pos.ne'] at hbp
          exact zero_ne_one hbp
        let u : S.field.Carrierˣ := Units.mk0 b hb0
        have hup : u ^ p = 1 := Units.ext (by change b ^ p = 1; exact hbp)
        have hu1 : u ≠ 1 := fun hh => hb1 (congrArg Units.val hh)
        have huo : orderOf u = p := orderOf_eq_prime hup hu1
        have hdvd : p ∣ 2 ^ S.field.degree - 1 := by
          simpa only [huo,Nat.card_units,S.field.card_eq] using orderOf_dvd_natCard u
        apply automizer_orderPrime_mem_layer D S hp _ ha
        refine Or.inl ⟨Or.inr ⟨m⟩,hdvd.trans ?_⟩
        simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2
    exact g2_inner_odd_prime_lower D S m p hp ho a ha haL
  · have hh := odd_field_lower τ hp ho a ha (π a) hs (hsemi a)
    rw [Natural.finrank_space,
      Representation.OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq] at hh
    have hlow : 4 * S.field.degree ≤ fixedCodim τ (zpowers a) := by omega
    exact hlow.trans (fixedCodim_le_of_equivariant_surjection
      (automizerRepresentation V) τ (E.toLinearMap.comp (projectionLinear D S c))
      (E.surjective.comp (projectionLinear_surjective D S c))
      (fun b v => (congrArg E (he b v)).trans (hτ b _)) (zpowers a))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
