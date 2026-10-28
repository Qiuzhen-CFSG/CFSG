module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearC28
public import Theory.Representation.IrreduciblePairBound
public import Theory.Representation.IrreducibleFixedPoints
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearRank
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearC28

/-!
# The original nonbinary linear-three pair on its reciprocal residual

The actual reciprocal cover L=LH O₂(L), together with centralization of the
whole source orbit by O₂(L), makes the original SL₃ actor surjective on LH.
Both original inequivalent simple summands survive this restriction. The
literal residual therefore has no fixed points on the complete orbit, and
the orbit cannot embed into repetitions of a space of dimension below six
times the field degree. The scalar center remains in the full SL₃ actor.

Source: Aschbacher--Smith C.4.8 and 7.3.4, printed pp.154,699, with the
original inequivalent pair of Table7.2.1, p.698, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem linear_three_dimension (F : BinaryField) :
    Module.finrank (ZMod 2) (Fin 3 → F.Carrier) = 3 * F.degree := by
  have hF : Module.finrank (ZMod 2) F.Carrier = F.degree := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod,F.card_eq] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
  simp [Module.finrank_pi_fintype,hF]

private theorem linear_pair_fixed_zero (F : BinaryField)
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (v : (Fin 3 → F.Carrier) × (Fin 3 → F.Carrier))
    (hv : ∀ g, ((linearNatural F 3).prod
      ((linearNatural F 3).comp a.toMonoidHom)) g v = v) : v = 0 := by
  let : IsIrreducible (linearNatural F 3) :=
    ExtensionConsequences.linearNatural_irreducible F (by decide)
  have hz := OneCohomology.fixed_eq_bot_of_irreducible_finrank
    (linearNatural F 3) (by rw [linear_three_dimension]; have := F.degree_pos; omega)
  have h₁ : v.1 ∈ OneCohomology.fixed (linearNatural F 3) :=
    fun g => congrArg Prod.fst (hv g)
  have h₂ : v.2 ∈ OneCohomology.fixed (linearNatural F 3) := by
    intro g
    have hh := congrArg Prod.snd (hv (a.symm g))
    change linearNatural F 3 (a (a.symm g)) v.2 = v.2 at hh
    simpa only [MulEquiv.apply_symm_apply] using hh
  rw [hz,Submodule.mem_bot] at h₁ h₂
  exact Prod.ext h₁ h₂

/-- The literal reciprocal residual retains the full original SL₃ actor and
both inequivalent simple summands on the unchanged doubled source orbit. -/
theorem sourceOrbit_linear_witness_pair_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier),
      ∃ q : LH →* Matrix.SpecialLinearGroup (Fin 3) F.Carrier,
        Function.Surjective q ∧
        (¬ Nonempty ((linearNatural F 3).Equiv
          ((linearNatural F 3).comp a.toMonoidHom))) ∧
        ∃ e : Additive D.sourceOrbit ≃ₗ[ZMod 2]
          ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)),
          ∀ l v, e (doubledSeedAction LH D.sourceOrbit
            (((map_subtype_le _).trans inf_le_left).trans
              D.sourceOrbit_component_normalizes) l v) =
            ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom))
              (q l) (e v) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  obtain ⟨a,q,hq,hne,e,he⟩ := D.original_twisted_coordinates h hd F hmodel
  have hQC := D.orbit_core_centralizes h
  have hk (b : G) (hb : b ∈ L.pCoreIn 2) : q ⟨b,pCoreIn_le 2 L hb⟩ = 1 := by
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := e.surjective (v,0)
    have hh := he ⟨b,pCoreIn_le 2 L hb⟩ w
    have hfix : doubledSeedAction L D.sourceOrbit
        D.sourceOrbit_component_normalizes ⟨b,pCoreIn_le 2 L hb⟩ w = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hQC hb w.toMul w.toMul.property).symm
    rw [hfix,hw] at hh
    have hfirst := congrArg Prod.fst hh
    change linearNatural F 3 (q ⟨b,pCoreIn_le 2 L hb⟩) v =
      linearNatural F 3 1 v
    simpa using hfirst.symm
  let p := q.comp (inclusion hLH)
  have hp : Function.Surjective p := by
    intro g
    obtain ⟨l,rfl⟩ := hq g
    obtain ⟨b,hb,c,hc,hbc⟩ := hw.2.2.2.2.2.2.2.1.subset l.property
    refine ⟨⟨b,hb⟩,?_⟩
    have hh : (⟨b,hLH hb⟩ : L) * ⟨c,pCoreIn_le 2 L hc⟩ = l := Subtype.ext hbc
    change q ⟨b,hLH hb⟩ = q l
    rw [←hh,map_mul,hk c hc,mul_one]
  exact ⟨a,p,hp,hne,e,fun l v => he (inclusion hLH l) v⟩

/-- The actual reciprocal residual fixes no nonidentity element of the whole
original linear-three doubled orbit. -/
theorem sourceOrbit_linear_witness_fixed_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    D.sourceOrbit ⊓ centralizer (LH : Set G) = ⊥ := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  obtain ⟨a,q,hq,_,e,he⟩ := D.sourceOrbit_linear_witness_pair_coordinates h hd F hmodel hw
  apply bot_unique
  intro x hx
  let v : Additive D.sourceOrbit := Additive.ofMul ⟨x,hx.1⟩
  have hv : e v = 0 := linear_pair_fixed_zero F a (e v) (by
    intro g
    obtain ⟨l,rfl⟩ := hq g
    rw [←he]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 l l.property))
  exact congrArg (fun z : Additive D.sourceOrbit => (z.toMul : G)) (e.map_eq_zero_iff.mp hv)

private theorem no_small_linear_pair
    (F : BinaryField) (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hne : ¬ Nonempty ((linearNatural F 3).Equiv
      ((linearNatural F 3).comp a.toMonoidHom)))
    {B Y ι : Type*} [Group B] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) Y]
    (p : B →* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) (hp : Function.Surjective p)
    (σ : Representation (ZMod 2) B Y)
    (τ : Representation (ZMod 2) B (ι → Y))
    (hτ : ∀ x v i, τ x v i = σ x (v i))
    (hd : Module.finrank (ZMod 2) Y < 6 * F.degree)
    (f : ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)) →ₗ[ZMod 2] (ι → Y))
    (hf : Function.Injective f)
    (he : ∀ x v, f (((linearNatural F 3).prod
      ((linearNatural F 3).comp a.toMonoidHom)) (p x) v) = τ x (f v)) : False := by
  let ρ : Representation (ZMod 2) B (Fin 3 → F.Carrier) := (linearNatural F 3).comp p
  let η : Representation (ZMod 2) B (Fin 3 → F.Carrier) :=
    (linearNatural F 3).comp (a.toMonoidHom.comp p)
  let : IsIrreducible (linearNatural F 3) :=
    ExtensionConsequences.linearNatural_irreducible F (by decide)
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff p hp _).mpr inferInstance
  let : IsIrreducible η :=
    (irreducible_comp_surjective_iff _ (a.surjective.comp hp) _).mpr inferInstance
  have hz (b : η.IntertwiningMap ρ) : b = 0 := by
    rcases IsIrreducible.bijective_or_eq_zero b with hb | hb
    · apply (hne ?_).elim
      let c := (b.ofBijective hb).symm
      refine ⟨Representation.Equiv.mk c.toLinearEquiv ?_⟩
      intro g
      apply LinearMap.ext
      intro v
      obtain ⟨x,rfl⟩ := hp g
      exact LinearMap.congr_fun (c.isIntertwining' x) v
    · exact hb
  let j : (ρ.prod η).IntertwiningMap τ := {
    toLinearMap := f
    isIntertwining' := by
      intro x
      apply LinearMap.ext
      intro v
      exact he x v }
  apply no_small_repeated_inequivalent_pair hz (σ := σ) _ τ hτ j hf
  rw [linear_three_dimension]
  omega

/-- Repetitions of a smaller module cannot contain the original pair for the
literal residual, even when the target restriction is not semisimple. -/
theorem sourceOrbit_linear_witness_no_small_repeated
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    {Y ι : Type*} [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y] :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∀ (σ : Representation (ZMod 2) LH Y) (τ : Representation (ZMod 2) LH (ι → Y)),
      (∀ x v i, τ x v i = σ x (v i)) → Module.finrank (ZMod 2) Y < 6 * F.degree →
      ∀ f : Additive D.sourceOrbit →ₗ[ZMod 2] (ι → Y), Function.Injective f →
        (∀ l v, f (doubledSeedAction LH D.sourceOrbit
          (((map_subtype_le _).trans inf_le_left).trans D.sourceOrbit_component_normalizes) l v) =
          τ l (f v)) → False := by
  intro LH σ τ hτ hdim f hf he
  obtain ⟨a,p,hp,hne,e,hepair⟩ := D.sourceOrbit_linear_witness_pair_coordinates h hd F hmodel hw
  apply no_small_linear_pair F a hne p hp σ τ hτ hdim (f.comp e.symm.toLinearMap)
    (hf.comp e.symm.injective)
  intro l v
  change f (e.symm (((linearNatural F 3).prod
    ((linearNatural F 3).comp a.toMonoidHom)) (p l) v)) = τ l (f (e.symm v))
  have hh := hepair l (e.symm v)
  rw [e.apply_symm_apply] at hh
  rw [←hh,e.symm_apply_apply]
  exact he l (e.symm v)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
