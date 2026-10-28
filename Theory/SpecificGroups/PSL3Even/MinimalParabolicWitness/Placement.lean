module

public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.Extension
public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.CentralActor
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The original elementary subgroup lies in the long root

For a faithful normal PSL₃ section in H=KT, unique maximality supplies a
swapping actor. The original elementary subgroup's intersection with K lies
in the highest-root center. Normality under T then makes every element of V
act centrally on UT₃. The explicit actor calculation makes it inner, and
faithfulness places V in K. Applying the plane argument once more places the
whole original V in the long-root group.

Source: Aschbacher--Smith, E.2.7, printed p.219.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Even.MinimalParabolicWitness
variable {H : Type*} [Group H] [Finite H]
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (K : Subgroup H) [K.Normal] (e : K ≃* PSL(3,F))
variable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)

include hn hF in
/-- Faithfulness and unique maximality place the supplied normal elementary
subgroup in the original marked highest-root group. -/
theorem elementary_le_longRoot (T M V : Subgroup H)
    (hgen : K ⊔ T = ⊤) (hU : T.comap (modelEmbedding F K e) = unipotent F)
    (hunique : Order.HasUniqueMaximalOver T ⊤) (hM : T ≤ M ∧ IsCoatom M)
    (hc : centralizer (K : Set H) = ⊥)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T) (hVN : T ≤ normalizer (V : Set H)) :
    V ≤ (projectiveCenter F).map (modelEmbedding F K e) := by
  let f := modelEmbedding F K e
  have hf : Function.Injective f := modelEmbedding_injective F K e
  let A := V.comap f
  let r : A →* V :=
    { toFun := fun x => ⟨f x.val, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val) }
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective r
    (by intro x y h; apply Subtype.ext; apply hf; exact congrArg (fun z : V => (z : H)) h)
  have hAU : A ≤ unipotent F := by rw [← hU]; exact comap_mono hVT
  have hpres (t : H) (ht : t ∈ T) :
      (unipotent F).map (modelAction F K e t).toMonoidHom = unipotent F := by
    apply Subgroup.map_injective hf
    rw [map_modelAction, ← hU, map_comap_eq, modelEmbedding_range]
    exact mem_normalizer_iff_map_conj_eq.mp
      (inf_normalizer_le_normalizer_inf ⟨by rw [normalizer_eq_top]; trivial, T.le_normalizer ht⟩)
  have hinv (t : H) (ht : t ∈ T) : A.map (modelAction F K e t).toMonoidHom = A := by
    apply Subgroup.map_injective hf
    rw [map_modelAction, map_comap_eq, modelEmbedding_range]
    exact mem_normalizer_iff_map_conj_eq.mp
      (inf_normalizer_le_normalizer_inf ⟨by rw [normalizer_eq_top]; trivial, hVN ht⟩)
  obtain ⟨⟨t,ht,hs⟩,_⟩ := diagram_and_borel F K e hn hF T M hgen hU hunique hM
  have hAZ : A ≤ projectiveCenter F :=
    elementary_invariant_le_center F hn hF _ (hpres t ht) hs A hAU (hinv t ht)
  have hactinj : Function.Injective (modelAction F K e) :=
    (MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot K hc)
  have hVK : V ≤ K := by
    intro v hv
    have hd (u : PSL(3,F)) (hu : u ∈ unipotent F) :
        modelAction F K e v u * u⁻¹ ∈ projectiveCenter F := by
      apply hAZ
      change f (modelAction F K e v u * u⁻¹) ∈ V
      rw [map_mul, map_inv, modelEmbedding_action]
      change v * f u * v⁻¹ * (f u)⁻¹ ∈ V
      have huT : f u ∈ T := by change u ∈ T.comap f; rwa [hU]
      have hvconj := (mem_normalizer_iff.mp (hVN huT) v⁻¹).mp (V.inv_mem hv)
      simpa only [mul_assoc] using V.mul_mem hv hvconj
    have hp : modelAction F K e v ^ 2 = 1 := by
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian v hv, map_one]
    obtain ⟨z,hz⟩ := inner_of_central_displacement F hn hF _ (hpres v (hVT hv)) hp hd
    have he : modelAction F K e (f z) = MulAut.conj z := by
      ext x
      apply hf
      rw [modelEmbedding_action]
      simp only [MulAut.conj_apply, map_mul, map_inv]
      rfl
    have hev : f z = v := hactinj (he.trans hz)
    rw [← hev]
    exact (e.symm z).property
  intro v hv
  obtain ⟨z,hz⟩ : ∃ z, f z = v := by
    rw [← modelEmbedding_range F K e] at hVK
    exact hVK hv
  refine ⟨z,hAZ ?_,hz⟩
  change f z ∈ V
  rwa [hz]

end Matrix.PSL3Even.MinimalParabolicWitness
