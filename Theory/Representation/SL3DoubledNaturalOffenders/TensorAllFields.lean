module
public import Theory.Representation.SL3DoubledNaturalOffenders
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Intrinsic

/-!
# Doubled-natural tensor offenders in every binary field degree

The tensor kernel consists of reciprocal scalars. Its SL₂ determinant forces
that scalar to be one in characteristic two, retaining the cubic SL₃ center
in even degree. The full SL₃ two-rank gives the same projection bound as in
odd degree. The common fixed-space argument then excludes every nontrivial
multiplicity projection from an offender.

This extends TensorEstimate without changing its public odd-degree API.
The normalizer application is in AllFields. Source: Aschbacher--Smith
B.5.9--10, printed pp.107--109, and C.1.34(2), pp.136--137.
-/

public noncomputable section
namespace Representation.SL3DoubledNaturalOffenders
open Matrix BinaryOffender Theory.GroupTheory
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F]
namespace AllFields

omit [Finite F] in
/-- Tensor faithfulness retains the full cubic center in even degree. -/
theorem tensor_asGroupHom_injective :
    Function.Injective (tensorRepresentation F).asGroupHom := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro p hp
  have haction (v : Space F) (i : Fin 2) :
      p.1.val.mulVec (multiplicity F p.2.val v i) = v i :=
    congrArg (fun b : Ambient F => b.val v i) hp
  obtain ⟨a,ha,hg,hc⟩ := tensor_identity_scalar_factors p.1.val p.2.val haction
  have hd : (a⁻¹)^2 = 1 := by
    have hh := congrArg Matrix.det hc
    simpa [Matrix.det_smul,p.2.property] using hh.symm
  have hi : a⁻¹ = 1 := CharTwo.sq_injective (by simpa using hd)
  have ha1 : a = 1 := by simpa using congrArg Inv.inv hi
  change p = (1,1)
  exact Prod.ext (Subtype.ext (by simpa [ha1] using hg))
    (Subtype.ext (by simpa [ha1] using hc))

omit [Algebra (ZMod 2) F] in
/-- Elementary subgroups of the full special linear group have order at most q². -/
theorem natural_elementary_card_le {m : ℕ} (hF : Nat.card F = 2^m)
    (hpos : 0 < m) (A : Subgroup (SL F)) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ Nat.card F ^ 2 := by
  have hb := (primeRank_le_iff_elementary_card_le (SL F)).mp
    (HermitianTensorThree.ImageOuter.OuterRank.specialLinearThree_twoRank F hpos hF).le
    A inferInstance
  simpa only [hF,←pow_mul,Nat.mul_comm m 2] using hb

omit [Finite F] in
/-- The multiplicity coordinate is trivial exactly for actors in the marked component. -/
theorem tensor_mem_component_iff {m : ℕ} (_hF : Nat.card F = 2 ^ m)
    (p : SL F × MultiplicitySL F) :
    (tensorRepresentation F).asGroupHom p ∈ component F ↔ p.2 = 1 := by
  have hone (g : SL F) : (tensorRepresentation F).asGroupHom (g, 1) =
      (representation F).asGroupHom g := by
    apply Units.ext
    change representation F g * multiplicityRepresentation F 1 = representation F g
    rw [map_one, mul_one]
  constructor
  · rintro ⟨g,hg⟩
    exact congrArg Prod.snd (tensor_asGroupHom_injective (F := F) ((hone g).trans hg)).symm
  · intro hp
    refine ⟨p.1, ?_⟩
    have he : p = (p.1,1) := Prod.ext rfl hp
    rw [he]
    exact (hone _).symm

private lemma le_projection_product {G H : Type*} [Group G] [Group H]
    (E : Subgroup (G × H)) :
    E ≤ (E.map (MonoidHom.fst G H)).prod (E.map (MonoidHom.snd G H)) := by
  intro p hp
  exact ⟨⟨p,hp,rfl⟩, ⟨p,hp,rfl⟩⟩

private lemma product_card_le {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (hpos : 0 < m) (E : Subgroup (SL F × MultiplicitySL F))
    [IsElementaryAbelian 2 E] :
    Nat.card ((E.map (MonoidHom.fst _ _)).prod (E.map (MonoidHom.snd _ _))) ≤
      2 ^ (3 * m) := by
  let P := E.map (MonoidHom.fst (SL F) (MultiplicitySL F))
  let Q := E.map (MonoidHom.snd (SL F) (MultiplicitySL F))
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map _
  change Nat.card (P.prod Q) ≤ _
  rw [Nat.card_congr (Subgroup.prodEquiv P Q).toEquiv, Nat.card_prod]
  calc
    Nat.card P * Nat.card Q ≤ Nat.card F ^ 2 * Nat.card F :=
      Nat.mul_le_mul (natural_elementary_card_le hF hpos P)
        (multiplicity_elementary_card_le Q)
    _ = 2 ^ (3 * m) := by rw [hF, ← pow_mul, ← pow_add]; congr 1; omega

/-- Every elementary tensor subgroup acting nontrivially on multiplicities
has binary rank strictly smaller than its fixed codimension. This includes every positive binary field degree. -/
theorem rank_lt_fixedCodim_of_le_tensorSubgroup {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (hpos : 0 < m) {A : Subgroup (Ambient F)}
    (hA : IsElementaryTwo A) (hAT : A ≤ tensorSubgroup F) (hAC : ¬ A ≤ component F) :
    rank A < fixedCodim (action F) A := by
  classical
  let : Finite (Module.End (ZMod 2) (Space F)) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) (Space F) =>
      (f : Space F → Space F)) DFunLike.coe_injective
  let φ := (tensorRepresentation F).asGroupHom
  have hφ := tensor_asGroupHom_injective (F := F)
  let E := A.comap φ
  have hEA : E.map φ = A := Subgroup.map_comap_eq_self hAT
  let e : E ≃* A := (E.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hEA)
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hcard : Nat.card E = Nat.card A := Nat.card_congr e.toEquiv
  let P := E.map (MonoidHom.fst (SL F) (MultiplicitySL F))
  let Q := E.map (MonoidHom.snd (SL F) (MultiplicitySL F))
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map _
  have hEP : E ≤ P.prod Q := le_projection_product E
  have hprod : Nat.card (P.prod Q) ≤ 2 ^ (3 * m) := product_card_le hF hpos E
  have hr : rank A ≤ 3 * m := by
    have hb := Nat.log_mono_right (b := 2) ((Subgroup.card_le_of_le hEP).trans hprod)
    rwa [hcard, Nat.log_pow (by decide : 1 < 2)] at hb
  obtain ⟨p,hp,hp2⟩ : ∃ p ∈ E, p.2 ≠ 1 := by
    by_contra! hn
    apply hAC
    intro a ha
    obtain ⟨p,hpa⟩ := hAT ha
    rw [← hpa]
    apply (tensor_mem_component_iff hF p).mpr
    exact hn p (show φ p ∈ A by rw [hpa]; exact ha)
  obtain ⟨c,hc⟩ := multiplicity_conjugate_upper Q
  have hdQ : p.2 ∈ Q := ⟨p,hp,rfl⟩
  have hconj := hc (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hdQ)
  obtain ⟨t,ht⟩ := (SpecialLinearGroup.mem_upperUnipotent F _).mp hconj
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hp2
    apply (MulAut.conj c).injective
    change c * p.2 * c⁻¹ = c * 1 * c⁻¹
    change SpecialLinearGroup.transvection zero_ne_one t = c * p.2 * c⁻¹ at ht
    rw [← ht, ht0, SpecialLinearGroup.transvection_coeff_zero]
    simp
  have hge := fixedCodim_ge_three_mul_of_conjugate_upper hF p.1 c p.2 ht0 ht.symm hp
  by_cases hmax : rank A = 3 * m
  · have hEcard : Nat.card E = 2 ^ (3 * m) := by
      rw [hcard, hA.card_eq_two_pow_rank, hmax]
    have hEprod : E = P.prod Q :=
      Subgroup.eq_of_le_of_card_ge hEP (hEcard ▸ hprod)
    have hP : P ≠ ⊥ := by
      intro hP
      have hb := Subgroup.card_le_of_le hEP
      rw [hEcard, Nat.card_congr (Subgroup.prodEquiv P Q).toEquiv,
        Nat.card_prod, hP, Subgroup.card_bot, one_mul] at hb
      have hle := hb.trans (multiplicity_elementary_card_le Q)
      rw [hF, Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at hle
      omega
    obtain ⟨g,hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP
    have hg1 : (g : SL F) ≠ 1 := fun he => hg (Subtype.ext he)
    have ha : φ (1,p.2) ∈ A := by
      change (1,p.2) ∈ E
      rw [hEprod]
      exact ⟨P.one_mem,hdQ⟩
    have hb : φ (g,1) ∈ A := by
      change (g.val,1) ∈ E
      rw [hEprod]
      exact ⟨g.property,Q.one_mem⟩
    rw [hmax]
    exact fixedCodim_gt_three_mul_of_conjugate_pure hF hg1 c p.2 ht0 ht.symm ha hb
  · exact (lt_of_le_of_ne hr hmax).trans_le hge

/-- Offenders contained in the actual tensor subgroup lie in the identically
marked natural SL₃ component. Tensor containment is the sole localization premise. -/
theorem offender_le_component_of_le_tensorSubgroup {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (hpos : 0 < m) {A : Subgroup (Ambient F)}
    (hA : IsOffender (action F) A) (hAT : A ≤ tensorSubgroup F) : A ≤ component F := by
  by_contra hAC
  exact (not_lt_of_ge hA.2)
    (rank_lt_fixedCodim_of_le_tensorSubgroup hF hpos hA.1 hAT hAC)

end AllFields
end Representation.SL3DoubledNaturalOffenders
