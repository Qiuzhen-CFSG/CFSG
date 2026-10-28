module
public import Theory.Representation.BinaryDoubledNaturalNormalizer
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.Representation.SL3DoubledNaturalOffenders.BinaryOrbits
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Swap coordinates for binary doubled-natural two-group extensions

The full doubled-natural normalizer is already identified with SL₃(2) ×
SL₂(2). A two-group in its multiplicity factor is conjugate into the
permutation matrices. Transporting by that same multiplicity matrix gives
coordinates for the entire extension in which the outer action swaps the
two natural copies, while leaving the original component marking intact.

The actual LT action in Chapter 13 uses this construction to apply the
42-point and 14-point orbit calculations, including their local Sylow
conditions and original odd Frattini actions.
Source: Aschbacher--Smith, 13.1.12, printed pp.872--873; B.5.9--10.
-/

public noncomputable section
namespace Representation.SL3DoubledNaturalOffenders
open Matrix Subgroup
namespace BinaryNormalizer

abbrev F := ZMod 2
abbrev B := Ambient F
abbrev H := SL F × MultiplicitySL F

def permutation : Equiv.Perm (Fin 2) →* MultiplicitySL F :=
  (BinaryLinear.OuterCyclic.slEquivLinear 2).symm.toMonoidHom.comp
    { toFun s := LinearEquiv.funCongrLeft F F s.symm
      map_one' := by ext v i; rfl
      map_mul' s t := by ext v i; rfl }

theorem permutation_apply (s : Equiv.Perm (Fin 2)) (v : Fin 2 → F) :
    (permutation s).val.mulVec v = fun i => v (s.symm i) := by
  change BinaryLinear.OuterCyclic.slEquivLinear 2
    ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm _) v = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem permutation_injective : Function.Injective permutation := by
  intro s t h
  have he (v : Fin 2 → F) (i : Fin 2) : v (s.symm i) = v (t.symm i) := by
    rw [← congrFun (permutation_apply s v) i, ← congrFun (permutation_apply t v) i,h]
  apply inv_injective (G := Equiv.Perm (Fin 2))
  apply _root_.Equiv.ext
  intro i
  by_contra hn
  have hh := he (Pi.single (s.symm i) 1) i
  have hn' : t.symm i ≠ s.symm i := Ne.symm hn
  simp [Pi.single_eq_of_ne hn'] at hh

def changeBasis : MultiplicitySL F := ⟨!![1,0;1,1],by decide⟩

theorem upper_into_permutation :
    (SpecialLinearGroup.upperUnipotent F).map (MulAut.conj changeBasis).toMonoidHom ≤
      permutation.range := by
  rintro _ ⟨g,hg,rfl⟩
  obtain ⟨a,rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent F g).mp hg
  have ha : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  rcases ha with rfl | rfl
  · refine ⟨1,?_⟩
    simp
  · refine ⟨Equiv.swap 0 1,?_⟩
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext v
    rw [permutation_apply]
    have hci : changeBasis⁻¹ = changeBasis := by decide
    change (fun i => v ((Equiv.swap (0 : Fin 2) 1).symm i)) =
      (changeBasis * SpecialLinearGroup.transvection (i := 0) (j := 1)
        zero_ne_one 1 * changeBasis⁻¹).val.mulVec v
    rw [hci]
    have hm : (changeBasis * SpecialLinearGroup.transvection (i := 0) (j := 1)
        zero_ne_one 1 * changeBasis).val = !![0,1;1,0] := by decide
    rw [hm]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Every binary multiplicity two-group can be put in identity-or-swap coordinates. -/
theorem two_group_conjugate_permutation (A : Subgroup (MultiplicitySL F))
    (hA : IsPGroup 2 A) :
    ∃ c : MultiplicitySL F, A.map (MulAut.conj c).toMonoidHom ≤ permutation.range := by
  obtain ⟨P,hP⟩ := hA.exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq (MultiplicitySL F) P
    (SpecialLinearGroup.upperUnipotentSylow F 2)
  have he : (P : Subgroup (MultiplicitySL F)).map (MulAut.conj c).toMonoidHom =
      SpecialLinearGroup.upperUnipotent F := congrArg Sylow.toSubgroup hc
  have hA' : A.map (MulAut.conj c).toMonoidHom ≤ SpecialLinearGroup.upperUnipotent F :=
    he ▸ Subgroup.map_mono hP
  have hmaps := (Subgroup.map_mono (f := (MulAut.conj changeBasis).toMonoidHom) hA').trans
    upper_into_permutation
  rw [Subgroup.map_map] at hmaps
  have hh : (MulAut.conj changeBasis).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (changeBasis * c)).toMonoidHom := by
    apply MonoidHom.ext
    intro a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      _root_.mul_inv_rev,mul_assoc]
  rw [hh] at hmaps
  exact ⟨changeBasis * c,hmaps⟩

theorem tensor_permutation (g : SL F) (s : Equiv.Perm (Fin 2)) (v : Space F) :
    tensorRepresentation F (g,permutation s) v = BinaryOrbits.outerRepresentation (g,s) v := by
  funext i
  change g.val.mulVec (multiplicity F (permutation s).val v i) = g.val.mulVec (v (s.symm i))
  congr 1
  ext j
  change (permutation s).val i 0 * v 0 j + (permutation s).val i 1 * v 1 j = _
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
    congrFun (permutation_apply s (fun k => v k j)) i

/-- The entire extension by a multiplicity two-group has simultaneous swap coordinates. -/
theorem two_group_extension {K : Type*} [Group K] (q : K →* H)
    (hq : IsPGroup 2 ((MonoidHom.snd (SL F) (MultiplicitySL F)).comp q).range) :
    ∃ e : Space F ≃ₗ[F] Space F,
      ∃ r : K →* SL F × Equiv.Perm (Fin 2),
        (∀ k v, e (tensorRepresentation F (q k) v) =
          BinaryOrbits.outerRepresentation (r k) (e v)) ∧
        (∀ k, (q k).2 = 1 → r k = ((q k).1,1)) := by
  let q₂ := (MonoidHom.snd (SL F) (MultiplicitySL F)).comp q
  obtain ⟨c,hc⟩ := two_group_conjugate_permutation q₂.range hq
  let j := MonoidHom.ofInjective permutation_injective
  let q₂c := (MulAut.conj c).toMonoidHom.comp q₂
  have hr (k : K) : q₂c k ∈ permutation.range := hc ⟨q₂ k,⟨k,rfl⟩,rfl⟩
  let r₂ := j.symm.toMonoidHom.comp (q₂c.codRestrict permutation.range hr)
  let r := ((MonoidHom.fst (SL F) (MultiplicitySL F)).comp q).prod r₂
  have he₂ (k : K) : permutation (r₂ k) = c * (q k).2 * c⁻¹ := by
    exact congrArg Subtype.val (j.apply_symm_apply ⟨q₂c k,hr k⟩)
  let b := (tensorRepresentation F).asGroupHom (1,c)
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv b
  refine ⟨e,r,?_,?_⟩
  · intro k v
    change tensorRepresentation F (1,c) (tensorRepresentation F (q k) v) =
      BinaryOrbits.outerRepresentation ((q k).1,r₂ k) (tensorRepresentation F (1,c) v)
    rw [← tensor_permutation,he₂]
    change (tensorRepresentation F (1,c) * tensorRepresentation F (q k)) v =
      (tensorRepresentation F ((q k).1,c * (q k).2 * c⁻¹) *
        tensorRepresentation F (1,c)) v
    rw [← map_mul,← map_mul]
    congr 2
    ext <;> simp
  · intro k hk
    change ((q k).1,r₂ k) = ((q k).1,1)
    apply Prod.ext
    · rfl
    change r₂ k = 1
    apply permutation_injective
    rw [he₂,hk,map_one]
    simp

end BinaryNormalizer
end Representation.SL3DoubledNaturalOffenders
