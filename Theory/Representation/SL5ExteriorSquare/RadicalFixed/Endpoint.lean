module
public import Theory.Representation.SL5ExteriorSquare.RadicalFixed.StandardCuts
public import Theory.SpecificGroups.BinaryLinear.RadicalCut
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import Theory.GroupTheory.PRadicalSylowNormalizer
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Six fixed dimensions force the actual hyperplane radical

The canonical radical filtration supplies a full block radical in the original
subgroup. An explicitly retained conjugation puts that block in standard form.
The four fixed-space bounds force the hyperplane cut. Its six-space is then
fixed pointwise by the whole radical, which forces equality with the full
hyperplane radical. No parabolic or coordinate replacement is assumed.
Source: Aschbacher--Smith C.4.8 and 12.5.2, pp.154,817.
-/
public noncomputable section
open Subgroup
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional BinaryLinear.OuterCyclic

private theorem exists_conjugate_cut (P : Subgroup Group) (hP : P.IsPRadical 2) :
    ∃ (g : Group) (k : Fin 4),
      parabolicUnipotent (k.val+1) ≤ P.map (MulAut.conj g).toMonoidHom := by
  let e := slEquivLinear 5
  obtain ⟨W,hW0,hWt,hWP⟩ := BinaryLinear.exists_radical_cut
    (P.map e.toMonoidHom) (hP.map_equiv e)
  have hd0 : 0 < Module.finrank (ZMod 2) W := by
    exact Nat.pos_of_ne_zero (fun hh => hW0 (Submodule.finrank_eq_zero.mp hh))
  have hd5 : Module.finrank (ZMod 2) W < 5 := by
    have hh : Module.finrank (ZMod 2) W ≤ 5 := by simpa using Submodule.finrank_le W
    by_contra hn
    apply hWt
    apply Submodule.eq_of_le_of_finrank_eq le_top
    simpa using (show Module.finrank (ZMod 2) W = 5 by omega)
  let k : Fin 4 := ⟨Module.finrank (ZMod 2) W-1,by omega⟩
  have hk : k.val+1 = Module.finrank (ZMod 2) W := by dsimp [k]; omega
  obtain ⟨a,ha⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq
    W (naturalFlag (k.val+1)) (by rw [finrank_naturalFlag _ (by omega),hk])
  let g := e.symm a
  have he : e g = a := e.apply_symm_apply a
  have hm : (P.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (P.map e.toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
      map_mul,map_inv,he]
  refine ⟨g,k,?_⟩
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [show (parabolicUnipotent (k.val+1)).map e.toMonoidHom =
    BinaryLinear.radical (naturalFlag (k.val+1)) from map_comap_eq_self_of_surjective e.surjective _,hm]
  have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hWP
  rwa [radical_map_conj,ha] at hh

private theorem finrank_fixed_conjugate (P : Subgroup Group) (g : Group) :
    Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2)
      (P.map (MulAut.conj g).toMonoidHom)) =
    Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2) P) := by
  let E : V ≃ₗ[ZMod 2] V :=
    LinearMap.GeneralLinearGroup.toLinearEquiv ((exteriorAction 2).asGroupHom g)
  have hE (a : Group) (v : V) :
      E (exteriorAction 2 a v) = exteriorAction 2 ((MulAut.conj g) a) (E v) := by
    change exteriorAction 2 g (exteriorAction 2 a v) =
      exteriorAction 2 (g*a*g⁻¹) (exteriorAction 2 g v)
    simp only [← Module.End.mul_apply,←map_mul]
    simp [mul_assoc]
  have hm := BinaryOffender.fixedSpace_map_equivariant (exteriorAction 2)
    (exteriorAction 2) (MulAut.conj g).toMonoidHom E hE P
  rw [←hm,E.finrank_map_eq]

private theorem le_hyperplane_radical_of_fixed (P : Subgroup Group)
    (hfix : BinaryOffender.fixedSpace (exteriorAction 2) P = V₆) :
    P ≤ parabolicUnipotent 4 := by
  have hf (g : Group) (hg : g ∈ P) (v : V) (hv : v ∈ V₆) :
      exteriorAction 2 g v = v := (hfix.symm ▸ hv) ⟨g,hg⟩
  intro g hg
  rw [parabolicUnipotent_four_eq_shearSubgroup,←pointwiseV₆_eq_shearSubgroup]
  refine ⟨?_,hf g hg⟩
  rw [←exteriorStabilizer_V₆_eq_parabolic]
  intro v
  constructor
  · intro hv
    have hh := hf g⁻¹ (P.inv_mem hg) (exteriorAction 2 g v) hv
    have hv' : exteriorAction 2 g⁻¹ (exteriorAction 2 g v) = v := by
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one]
      rfl
    rw [hv'] at hh
    exact hh.symm ▸ hv
  · intro hv
    rw [hf g hg v hv]
    exact hv

private theorem normalizer_hyperplane_radical :
    normalizer (parabolicUnipotent 4 : Set Group) = parabolic 4 := by
  let e := slEquivLinear 5
  have hR : (parabolicUnipotent 4).map e.toMonoidHom =
      BinaryLinear.radical (naturalFlag 4) := map_comap_eq_self_of_surjective e.surjective _
  have hM : (parabolic 4).map e.toMonoidHom = BinaryLinear.parabolic (naturalFlag 4) := by
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      exact hg
    · intro g hg
      refine ⟨e.symm g,?_,e.apply_symm_apply g⟩
      intro v
      change e (e.symm g) v ∈ naturalFlag 4 ↔ v ∈ naturalFlag 4
      rw [e.apply_symm_apply]
      exact hg v
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_equiv_normalizer_eq,hR,hM]
  apply BinaryLinear.normalizer_radical
  intro he
  have hh := finrank_naturalFlag 4 (by decide)
  have hz : Module.finrank (ZMod 2) (naturalFlag 4) = 0 :=
    Submodule.finrank_eq_zero.mpr he
  omega

/-- Any actual radical fixing at least a six-space is conjugate to the full
hyperplane radical, with its exact fixed six-space and conjugating element retained. -/
theorem radical_six_fixed_hyperplane (P : Subgroup Group) (hP : P.IsPRadical 2)
    (hd : 6 ≤ Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2) P)) :
    ∃ g : Group,
      P.map (MulAut.conj g).toMonoidHom = parabolicUnipotent 4 ∧
      normalizer (P.map (MulAut.conj g).toMonoidHom : Set Group) = parabolic 4 ∧
      BinaryOffender.fixedSpace (exteriorAction 2) (P.map (MulAut.conj g).toMonoidHom) = V₆ ∧
      Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2) P) = 6 := by
  obtain ⟨g,k,hcut⟩ := exists_conjugate_cut P hP
  let Q := P.map (MulAut.conj g).toMonoidHom
  have hle : BinaryOffender.fixedSpace (exteriorAction 2) Q ≤
      BinaryOffender.fixedSpace (exteriorAction 2) (parabolicUnipotent (k.val+1)) := by
    intro v hv a
    exact hv ⟨a,hcut a.property⟩
  have he := finrank_fixed_conjugate P g
  have hb := (Submodule.finrank_mono hle).trans (finrank_fixed_parabolicUnipotent_le k)
  have hk : k = 3 := by
    change Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2) Q) = _ at he
    fin_cases k <;> first | rfl | (norm_num at hb; omega)
  subst k
  change parabolicUnipotent 4 ≤ Q at hcut
  change BinaryOffender.fixedSpace (exteriorAction 2) Q ≤
    BinaryOffender.fixedSpace (exteriorAction 2) (parabolicUnipotent 4) at hle
  rw [fixedSpace_parabolicUnipotent_four] at hle
  have hqdim : Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2) Q) = 6 := by
    change Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2) Q) = _ at he
    have hh := Submodule.finrank_mono hle
    rw [standard_dimensions.2.2.2.1] at hh
    omega
  have hfix : BinaryOffender.fixedSpace (exteriorAction 2) Q = V₆ :=
    Submodule.eq_of_le_of_finrank_eq hle (hqdim.trans standard_dimensions.2.2.2.1.symm)
  have hQ : Q = parabolicUnipotent 4 :=
    le_antisymm (le_hyperplane_radical_of_fixed Q hfix) hcut
  exact ⟨g,hQ,by
    change normalizer (Q : Set Group) = parabolic 4
    rw [hQ,normalizer_hyperplane_radical],hfix,he.symm.trans hqdim⟩

end Representation.SL5ExteriorSquare
