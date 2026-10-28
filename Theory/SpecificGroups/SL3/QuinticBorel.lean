module
public import Theory.SpecificGroups.SL3.QuinticParabolic
public import Theory.SpecificGroups.SL3.QuinticRadical
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
/-!
# Quintic actors normalized by a linear-three Sylow normalizer

An odd-order automorphism has no graph factor. If all Borel displacements
lie in its unipotent radical, the faithful torus axis kills the field part.
The diagonal quotient has exponent dividing three, so a quintic actor is
inner; its conjugator lies in the same five-free Borel, a contradiction.
The actor group's two-group inner intersection forces those displacements.

The calculation descends through the literal cubic center of SL₃ and is
transported back by the faithful central-quotient action. It includes both
the specified Sylow subgroup and the original component equivalence.
Source: Aschbacher--Smith 14.6.15, printed p.1035; GLS3 §2.7. Imported ATLAS
models retain attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups Pointwise
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.SixCommutators
namespace Matrix.SL3.QuinticBorel
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable (F : Type*) [Field F] [Finite F] [CharP F 2] {n : ℕ}

omit [CharP F 2] in
theorem five_not_dvd_borelSL (hF : Nat.card F = 2^n) (hd : ¬4 ∣ n) :
    ¬5 ∣ Nat.card (borelSL F) := by
  rw [DefiningSylow.card_borelSL,hF]
  have hu := (by decide : Nat.Prime 5).coprime_iff_not_dvd.mp
    (Matrix.PSL3.LinearThree.QuinticParabolic.five_coprime_units F hF hd)
  rw [Nat.card_units,hF] at hu
  apply (by decide : Nat.Prime 5).not_dvd_mul
  · intro hh
    exact (by decide : ¬(5:ℕ) ∣ 2)
      ((by decide : Nat.Prime 5).dvd_of_dvd_pow
        ((by decide : Nat.Prime 5).dvd_of_dvd_pow hh))
  · exact fun hh => hu ((by decide : Nat.Prime 5).dvd_of_dvd_pow hh)

private theorem projective_borel_rigidity (hn : 1 < n) (hF : Nat.card F = 2^n) (hd : ¬4 ∣ n)
    (a : MulAut PSL(3,F)) (ha : orderOf a = 5)
    (hU : (unipotent F).map a.toMonoidHom = unipotent F)
    (hfix : ∀ b ∈ borel F, a b * b⁻¹ ∈ unipotent F) : False := by
  have hcover := Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation
    F (by omega) hF
    (Matrix.PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots_of_charTwo F)
  have hp : a^5=1 := ha ▸ pow_orderOf_eq_one a
  have haL := Matrix.PSL3.SplitPrimeActors.primePower_mem_linearField (by decide : Odd 5)
    a (hcover ▸ mem_top a) (m := 1) (by simpa using hp)
  obtain ⟨g,σ,he⟩ := linearField_factorization F a haL
  have he' : a = projectiveActor F g σ false := by simpa only [projectiveActor, Bool.false_eq_true, ↓reduceIte,mul_one] using he
  have hm := NormalizerForm.linearConj_upperTriangular F g
    (linear_part_unipotent F g σ false (he' ▸ hU))
  have hσ : σ=1 := by
    apply RingEquiv.ext
    intro x
    by_cases hx : x=0
    · simp [hx]
    · let u : Fˣ := Units.mk0 x hx
      have hh := hfix (torusMap F (u,1)) (torus_le_borel F ⟨(u,1),rfl⟩)
      rw [he'] at hh
      simp only [projectiveActor,Bool.false_eq_true,↓reduceIte,mul_one,
        MulAut.mul_apply,field_torusMap,map_one] at hh
      have hparam := ResidualLinear.parameters_eq_of_displacement g hm _ _ hh
      exact congrArg Units.val (ResidualParameters.projective_axis_injective hparam)
  rw [hσ,map_one,mul_one] at he
  have hi : a ∈ MulAut.innerSubgroup PSL(3,F) := by
    have hc : a^3 ∈ MulAut.innerSubgroup PSL(3,F) := he ▸ ResidualInner.linearConj_cube_inner g
    exact (zpowers_le.mpr hc) (mem_zpowers_pow_iff.mpr (by rw [ha]; decide))
  obtain ⟨x,hx⟩ := hi
  have hxN : x ∈ normalizer (unipotent F : Set PSL(3,F)) := by
    rw [mem_normalizer_iff_map_conj_eq,hx]
    exact hU
  rw [normalizer_unipotent F (by omega) hF] at hxN
  have hfive : 5 ∣ Nat.card (borel F) := by
    let t : borel F →* MulAut PSL(3,F) := MulAut.conj.comp (borel F).subtype
    have ht : t ⟨x,hxN⟩ = a := hx
    exact ha ▸ ht ▸ (orderOf_map_dvd t ⟨x,hxN⟩).trans (orderOf_dvd_natCard (⟨x,hxN⟩ : borel F))
  have hproj : Nat.card (borel F) ∣ Nat.card (borelSL F) := card_map_dvd _ _
  exact five_not_dvd_borelSL F hF hd (hfive.trans hproj)

theorem no_projective_borel_actor (hn : 1 < n) (hF : Nat.card F = 2^n) (hd : ¬4 ∣ n)
    (A : Subgroup (MulAut (PSL(3,F))))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup (PSL(3,F)) : Subgroup _))
    (hN : (borel F).map (MulAut.conj : PSL(3,F) →* MulAut (PSL(3,F))) ≤ normalizer (A : Set _))
    (a : MulAut (PSL(3,F))) (ha : a ∈ A)
    (hfix : (unipotent F).map a.toMonoidHom = unipotent F)
    (ha5 : orderOf a = 5) : False := by
  let D := (A ⊓ MulAut.innerSubgroup (PSL(3,F))).comap MulAut.conj
  have hD : IsPGroup 2 D := hi.comap_of_injective _
    (inner_injective F)
  have hbfix (b : zpowers a) : (unipotent F).map b.val.toMonoidHom = unipotent F :=
    (zpowers_le.mpr hfix : zpowers a ≤ MulAction.stabilizer (MulAut (PSL(3,F))) (unipotent F)) b.property
  have hbA (b : zpowers a) : b.val ∈ A := (zpowers_le.mpr ha) b.property
  have dd (b : zpowers a) (x : PSL(3,F)) (hx : x ∈ borel F) :
      x⁻¹ * b.val x ∈ unipotent F := by
    have hn := hN (mem_map_of_mem MulAut.conj hx)
    have ha' : (MulAut.conj x)⁻¹ * b.val * MulAut.conj x ∈ A :=
      (mem_normalizer_iff.mp (inv_mem hn) b.val).mp (hbA b)
    have he : MulAut.conj (x⁻¹ * b.val x) =
        ((MulAut.conj x)⁻¹ * b.val * MulAut.conj x) * b.val⁻¹ := by
      ext y : 1
      change (x⁻¹ * b.val x) * y * (x⁻¹ * b.val x)⁻¹ =
        x⁻¹ * b.val (x * b.val.symm y * x⁻¹) * x
      simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
      group
    have hm : x⁻¹ * b.val x ∈ D :=
      ⟨he ▸ A.mul_mem ha' (A.inv_mem (hbA b)),⟨_,rfl⟩⟩
    have hb : (borel F).map b.val.toMonoidHom = borel F := by
      rw [←normalizer_unipotent F (by omega) hF]
      rw [map_equiv_normalizer_eq,hbfix b]
    have hx' : b.val x ∈ borel F := hb ▸ mem_map_of_mem b.val.toMonoidHom hx
    have hh : x⁻¹ * b.val x ∈ D ⊓ normalizer (unipotentSylow F (by omega) hF : Set (PSL(3,F))) :=
      ⟨hm,by
        change x⁻¹ * b.val x ∈ normalizer (unipotent F : Set (PSL(3,F)))
        rw [normalizer_unipotent F (by omega) hF]
        exact (borel F).mul_mem ((borel F).inv_mem hx) hx'⟩
    rw [hD.inf_normalizer_sylow (unipotentSylow F (by omega) hF)] at hh
    exact hh.2
  apply projective_borel_rigidity F hn hF hd a ha5 hfix
  intro x hx
  have hh := dd ⟨a,mem_zpowers a⟩ x hx
  have hxN : x ∈ normalizer (unipotent F : Set PSL(3,F)) := by
    rw [normalizer_unipotent F (by omega) hF]; exact hx
  have hc := (mem_normalizer_iff.mp hxN (x⁻¹*a x)).mp hh
  simpa only [mul_inv_cancel_left,mul_assoc] using hc

theorem no_projective_marked_sylow_actor
    {C : Type*} [Group C] [Finite C] (e : C ≃* PSL(3,F))
    (hn : 1 < n) (hF : Nat.card F = 2^n) (hd : ¬4 ∣ n) (S : Sylow 2 C)
    (hS : (S : Subgroup C).map e.toMonoidHom = unipotent F)
    (A : Subgroup (MulAut C))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup C : Subgroup _))
    (hN : (normalizer (S : Set C)).map (MulAut.conj : C →* MulAut C) ≤
      normalizer (A : Set _))
    (a : MulAut C) (ha : a ∈ A)
    (hfix : (S : Subgroup C).map a.toMonoidHom = S)
    (ha5 : orderOf a = 5) : False := by
  let f := (MulAut.congr e).toMonoidHom
  let D := A.map f
  have hB : (normalizer (S : Set C)).map e.toMonoidHom = borel F := by
    change (normalizer ((S : Subgroup C) : Set C)).map e.toMonoidHom = borel F
    rw [map_equiv_normalizer_eq,hS,normalizer_unipotent F (by omega) hF]
  have hiD : IsPGroup 2 (D ⊓ MulAut.innerSubgroup (PSL(3,F)) : Subgroup _) := by
    have hh : (A ⊓ MulAut.innerSubgroup C).map f = D ⊓ MulAut.innerSubgroup (PSL(3,F)) := by
      rw [map_inf _ _ f (MulAut.congr e).injective,MulAut.map_innerSubgroup_congr e]
    exact hh ▸ hi.map f
  have hND : (borel F).map (MulAut.conj : PSL(3,F) →* MulAut (PSL(3,F))) ≤
      normalizer (D : Set (MulAut (PSL(3,F)))) := by
    have hc : f.comp (MulAut.conj : C →* MulAut C) =
        (MulAut.conj : PSL(3,F) →* MulAut (PSL(3,F))).comp e.toMonoidHom := by
      ext x : 1
      exact MulAut.congr_conj e x
    have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    rwa [Subgroup.map_map,hc,←Subgroup.map_map,hB] at hh
  have hfixD : (unipotent F).map (MulAut.congr e a).toMonoidHom = unipotent F := by
    rw [←hS,Subgroup.map_map]
    have hc : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by
      ext x : 1
      change e (a (e.symm (e x))) = e (a x)
      rw [e.symm_apply_apply]
    rw [hc,←Subgroup.map_map,hfix]
  exact no_projective_borel_actor F hn hF hd D hiD hND _ (mem_map_of_mem f ha) hfixD
    ((MulAut.congr e).orderOf_eq a |>.trans ha5)

theorem no_projective_sylow_actor
    (hn : 1 < n) (hF : Nat.card F = 2^n) (hd : ¬4 ∣ n)
    (S : Sylow 2 PSL(3,F)) (A : Subgroup (MulAut PSL(3,F)))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup PSL(3,F) : Subgroup _))
    (hN : (normalizer (S : Set PSL(3,F))).map MulAut.conj ≤ normalizer (A : Set _))
    (a : MulAut PSL(3,F)) (ha : a ∈ A) (ha5 : orderOf a = 5)
    (hfix : (S : Subgroup PSL(3,F)).map a.toMonoidHom = S) : False := by
  obtain ⟨g,hg,_⟩ := sylow_normalizer_conjugate F (by omega) hF S
  let e := (MulAut.conj g).symm
  have he : (S : Subgroup PSL(3,F)).map e.toMonoidHom = unipotent F := by
    rw [←hg,Subgroup.map_map]
    have hc : e.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id PSL(3,F) := by
      apply MonoidHom.ext
      intro x
      exact e.apply_symm_apply x
    rw [hc,Subgroup.map_id]
  exact no_projective_marked_sylow_actor F e hn hF hd S he A hi hN a ha hfix ha5



omit [Finite F] [CharP F 2] in
private theorem centerAction_conj_comp :
    (centerAction F).comp (MulAut.conj : SL(3,F) →* MulAut SL(3,F)) =
      (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)).comp (projection F) := by
  ext x : 1
  apply MulEquiv.ext
  intro y
  obtain ⟨y,rfl⟩ := projection_surjective F y
  change centerAction F (MulAut.conj x) (QuotientGroup.mk y) = _
  rw [centerAction_mk]
  change projection F (x*y*x⁻¹) = projection F x * projection F y * (projection F x)⁻¹
  simp only [map_mul,map_inv]

omit [Finite F] [CharP F 2] in
private theorem map_inner :
    (MulAut.innerSubgroup SL(3,F)).map (centerAction F) = MulAut.innerSubgroup PSL(3,F) := by
  apply le_antisymm
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    refine ⟨projection F x,?_⟩
    exact (DFunLike.congr_fun (centerAction_conj_comp F) x).symm
  · rintro _ ⟨y,rfl⟩
    obtain ⟨x,rfl⟩ := projection_surjective F y
    exact ⟨MulAut.conj x,⟨x,rfl⟩,DFunLike.congr_fun (centerAction_conj_comp F) x⟩

/-- The full Sylow normalizer obstruction on SL₃, retaining its scalar center. -/
theorem no_special_sylow_actor (hn : 1 < n) (hF : Nat.card F = 2^n) (hd : ¬4 ∣ n)
    (S : Sylow 2 SL(3,F)) (A : Subgroup (MulAut SL(3,F)))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup SL(3,F) : Subgroup _))
    (hN : (normalizer (S : Set SL(3,F))).map MulAut.conj ≤ normalizer (A : Set _))
    (a : MulAut SL(3,F)) (ha : a ∈ A) (ha5 : orderOf a = 5)
    (hfix : (S : Subgroup SL(3,F)).map a.toMonoidHom = S) : False := by
  let f := centerAction F
  let D := A.map f
  let T := S.mapSurjective (projection_surjective F)
  have hiD : IsPGroup 2 (D ⊓ MulAut.innerSubgroup PSL(3,F) : Subgroup _) := by
    have hh : (A ⊓ MulAut.innerSubgroup SL(3,F)).map f = D ⊓ MulAut.innerSubgroup PSL(3,F) := by
      rw [map_inf _ _ f (ActorCoverage.centerAction_injective F),map_inner F]
    exact hh ▸ hi.map f
  have hND : (normalizer (T : Set PSL(3,F))).map MulAut.conj ≤ normalizer (D : Set _) := by
    have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    rw [Subgroup.map_map,centerAction_conj_comp F,←Subgroup.map_map,
      S.normalizer_map_surjective (projection F) (projection_surjective F)] at hh
    exact hh
  have hfixD : (T : Subgroup PSL(3,F)).map (f a).toMonoidHom = T := by
    change ((S : Subgroup SL(3,F)).map (projection F)).map (f a).toMonoidHom =
      (S : Subgroup SL(3,F)).map (projection F)
    have he : (f a).toMonoidHom.comp (projection F) = (projection F).comp a.toMonoidHom := by
      ext x : 1
      exact centerAction_mk F a x
    rw [Subgroup.map_map,he,←Subgroup.map_map,hfix]
  exact no_projective_sylow_actor F hn hF hd T D hiD hND (f a) (mem_map_of_mem f ha)
    ((orderOf_injective f (ActorCoverage.centerAction_injective F) a).trans ha5) hfixD

omit [CharP F 2] in
/-- Normalizing the specified Sylow cannot be inner for an order-five actor
when the actual Borel is five-free. -/
theorem sylow_quintic_not_inner (hn : 0 < n) (hF : Nat.card F = 2^n) (hd : ¬4 ∣ n)
    {C : Type*} [Group C] [Finite C] (e : C ≃* SL(3,F))
    (S : Sylow 2 C) (a : MulAut C) (ha : orderOf a = 5)
    (hfix : (S : Subgroup C).map a.toMonoidHom = S) : a ∉ MulAut.innerSubgroup C := by
  rintro ⟨x,hx⟩
  have hxN : x ∈ normalizer (S : Set C) := mem_normalizer_iff_map_conj_eq.mpr (by rw [hx]; exact hfix)
  let f : normalizer (S : Set C) →* MulAut C := MulAut.conj.comp (normalizer (S : Set C)).subtype
  have hf : f ⟨x,hxN⟩ = a := hx
  have h5 : 5 ∣ Nat.card (normalizer (S : Set C)) :=
    ha ▸ hf ▸ (orderOf_map_dvd f ⟨x,hxN⟩).trans (orderOf_dvd_natCard (⟨x,hxN⟩ : normalizer (S : Set C)))
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : Nat.card (normalizer (S : Set C)) = Nat.card (normalizer (T : Set SL(3,F))) := by
    change Nat.card (normalizer ((S : Subgroup C) : Set C)) =
      Nat.card (normalizer ((S : Subgroup C).map e.toMonoidHom : Set SL(3,F)))
    rw [←map_equiv_normalizer_eq (S : Subgroup C) e]
    exact (card_map_of_injective e.injective).symm
  rw [he,Nat.card_congr (sylowSLNormalizerEquiv F hn hF T).toEquiv] at h5
  exact five_not_dvd_borelSL F hF hd h5

/-- Transport the obstruction along the original component model. -/
theorem no_sylow_actor_of_equiv (hn : 1 < n) (hF : Nat.card F = 2^n) (hd : ¬4 ∣ n)
    {C : Type*} [Group C] [Finite C] (e : C ≃* SL(3,F))
    (S : Sylow 2 C) (A : Subgroup (MulAut C))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup C : Subgroup _))
    (hN : (normalizer (S : Set C)).map MulAut.conj ≤ normalizer (A : Set _))
    (a : MulAut C) (ha : a ∈ A) (ha5 : orderOf a = 5)
    (hfix : (S : Subgroup C).map a.toMonoidHom = S) : False := by
  let f := (MulAut.congr e).toMonoidHom
  let D := A.map f
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hiD : IsPGroup 2 (D ⊓ MulAut.innerSubgroup SL(3,F) : Subgroup _) := by
    have hh : (A ⊓ MulAut.innerSubgroup C).map f = D ⊓ MulAut.innerSubgroup SL(3,F) := by
      rw [map_inf _ _ f (MulAut.congr e).injective,MulAut.map_innerSubgroup_congr e]
    exact hh ▸ hi.map f
  have hND : (normalizer (T : Set SL(3,F))).map MulAut.conj ≤ normalizer (D : Set _) := by
    have hc : f.comp (MulAut.conj : C →* MulAut C) =
        (MulAut.conj : SL(3,F) →* MulAut SL(3,F)).comp e.toMonoidHom := by
      ext x : 1
      exact MulAut.congr_conj e x
    have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    rw [Subgroup.map_map,hc,←Subgroup.map_map,
      S.normalizer_map_surjective e.toMonoidHom e.surjective] at hh
    exact hh
  have hfixD : (T : Subgroup SL(3,F)).map (MulAut.congr e a).toMonoidHom = T := by
    change ((S : Subgroup C).map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom =
      (S : Subgroup C).map e.toMonoidHom
    rw [Subgroup.map_map]
    have hc : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by
      ext x : 1
      change e (a (e.symm (e x))) = e (a x)
      rw [e.symm_apply_apply]
    rw [hc,←Subgroup.map_map,hfix]
  exact no_special_sylow_actor F hn hF hd T D hiD hND _ (mem_map_of_mem f ha)
    ((MulAut.congr e).orderOf_eq a |>.trans ha5) hfixD

end Matrix.SL3.QuinticBorel
