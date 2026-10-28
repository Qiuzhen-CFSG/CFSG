module

public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.SL3RepeatedNaturalFlagTypes


/-!
# Natural SL3 actions cannot be minimal parabolic

Mark the actual Sylow intersection with the standard upper unipotent group.
The linear intertwiner for every element of the ambient Sylow preserves both
natural flags, so both standard maximal parabolics lift to proper Sylow
overgroups. Their join contains the normal SL3 supplement, contradicting the
unique maximal overgroup condition. The argument applies to positive repeated
natural modules and to any actual invariant section carrying such an action.

Source: Aschbacher–Smith, proof of B.6.9, printed p.116 (1 March 2004).
No invariant-parabolic premise or family-recognition conclusion is assumed.
-/

public section

open Subgroup Representation
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource Matrix.PSL3.LinearThree

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sup_sylow_ne_top
    (T : Sylow 2 G) (L P : Subgroup G) (hPL : P ≤ L)
    (hTP : (T : Subgroup G) ≤ normalizer (P : Set G))
    (hLP : L ⊓ (T : Subgroup G) ≤ P) (hne : P ≠ L) : P ⊔ (T : Subgroup G) ≠ ⊤ := by
  intro he
  apply hne
  apply le_antisymm hPL
  intro x hx
  have hm : x ∈ (P : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left P (T : Subgroup G) hTP, he]
    trivial
  obtain ⟨p, hp, t, ht, hpt⟩ := hm
  have htL : t ∈ L := by
    have hh := L.mul_mem (L.inv_mem (hPL hp)) hx
    simpa only [← hpt, inv_mul_cancel_left] using hh
  exact hpt ▸ P.mul_mem hp (hLP ⟨htL,ht⟩)

/-- Two proper Sylow-invariant subgroups of a supplement rule out uniqueness. -/
theorem not_minimalParabolic_of_two_overgroups
    (T : Sylow 2 G) (L P Q : Subgroup G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) (hPQ : P ⊔ Q = L)
    (hP : P ≠ L) (hQ : Q ≠ L)
    (hnP : (T : Subgroup G) ≤ normalizer (P : Set G))
    (hnQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hiP : L ⊓ (T : Subgroup G) ≤ P) (hiQ : L ⊓ (T : Subgroup G) ≤ Q) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  intro h
  have hp := sup_sylow_ne_top T L P (le_sup_left.trans hPQ.le) hnP hiP hP
  have hq := sup_sylow_ne_top T L Q (le_sup_right.trans hPQ.le) hnQ hiQ hQ
  let M := minimalParabolicMax T h
  have hm : (T : Subgroup G) ≤ M ∧ M ⋖ ⊤ :=
    ⟨(minimalParabolicMax_spec T h).2, (minimalParabolicMax_spec T h).1.covBy_top⟩
  have hPM := h.1.le_maximal hm le_sup_right (lt_top_iff_ne_top.mpr hp)
  have hQM := h.1.le_maximal hm le_sup_right (lt_top_iff_ne_top.mpr hq)
  have hLM : L ≤ M := by
    rw [← hPQ]
    exact sup_le (le_sup_left.trans hPM) (le_sup_left.trans hQM)
  have hg : (⊤ : Subgroup G) ≤ M := by
    rw [← hgen]
    exact sup_le hLM hm.1
  exact (minimalParabolicMax_spec T h).1.ne_top (top_unique hg)

omit [Finite G] in
private theorem normal_action_flags
    {V F : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Finite F] [CharP F 2]
    (L : Subgroup G) [L.Normal] (ρ : Representation (ZMod 2) G V)
    (e : L ≃* SL(3, F)) (t : G)
    (hU : (unipotentSL F).map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = unipotentSL F)
    (hmodule : ∃ E : BinaryField, ∃ r : ℕ, 0 < r ∧
      IsRepeatedLinearNatural (ρ.comp L.subtype) E 3 r) :
    (pointParabolicSL F).map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = pointParabolicSL F ∧
    (lineParabolicSL F).map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = lineParabolicSL F := by
  obtain ⟨E,r,hr,⟨c⟩⟩ := hmodule
  let d := c.linearEquiv
  let A := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
  let b := d.symm.trans (A.trans d)
  let f := e.symm.trans c.groupEquiv
  have hnat (k : L) (w : V) :
      d (ρ (k : G) w) = fun i => (c.groupEquiv k).val.mulVec ((d w) i) := c.intertwines k w
  have hA (w : V) : A w = ρ t w := rfl
  apply Representation.SL3RepeatedNaturalFlagTypes.flags_of_intertwiner _ hU f hr b
  intro g w
  let k := e.symm g
  have he : c.groupEquiv ((MulAut.conjNormal t) k) =
      f ((MulAut.congr e (MulAut.conjNormal t)) g) := by
    change _ = c.groupEquiv (e.symm (e ((MulAut.conjNormal t) (e.symm g))))
    rw [e.symm_apply_apply]
  calc
    b (fun i => (f g).val.mulVec (w i)) = d (ρ t (ρ (k : G) (d.symm w))) := by
      change d (A (d.symm (fun i => (f g).val.mulVec (w i)))) = _
      rw [hA]
      congr 2
      apply d.injective
      rw [d.apply_symm_apply, hnat, d.apply_symm_apply]
      rfl
    _ = d (ρ (((MulAut.conjNormal t) k : L) : G) (ρ t (d.symm w))) := by
      congr 1
      rw [MulAut.conjNormal_apply]
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
    _ = fun i => (f ((MulAut.congr e (MulAut.conjNormal t)) g)).val.mulVec ((b w) i) := by
      rw [hnat,he]
      rfl

/-- The actual repeated natural action supplies both Sylow-invariant parabolics. -/
theorem exists_sylow_invariant_linear_three_parabolics
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (ρ : Representation (ZMod 2) G V) (F : BinaryField) (r : ℕ) (hr : 0 < r)
    (hmodule : IsRepeatedLinearNatural (ρ.comp L.subtype) F 3 r) :
    ∃ P Q : Subgroup G, P ⊔ Q = L ∧ P ≠ L ∧ Q ≠ L ∧
      (T : Subgroup G) ≤ normalizer (P : Set G) ∧
      (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
      L ⊓ (T : Subgroup G) ≤ P ∧ L ⊓ (T : Subgroup G) ≤ Q := by
  classical
  obtain ⟨c⟩ := hmodule
  let e₀ := c.groupEquiv
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal L
  obtain ⟨g,hg,_⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate
    F.Carrier F.degree_pos F.card_eq (S.mapSurjective (f := e₀.toMonoidHom) e₀.surjective)
  change (unipotentSL F.Carrier).map (MulAut.conj g).toMonoidHom =
    (S : Subgroup L).map e₀.toMonoidHom at hg
  let e := e₀.trans (MulAut.conj g).symm
  have hmark : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom = unipotentSL F.Carrier := by
    rw [← hS]
    change (S : Subgroup L).map ((MulAut.conj g).symm.toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← map_map, ← hg]
    exact (MulAut.conj g).mapSubgroup.symm_apply_apply _
  have hacts (t : T) :
      (unipotentSL F.Carrier).map
        (MulAut.congr e (MulAut.conjNormal (t : G))).toMonoidHom = unipotentSL F.Carrier := by
    have ht : ((T : Subgroup G).subgroupOf L).map (MulAut.conjNormal (t : G)).toMonoidHom =
        (T : Subgroup G).subgroupOf L := by
      apply le_antisymm
      · rintro x ⟨y,hy,rfl⟩
        change (t : G) * (y : G) * (t : G)⁻¹ ∈ (T : Subgroup G)
        exact T.mul_mem (T.mul_mem t.property hy) (T.inv_mem t.property)
      · intro x hx
        refine ⟨MulAut.conjNormal ((t : G)⁻¹) x, ?_, ?_⟩
        · change (((MulAut.conjNormal ((t : G)⁻¹)) x : L) : G) ∈ (T : Subgroup G)
          rw [MulAut.conjNormal_apply, inv_inv]
          exact T.mul_mem (T.mul_mem (T.inv_mem t.property) hx) t.property
        · apply Subtype.ext
          change (((MulAut.conjNormal (t : G))
            ((MulAut.conjNormal ((t : G)⁻¹)) x) : L) : G) = x
          simp only [MulAut.conjNormal_apply, inv_inv]
          group
    have he : (MulAut.congr e (MulAut.conjNormal (t : G))).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp (MulAut.conjNormal (t : G)).toMonoidHom := by
      ext x
      simp [MulAut.congr_apply]
    rw [← hmark, map_map, he, ← map_map, ht]
  let f : SL(3,F.Carrier) →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hftop : (⊤ : Subgroup SL(3,F.Carrier)).map f = L := by
    rw [show f = L.subtype.comp e.symm.toMonoidHom from rfl, ← map_map,
      map_top_of_surjective _ e.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]
  let P := (pointParabolicSL F.Carrier).map f
  let Q := (lineParabolicSL F.Carrier).map f
  have hPQ : P ⊔ Q = L := by
    rw [show P = (pointParabolicSL F.Carrier).map f from rfl,
      show Q = (lineParabolicSL F.Carrier).map f from rfl, ← Subgroup.map_sup,
      parabolicsSL_sup_eq_top, hftop]
  have hP : P ≠ L := by
    intro he
    exact (pointParabolicSL_isCoatom F.Carrier).ne_top (map_injective hf (he.trans hftop.symm))
  have hQ : Q ≠ L := by
    intro he
    exact (lineParabolicSL_isCoatom F.Carrier).ne_top (map_injective hf (he.trans hftop.symm))
  have hnorm (D : Subgroup SL(3,F.Carrier))
      (hd : ∀ t : T, D.map (MulAut.congr e (MulAut.conjNormal (t : G))).toMonoidHom = D) :
      (T : Subgroup G) ≤ normalizer ((D.map f) : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let a := MulAut.congr e (MulAut.conjNormal t)
    have hay : a y ∈ D := by
      rw [← hd ⟨t,ht⟩]
      exact mem_map_of_mem _ hy
    refine ⟨a y,hay,?_⟩
    simp [f,a,MulAut.congr_apply,MulAut.conjNormal_apply]
  have hflags (t : T) := normal_action_flags L ρ e t (hacts t) ⟨F,r,hr,⟨c⟩⟩
  have hint (D : Subgroup SL(3,F.Carrier)) (hd : unipotentSL F.Carrier ≤ D) :
      L ⊓ (T : Subgroup G) ≤ D.map f := by
    rintro x ⟨hxL,hxT⟩
    have hx : e ⟨x,hxL⟩ ∈ unipotentSL F.Carrier := by
      rw [← hmark]
      exact mem_map_of_mem _ hxT
    refine ⟨e ⟨x,hxL⟩, hd hx, ?_⟩
    simp [f]
  exact ⟨P,Q,hPQ,hP,hQ,
    (hnorm _ fun t => (hflags t).1), (hnorm _ fun t => (hflags t).2),
    (hint _ ((unipotentSL_le_borelSL F.Carrier).trans inf_le_left)),
    (hint _ ((unipotentSL_le_borelSL F.Carrier).trans inf_le_right))⟩

/-- A positive repeated natural SL3 supplement cannot be a minimal parabolic. -/
theorem not_minimalParabolic_of_repeated_natural_three
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (ρ : Representation (ZMod 2) G V) (F : BinaryField) (r : ℕ) (hr : 0 < r)
    (hmodule : IsRepeatedLinearNatural (ρ.comp L.subtype) F 3 r) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  obtain ⟨P,Q,hPQ,hP,hQ,hnP,hnQ,hiP,hiQ⟩ :=
    exists_sylow_invariant_linear_three_parabolics T L ρ F r hr hmodule
  exact not_minimalParabolic_of_two_overgroups T L P Q hgen hPQ hP hQ hnP hnQ hiP hiQ

/-- The single natural module is already incompatible with minimal parabolicity. -/
theorem not_minimalParabolic_of_natural_three
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (ρ : Representation (ZMod 2) G V) (F : BinaryField)
    (hmodule : IsLinearNatural (ρ.comp L.subtype) F 3) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  obtain ⟨c⟩ := hmodule
  apply not_minimalParabolic_of_repeated_natural_three T L hgen ρ F 1 (by decide)
  refine ⟨⟨c.groupEquiv, c.linearEquiv.trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 3 → F.Carrier)).symm, ?_⟩⟩
  intro g v
  funext i
  exact c.intertwines g v

/-- The actual two-residual of a minimal parabolic has no repeated natural SL3 action. -/
theorem minimalParabolic_not_repeated_natural_residual_three
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) G V) (F : BinaryField) (r : ℕ) (hr : 0 < r) :
    ¬ IsRepeatedLinearNatural (ρ.comp (pResidual 2 G).subtype) F 3 r := by
  intro hm
  exact not_minimalParabolic_of_repeated_natural_three T (pResidual 2 G)
    (pResidual_sup_sylow_eq_top T) ρ F r hr hm hP

end CFSG.Quasithin.ChapterB
