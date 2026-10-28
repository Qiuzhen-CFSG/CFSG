module

public import Theory.Representation.SL2NaturalOffenders.PointwiseFixer
public import Theory.Representation.SL2NaturalOffenders.NaturalPair

/-!
# Pointwise fixers of two natural SL₂ modules

The additive centralizer of the two independent natural factors consists of
independent field scalars. A normalizer fixing the two Sylow fixed lines
pointwise also fixes every scalar endomorphism under conjugation. It is
therefore linear on each coordinate. A two-element has determinant one on
each coordinate, so faithfulness puts it in the literal product layer.

The argument includes the field with two elements and does not assume that
an ambient element preserves the coordinate factors.
Source: Aschbacher–Smith B.2.20 and B.6.10, printed pp.82 and117.
-/

public section
open Matrix.SpecialLinearGroup Representation.BinaryOffender
namespace Representation.SL2NaturalOffenders
variable {F : Type*} [Field F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "V" => Fin 2 → F

theorem natural_fixed_all_eq_zero (v : V)
    (hv : ∀ g : D, g.val.mulVec v = v) : v = 0 := by
  have h₀ := congrFun (hv (transvection (i := 0) (j := 1) zero_ne_one (1 : F))) 0
  have h₁ := congrFun (hv (transvection (i := 1) (j := 0) one_ne_zero (1 : F))) 1
  simp [transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₀ h₁
  ext i
  fin_cases i
  · simpa using h₁
  · simpa using h₀

theorem centralizer_pair_scalars (f : (V × V) →+ (V × V))
    (hf : ∀ (g h : D) (v w : V),
      f (g.val.mulVec v, h.val.mulVec w) =
        (g.val.mulVec (f (v,w)).1, h.val.mulVec (f (v,w)).2)) :
    ∃ c d : F, ∀ v w, f (v,w) = (c • v,d • w) := by
  let f₁ : V →+ V :=
    { toFun := fun v => (f (v,0)).1
      map_zero' := by change (f 0).1 = 0; rw [map_zero]; rfl
      map_add' := by intro v w; simpa using congrArg Prod.fst (f.map_add (v,0) (w,0)) }
  let f₂ : V →+ V :=
    { toFun := fun v => (f (0,v)).2
      map_zero' := by change (f 0).2 = 0; rw [map_zero]; rfl
      map_add' := by intro v w; simpa using congrArg Prod.snd (f.map_add (0,v) (0,w)) }
  obtain ⟨c,hc⟩ := centralizer_scalar f₁ (fun g v => by
    simpa [f₁] using congrArg Prod.fst (hf g 1 v 0))
  obtain ⟨d,hd⟩ := centralizer_scalar f₂ (fun g v => by
    simpa [f₂] using congrArg Prod.snd (hf 1 g 0 v))
  have hz₁ (v : V) : (f (v,0)).2 = 0 := by
    apply natural_fixed_all_eq_zero
    intro g
    simpa using (congrArg Prod.snd (hf 1 g v 0)).symm
  have hz₂ (w : V) : (f (0,w)).1 = 0 := by
    apply natural_fixed_all_eq_zero
    intro g
    simpa using (congrArg Prod.fst (hf g 1 0 w)).symm
  refine ⟨c,d,fun v w => ?_⟩
  have hs : f (v,w) = f (v,0) + f (0,w) := by simpa using f.map_add (v,0) (0,w)
  apply Prod.ext
  · simpa [hz₂] using (congrArg Prod.fst hs).trans (by simpa [f₁, hz₂] using hc v)
  · simpa [hz₁] using (congrArg Prod.snd hs).trans (by simpa [f₂, hz₁] using hd w)


variable [Algebra (ZMod 2) F] {H : Type*} [Group H]

theorem conjugate_pair_scalars (L : Subgroup H) [L.Normal]
    (e : L ≃* D × D) (ρ : Representation (ZMod 2) H (V × V))
    (hnat : ∀ (g : L) (v w : V), ρ (g : H) (v,w) =
      ((e g).1.val.mulVec v,(e g).2.val.mulVec w))
    (a : H) (c d : F) :
    ∃ c' d' : F, ∀ v : V × V,
      ρ a (c • (ρ a⁻¹ v).1,d • (ρ a⁻¹ v).2) = (c' • v.1,d' • v.2) := by
  let f : (V × V) →+ (V × V) :=
    { toFun := fun v => ρ a (c • (ρ a⁻¹ v).1,d • (ρ a⁻¹ v).2)
      map_zero' := by simp only [map_zero, Prod.fst_zero, Prod.snd_zero, smul_zero]; exact (ρ a).map_zero
      map_add' := by
        intro v w
        simp only [map_add, Prod.fst_add, Prod.snd_add, smul_add]
        exact (ρ a).map_add (c • (ρ a⁻¹ v).1,d • (ρ a⁻¹ v).2) (c • (ρ a⁻¹ w).1,d • (ρ a⁻¹ w).2) }
  obtain ⟨c',d',hd⟩ := centralizer_pair_scalars f (by
    intro g h v w
    let x : L := e.symm (g,h)
    let y : L := ⟨a⁻¹ * (x : H) * a,
      (inferInstance : L.Normal).conj_mem' x x.property a⟩
    have hx (v w : V) : (g.val.mulVec v,h.val.mulVec w) = ρ (x : H) (v,w) := by
      rw [hnat]
      simp [x]
    have hy (v : V × V) : ρ (y : H) (c • v.1,d • v.2) =
        (c • (ρ (y : H) v).1,d • (ρ (y : H) v).2) := by
      simp only [hnat, Matrix.mulVec_smul]
    have hy₁ (v : V × V) : ρ a⁻¹ (ρ (x : H) v) = ρ (y : H) (ρ a⁻¹ v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel, mul_one]
    have hy₂ (v : V × V) : ρ a (ρ (y : H) v) = ρ (x : H) (ρ a v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel_left]
    change ρ a (c • (ρ a⁻¹ (g.val.mulVec v,h.val.mulVec w)).1,
      d • (ρ a⁻¹ (g.val.mulVec v,h.val.mulVec w)).2) =
      (g.val.mulVec (f (v,w)).1,h.val.mulVec (f (v,w)).2)
    rw [hx, hx, hy₁, ← hy, hy₂]
    rfl)
  exact ⟨c',d',fun v => hd v.1 v.2⟩

theorem pair_linear_of_fixed_axes (L : Subgroup H) [L.Normal]
    (e : L ≃* D × D) (ρ : Representation (ZMod 2) H (V × V))
    (hnat : ∀ (g : L) (v w : V), ρ (g : H) (v,w) =
      ((e g).1.val.mulVec v,(e g).2.val.mulVec w))
    (a : H) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0)
    (hfix₁ : ∀ c : F, ρ a (c • v,0) = (c • v,0))
    (hfix₂ : ∀ c : F, ρ a (0,c • w) = (0,c • w)) :
    ∀ (c d : F) (x : V × V),
      ρ a (c • x.1,d • x.2) = (c • (ρ a x).1,d • (ρ a x).2) := by
  intro c d x
  obtain ⟨c',d',hs⟩ := conjugate_pair_scalars L e ρ hnat a c d
  have hcancel (x : V × V) : ρ a⁻¹ (ρ a x) = x := by
    simp [← Module.End.mul_apply, ← map_mul]
  have hi₁ : ρ a⁻¹ (v,0) = (v,0) := by
    have hh := hcancel (v,0)
    simpa only [show ρ a (v,0) = (v,0) by simpa using hfix₁ 1] using hh
  have hi₂ : ρ a⁻¹ (0,w) = (0,w) := by
    have hh := hcancel (0,w)
    simpa only [show ρ a (0,w) = (0,w) by simpa using hfix₂ 1] using hh
  have hc : c' = c := by
    apply smul_left_injective F hv
    have hh := congrArg Prod.fst (hs (v,0))
    simpa only [hi₁,smul_zero,hfix₁] using hh.symm
  have hd : d' = d := by
    apply smul_left_injective F hw
    have hh := congrArg Prod.snd (hs (0,w))
    simpa only [hi₂,smul_zero,hfix₂] using hh.symm
  simpa only [hcancel,hc,hd] using hs (ρ a x)



theorem mem_pair_layer_of_linear_two_power_one (L : Subgroup H)
    (e : L ≃* D × D) (ρ : Representation (ZMod 2) H (V × V))
    (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v w : V), ρ (g : H) (v,w) =
      ((e g).1.val.mulVec v,(e g).2.val.mulVec w))
    {a : H} (ha : ∃ n : ℕ, a ^ (2 ^ n) = 1)
    (hlin : ∀ (c d : F) (x : V × V),
      ρ a (c • x.1,d • x.2) = (c • (ρ a x).1,d • (ρ a x).2)) : a ∈ L := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have hx (v w : V) : ρ a (v,0) = ((ρ a (v,w)).1,0) := by simpa using hlin 1 0 (v,w)
  have hy (v w : V) : ρ a (0,w) = (0,(ρ a (v,w)).2) := by simpa using hlin 0 1 (v,w)
  let T₁ : Module.End F V :=
    { toFun := fun v => (ρ a (v,0)).1
      map_add' := by intro v w; simpa using congrArg Prod.fst ((ρ a).map_add (v,0) (w,0))
      map_smul' := by intro c v; simpa using congrArg Prod.fst (hlin c 0 (v,0)) }
  let T₂ : Module.End F V :=
    { toFun := fun w => (ρ a (0,w)).2
      map_add' := by intro v w; simpa using congrArg Prod.snd ((ρ a).map_add (0,v) (0,w))
      map_smul' := by intro c v; simpa using congrArg Prod.snd (hlin 0 c (0,v)) }
  have hsplit (v w : V) : ρ a (v,w) = (T₁ v,T₂ w) := by
    apply Prod.ext
    · exact (congrArg Prod.fst (hx v w)).symm
    · exact (congrArg Prod.snd (hy v w)).symm
  have hpow (n : ℕ) (v w : V) : ρ (a ^ n) (v,w) = ((T₁ ^ n) v,(T₂ ^ n) w) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',map_mul]
      change ρ a (ρ (a ^ n) (v,w)) = _
      rw [ih,hsplit,pow_succ',pow_succ']
      rfl
  obtain ⟨n,hn⟩ := ha
  have hT₁ : T₁ ^ (2 ^ n) = 1 := by
    apply LinearMap.ext
    intro v
    have hh := congrArg Prod.fst (hpow (2 ^ n) v 0)
    simpa [hn] using hh.symm
  have hT₂ : T₂ ^ (2 ^ n) = 1 := by
    apply LinearMap.ext
    intro v
    have hh := congrArg Prod.snd (hpow (2 ^ n) 0 v)
    simpa [hn] using hh.symm
  have hdet (T : Module.End F V) (hT : T ^ (2 ^ n) = 1) :
      (LinearMap.toMatrix' T).det = 1 := by
    have hM : (LinearMap.toMatrix' T) ^ (2 ^ n) = 1 := by
      change (LinearMap.toMatrixAlgEquiv' T) ^ (2 ^ n) = 1
      rw [← map_pow,hT,map_one]
    have hd : (LinearMap.toMatrix' T).det ^ (2 ^ n) = 1 := by
      simpa only [Matrix.det_pow,Matrix.det_one] using congrArg Matrix.det hM
    simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 n 1 _).mp (by simpa using hd)
  let g : D := ⟨LinearMap.toMatrix' T₁,hdet T₁ hT₁⟩
  let h : D := ⟨LinearMap.toMatrix' T₂,hdet T₂ hT₂⟩
  have heq : ρ ((e.symm (g,h) : L) : H) = ρ a := by
    apply LinearMap.ext
    intro x
    rw [hnat,e.apply_symm_apply,hsplit]
    exact Prod.ext (LinearMap.toMatrix'_mulVec T₁ x.1) (LinearMap.toMatrix'_mulVec T₂ x.2)
  exact hfaith heq ▸ (e.symm (g,h)).property



variable [Finite F]

private theorem sylow_fixed_vector (P : Sylow 2 D) :
    ∃ v : V, v ≠ 0 ∧ ∀ g ∈ (P : Subgroup D), g.val.mulVec v = v := by
  let P' : Sylow 2 (⊤ : Subgroup D) :=
    P.mapSurjective (f := (Subgroup.topEquiv (G := D)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := D)).symm.surjective
  have hP : (P' : Subgroup (⊤ : Subgroup D)).map (⊤ : Subgroup D).subtype = P := by
    ext g
    simp [P']
  have hd := Ratios.sylowImage_fixedCodim (⊤ : Subgroup D) Subgroup.topEquiv
    (NoStrong.natural (F := F)) (fun _ _ => rfl) P'
  rw [hP] at hd
  have ht := fixedCodim_add_finrank (NoStrong.natural (F := F)) (P : Subgroup D)
  have hfull : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) F := by
    simp [Module.finrank_pi_fintype,two_mul]
  have hp : 0 < Module.finrank (ZMod 2) F := Module.finrank_pos
  have hpfix : 0 < Module.finrank (ZMod 2) (fixedSpace (NoStrong.natural (F := F)) (P : Subgroup D)) := by omega
  obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpfix
  exact ⟨v,fun h => hv (Subtype.ext h),fun g hg => v.property ⟨g,hg⟩⟩

/-- Literal two-factor fixed-space centralizer, with both factors marked. -/
theorem mem_pair_layer_of_fixedSpace (L : Subgroup H) [L.Normal]
    (e : L ≃* D × D) (ρ : Representation (ZMod 2) H (V × V))
    (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v w : V), ρ (g : H) (v,w) =
      ((e g).1.val.mulVec v,(e g).2.val.mulVec w))
    (P Q : Sylow 2 D) {a : H} (ha : ∃ n : ℕ, a ^ (2 ^ n) = 1)
    (hfix : ∀ v ∈ fixedSpace ρ
      (((P : Subgroup D).prod Q).map (L.subtype.comp e.symm.toMonoidHom)), ρ a v = v) :
    a ∈ L := by
  obtain ⟨v,hv,hPv⟩ := sylow_fixed_vector P
  obtain ⟨w,hw,hQw⟩ := sylow_fixed_vector Q
  apply mem_pair_layer_of_linear_two_power_one L e ρ hfaith hnat ha
  apply pair_linear_of_fixed_axes L e ρ hnat a v w hv hw
  · intro c
    apply hfix
    rintro ⟨_,g,hg,rfl⟩
    change ρ ((e.symm g : L) : H) (c • v,0) = (c • v,0)
    rw [hnat,e.apply_symm_apply,Matrix.mulVec_smul,hPv _ hg.1,Matrix.mulVec_zero]
  · intro c
    apply hfix
    rintro ⟨_,g,hg,rfl⟩
    change ρ ((e.symm g : L) : H) (0,c • w) = (0,c • w)
    rw [hnat,e.apply_symm_apply,Matrix.mulVec_smul,hQw _ hg.2,Matrix.mulVec_zero]
end Representation.SL2NaturalOffenders
