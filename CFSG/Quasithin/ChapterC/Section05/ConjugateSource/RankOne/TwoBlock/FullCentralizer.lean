module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.MarkedNormalizer

/-!
# The full R-centralizer in a genuine natural cover

Every natural root-line vector lifts to U∩Uˣ. An R-element centralizing Uˣ
therefore fixes that whole line. Semilinearity and its two-power order force
an upper-root action, supplied by the actual Uˣ-image. Subtracting that actor
leaves the full U-centralizer, by the proved cover-kernel theorem.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/
public section
open Subgroup Matrix.SpecialLinearGroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G}
variable {E F : Type*} [Field E] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite G] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem root_apply (d : FullNaturalModel R K F) (t : Multiplicative F)
    (w : Multiplicative (Fin 2 → F)) :
    (d.tau (upperUnipotentHom F t) w).toAdd = ![w.toAdd 0 + t.toAdd * w.toAdd 1,w.toAdd 1] := by
  rw [d.natural]
  ext i
  fin_cases i <;> simp [upperUnipotentHom,transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

omit [Finite G] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem fixed_lift (h : Setup R K E) (d : FullNaturalModel R K F)
    (s : S R) (u : U K)
    (he : d.projection (moduleConjugate h.coordinates.normalizes s u) = d.projection u) :
    moduleConjugate h.coordinates.normalizes s u = u := by
  apply h.fixedLift
  have hc : (moduleConjugate h.coordinates.normalizes s u / u : U K) ∈ d.projection.ker := by
    change d.projection _ = 1
    rw [map_div,he,div_self']
  have hk := (d.kernel _).mp hc
  have hq := (h.coordinates.projection_kernel _).mpr hk
  rw [map_div,div_eq_one] at hq
  exact hq

omit [Finite F] in
/-- The full natural action supplies the actual root actor rather than an
assumed centralizer product. The normalizer premise is discharged by the
source block-orbit stabilizer in the two-block application. -/
theorem Setup.full_centralizer_le_conjugate_sup
    (h : Setup R K E) (d : FullNaturalModel R K F) (hR : IsPGroup 2 R)
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hNK : R ⊓ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤ normalizer (K : Set G)) :
    R ⊓ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤
      (U K).map (MulAut.conj x⁻¹).toMonoidHom ⊔ (R ⊓ centralizer (U K : Set G)) := by
  let N := normalizer (K : Set G)
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  have hVS : V ≤ S R := h.conjugate_le hx
  have hVN : V ≤ N := hVS.trans d.normalizes
  have hp := h.factorization hx hnc
  have hQN : Q R K ≤ N := (h.core ▸ inf_le_left).trans d.normalizes
  have hQimage : ((Q R K).subgroupOf N).map d.action = ⊥ := by
    apply (map_eq_bot_iff ((Q R K).subgroupOf N)).mpr
    rw [d.action_kernel]
    exact subgroupOf_mono _ (h.core ▸ inf_le_right)
  have hVi : (V.subgroupOf N).map d.action = (upperUnipotent F).map d.tau := by
    have hh := d.image
    rw [hp.span,subgroupOf_sup hVN hQN,Subgroup.map_sup,hQimage,sup_bot_eq] at hh
    exact hh
  have hline (c : F) : ∃ u : U K, d.projection u = Multiplicative.ofAdd ![c,0] ∧ (u : G) ∈ V := by
    obtain ⟨u,hu⟩ := d.surjective (Multiplicative.ofAdd ![c,0])
    refine ⟨u,hu,?_⟩
    have huS : (u : G) ∈ centralizer (S R : Set G) := by
      intro s hs
      let s₀ : S R := ⟨s,hs⟩
      let sN : N := inclusion d.normalizes s₀
      have hm : d.action sN ∈ (upperUnipotent F).map d.tau := d.image ▸ mem_map_of_mem d.action hs
      obtain ⟨g,⟨t,rfl⟩,he⟩ := hm
      have hfix : d.projection (moduleConjugate h.coordinates.normalizes s₀ u) = d.projection u := by
        have hh := d.equivariant sN u
        change d.action sN (d.projection u) = d.projection (moduleConjugate h.coordinates.normalizes s₀ u) at hh
        rw [← hh,← he,hu]
        apply Multiplicative.toAdd.injective
        rw [root_apply]
        simp
      have hh := congrArg Subtype.val (fixed_lift h d s₀ u hfix)
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hh : (u : G) ∈ U K ⊓ centralizer (V : Set G) := ⟨u.property,centralizer_le hVS huS⟩
    rw [← (h.commutator_eq_fixed hx hnc).1,(h.commutator_eq_fixed hx hnc).2] at hh
    exact hh.2
  rintro a ⟨haR,haV⟩
  let aN : N := ⟨a,hNK ⟨haR,haV⟩⟩
  let π := (automorphismRepresentation d.action.range).comp d.action.rangeRestrict
  have hfix (c : F) : π aN ![c,0] = ![c,0] := by
    obtain ⟨u,hu,huV⟩ := hline c
    have he : normalizerConjugate aN u = u := by
      apply Subtype.ext
      change a * (u : G) * a⁻¹ = u
      rw [← haV (u : G) huV,mul_inv_cancel_right]
    change (d.action aN (Multiplicative.ofAdd ![c,0])).toAdd = _
    rw [← hu,d.equivariant,he,hu]
    rfl
  obtain ⟨n,hn⟩ := hR.exists_pow_pow_eq_one (⟨a,haR⟩ : R)
  have hnN : aN ^ (2 ^ n) = 1 := by
    apply Subtype.ext
    exact congrArg (fun r : R => (r : G)) hn
  obtain ⟨t,ht⟩ := natural_fixed_line_two_element π aN (d.semilinear aN) hfix n hnN
  have he : d.action aN = d.tau (upperUnipotentHom F (Multiplicative.ofAdd t)) := by
    apply MulEquiv.ext
    intro w
    apply Multiplicative.toAdd.injective
    exact (ht w.toAdd).trans (root_apply d (Multiplicative.ofAdd t) w).symm
  have hm : d.action aN ∈ (V.subgroupOf N).map d.action := by
    rw [hVi,he]
    exact mem_map_of_mem d.tau ⟨Multiplicative.ofAdd t,rfl⟩
  obtain ⟨v,hv,he⟩ := hm
  have hc : v⁻¹ * aN ∈ d.action.ker := by
    change d.action (v⁻¹ * aN) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hcU : (v : G)⁻¹ * a ∈ centralizer (U K : Set G) := by
    have hh : v⁻¹ * aN ∈ (centralizer (U K : Set G)).subgroupOf N := d.action_kernel ▸ hc
    exact hh
  have hcR : (v : G)⁻¹ * a ∈ R := R.mul_mem (R.inv_mem (hVS.trans inf_le_left hv)) haR
  have hh : (v : G) * ((v : G)⁻¹ * a) ∈ V ⊔ (R ⊓ centralizer (U K : Set G)) :=
    mul_mem_sup hv ⟨hcR,hcU⟩
  simpa only [mul_inv_cancel_left] using hh
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
