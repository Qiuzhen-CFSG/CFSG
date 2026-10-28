module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.OriginalData
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.FixedImages
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# The residual kernel and the original marked involution

The two-core of the relatively normal residual is characteristic, so its
centralization of V propagates to the full normalizer span U. Consequently
restriction from U to E is faithful on the residual action image.

The original Pc marking makes every centralizer conjugate of τ lie in the
original Sylow subgroup. Its elementary action on V therefore kills τ² on
every seed conjugate and hence on U. On the four-group E, τ is nontrivial;
its fixed subgroup has order two and supplies the actual denominator line.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry.OriginalData
variable {G D : Type*} [Group G] [Group D] [Finite G]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]

omit [IsMulCommutative V] in
/-- The original residual two-core centralizes the full conjugate span. -/
theorem residual_core_centralizes_span (d : OriginalData Y T V M E Pc) :
    twoCoreAmbient (lineY Y E) ≤ centralizer (lineV V E : Set G) := by
  have hk := Orthogonal.lineY_twoCore d.action Y E d.Y_le d.line_le
    d.residual_image d.residual_kernel
  have hn : lineNormalizer E ≤ normalizer (twoCoreAmbient (lineY Y E) : Set G) :=
    d.residual_normal.trans
      (normalizer_le_normalizer_characteristic_image (lineY Y E) (pCore 2 (lineY Y E)))
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro _ ⟨c, hc, v, hv, rfl⟩ n hnmem
  have hn' : c⁻¹ * n * c ∈ twoCoreAmbient (lineY Y E) := by
    simpa only [inv_inv, SetLike.mem_coe] using
      (hn ((lineNormalizer E).inv_mem hc) n).mp hnmem
  have he := congrArg (MulAut.conj c) ((hk ▸ hn').2 v hv)
  change n * (c * v * c⁻¹) = (c * v * c⁻¹) * n
  simp only [map_mul, MulAut.conj_apply] at he
  convert he.symm using 1 <;> group

omit [IsMulCommutative V] in
/-- The residual kernel on E is its kernel on the entire original module. -/
theorem residual_centralizer_line_eq_span (d : OriginalData Y T V M E Pc) :
    lineY Y E ⊓ centralizer (E : Set G) =
      lineY Y E ⊓ centralizer (lineV V E : Set G) := by
  apply le_antisymm
  · intro y hy
    refine ⟨hy.1, d.residual_core_centralizes_span ?_⟩
    rw [Orthogonal.lineY_twoCore d.action Y E d.Y_le d.line_le
      d.residual_image d.residual_kernel]
    exact (Orthogonal.lineY_centralizer_line_eq_module d.action Y E d.Y_le
      d.line_le d.line_card d.singular d.residual_image).le hy
  · exact inf_le_inf_left _ (centralizer_le (d.line_le.trans (le_conjugateSpanBy V _)))

omit [Finite G] [IsMulCommutative V] in
/-- Every square from the original selected Sylow subgroup kills the seed. -/
theorem sylow_square_centralizes_seed (d : OriginalData Y T V M E Pc)
    (s : G) (hs : s ∈ lineT T E) : s ^ 2 ∈ centralizer (V : Set G) := by
  let a := V.normalizerMonoidHom.comp (inclusion (d.sylow_le_M.trans d.action.normalizes))
  let := d.sylow_action_elementary
  let s' : lineT T E := ⟨s, hs⟩
  have hsq : a (s' ^ 2) = 1 := by
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (A := a.range) (a s') ⟨s', rfl⟩
  intro v hv
  have he := congrArg (fun b : MulAut V => (b ⟨v, hv⟩ : G)) hsq
  change s ^ 2 * v * (s ^ 2)⁻¹ = v at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The original Pc marking propagates the square of τ to all of U. -/
theorem tau_square_centralizes_span (d : OriginalData Y T V M E Pc) :
    d.marked.tau ^ 2 ∈ centralizer (lineV V E : Set G) := by
  rw [d.inherited.2.2.2]
  suffices hh : conjugateSpanBy V (temporaryCentralizer T V E) ≤
      centralizer ({d.marked.tau ^ 2} : Set G) by
    intro u hu
    exact mem_centralizer_singleton_iff.mp (hh hu)
  apply (closure_le _).mpr
  rintro _ ⟨c, hc, v, hv, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have ht : c⁻¹ * d.marked.tau * c ∈ Pc := by
    simpa only [inv_inv, SetLike.mem_coe] using
      (d.Pc_normalized ((centralizer (E : Set G)).inv_mem hc.2) d.marked.tau).mp d.tau_mem_Pc
  have he := congrArg (MulAut.conj c)
    (d.sylow_square_centralizes_seed _ (d.Pc_le_sylow ht) v hv)
  simp only [map_mul, MulAut.conj_apply] at he
  convert he using 1 <;> simp only [pow_two] <;> group

open Representation.NormalElementaryQuotient
/-- The selected τ acts involutorily on the full intrinsic module. -/
theorem operator_involutory (d : OriginalData Y T V M E Pc)
    [((lineV V E).subgroupOf (temporaryLineNormalizer T V E)).Normal]
    [IsElementaryAbelian 2 ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))]
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E))) :
    representation _ f hf hker (f d.tau) * representation _ f hf hker (f d.tau) = 1 := by
  rw [← map_mul, ← map_mul]
  have hk : d.tau * d.tau ∈ f.ker := by
    rw [hker]
    intro u hu
    apply Subtype.ext
    change (u : G) * (d.marked.tau * d.marked.tau) = (d.marked.tau * d.marked.tau) * (u : G)
    simpa only [pow_two] using d.tau_square_centralizes_span (u : G) hu
  rw [MonoidHom.mem_ker.mp hk, map_one]

omit [IsMulCommutative V] in
/-- The actual denominator fixed subgroup has two elements. -/
theorem markedFixed_card (d : OriginalData Y T V M E Pc) :
    Nat.card (markedFixed E d.marked.tau) = 2 := by
  let a : MulAut E := E.normalizerMonoidHom ⟨d.marked.tau, d.marked.tau_mem.2⟩
  have ha : a ^ 2 = 1 := by
    apply MulEquiv.ext
    intro e
    apply Subtype.ext
    change d.marked.tau * (d.marked.tau * (e : G) * d.marked.tau⁻¹) *
      d.marked.tau⁻¹ = e
    have h := d.sylow_square_centralizes_seed d.marked.tau d.marked.tau_mem
      e (d.line_le e.property)
    calc
      _ = d.marked.tau ^ 2 * (e : G) * (d.marked.tau ^ 2)⁻¹ := by
        simp only [pow_two]; group
      _ = e := mul_inv_eq_iff_eq_mul.mpr h.symm
  have heq : a.fixedSubgroup.map E.subtype = markedFixed E d.marked.tau := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have h := congrArg Subtype.val (MulAut.mem_fixedSubgroup a x |>.mp hx)
      change d.marked.tau * (x : G) * d.marked.tau⁻¹ = x at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    · intro he
      refine ⟨⟨e, he.1⟩, ?_, rfl⟩
      apply (MulAut.mem_fixedSubgroup a _).mpr
      apply Subtype.ext
      change d.marked.tau * e * d.marked.tau⁻¹ = e
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp he.2).symm
  have hle : Nat.card a.fixedSubgroup ≤ 4 := by
    simpa only [d.line_card] using a.fixedSubgroup.card_le_card_group
  have hne : Nat.card a.fixedSubgroup ≠ 4 := by
    intro hc
    have ht : a.fixedSubgroup = ⊤ := a.fixedSubgroup.eq_top_of_card_eq (hc.trans d.line_card.symm)
    apply d.tau_outside
    refine ⟨d.marked.tau_mem.1, ?_⟩
    intro e he
    have hh : (⟨e, he⟩ : E) ∈ a.fixedSubgroup := ht ▸ mem_top _
    have hf := congrArg Subtype.val (MulAut.mem_fixedSubgroup a _ |>.mp hh)
    change d.marked.tau * e * d.marked.tau⁻¹ = e at hf
    exact (mul_inv_eq_iff_eq_mul.mp hf).symm
  have hp : 0 < Nat.card a.fixedSubgroup := Nat.card_pos
  have hmod := MulAut.fixedSubgroup_card_mod_two a ha
  rw [d.line_card] at hmod
  rw [← heq, card_map_of_injective E.subtype_injective]
  omega

/-- The intrinsic intersection is spanned by an actual nonzero vector of C_E(τ). -/
theorem exists_denominator_fixed_generator (d : OriginalData Y T V M E Pc)
    [IsElementaryAbelian 2 ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))] :
    ∃ z : Additive ((lineV V E).subgroupOf (temporaryLineNormalizer T V E)), z ≠ 0 ∧
      subspace ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))
        ((E.subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))) ⊓
      subspace ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))
        ((centralizer ({d.tau} : Set (temporaryLineNormalizer T V E))).subgroupOf
          ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))) =
        Submodule.span (ZMod 2) {z} := by
  let H := temporaryLineNormalizer T V E
  let U := (lineV V E).subgroupOf H
  let W := subspace U ((E.subgroupOf H).subgroupOf U) ⊓
    subspace U ((centralizer ({d.tau} : Set H)).subgroupOf U)
  obtain ⟨e, he, huniq⟩ := (Nat.card_eq_two_iff' (1 : markedFixed E d.marked.tau)).mp
    d.markedFixed_card
  have hEU : E ≤ lineV V E := d.line_le.trans (le_conjugateSpanBy V _)
  let u : U := ⟨⟨e, d.span_le_temporary (hEU e.property.1)⟩, hEU e.property.1⟩
  let z : Additive U := Additive.ofMul u
  have hz : z ≠ 0 := by
    intro h
    apply he
    exact Subtype.ext (congrArg (fun w : Additive U => ((w.toMul : H) : G)) h)
  have hzw : z ∈ W := by
    refine ⟨e.property.1, mem_centralizer_singleton_iff.mpr ?_⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp e.property.2)
  refine ⟨z, hz, le_antisymm ?_ (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzw))⟩
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]; exact Submodule.zero_mem _
  have hxf : (((x.toMul : H) : G)) ∈ markedFixed E d.marked.tau := by
    refine ⟨hx.1, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx.2)
  let x' : markedFixed E d.marked.tau := ⟨_, hxf⟩
  have hxne : x' ≠ 1 := by
    intro hh
    apply hx0
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : markedFixed E d.marked.tau => (x : G)) hh
  have hxz : x = z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : markedFixed E d.marked.tau => (x : G)) (huniq x' hxne)
  rw [hxz]
  exact Submodule.subset_span (Set.mem_singleton z)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry.OriginalData
