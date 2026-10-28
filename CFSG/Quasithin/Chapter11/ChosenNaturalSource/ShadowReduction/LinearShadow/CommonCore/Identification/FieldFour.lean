module
public import Theory.Representation.BinarySylowFixedSpace
public import Theory.Representation.ElementaryPerfectSplit
public import Mathlib.LinearAlgebra.Projection
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction
public import Theory.SpecificGroups.PSL3Four.CentralCover.NonElementaryParabolic

/-!
# Sylow-invariant complements in the exceptional field-four cover

For the literal central covering map onto PSL₃(4), an abelian subgroup
mapping onto the affine translations and disjoint from the covering kernel
cannot be normalized by a Sylow two-subgroup unless the kernel is odd.
The proof averages a Sylow-invariant projection over the odd number of
Sylow cosets. Its globally invariant projection kills commutators, contrary
to the proved full commutator generation of the parabolic two-core.

For a two-group kernel, an abelian complement first makes the parabolic
core abelian. The non-elementary-cover theorem then forces the kernel to
have exponent two. For an arbitrary central kernel, passage to a quotient
with kernel of order two preserves the actual complement, Sylow subgroup,
and affine image. Thus odd central factors are retained. The last theorem
recovers the trivial two-core of the original quasisimple covering group.

These are the model obstruction and its original-cover applications needed
by the common-core identification. The chapter assembly still has to realize
its PV/V as the specified subgroup, with the literal parabolic image and
Sylow invariance. This module does not assert that remaining realization or
the complete p.774 result. Its owner is qt-d-1222-shadow-common-identification;
qt-d-1222-shadow-common-core retains the earlier-source final assembly.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
I.2.2(3), printed pp.409--410, and the first three paragraphs of p.774.
-/

public noncomputable section

open Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.FieldFour
variable {G M : Type*} [Group G] [Finite G]
    [AddCommGroup M] [Module (ZMod 2) M]

private theorem invariant_retraction
    (ρ : Representation (ZMod 2) G M) (S : Sylow 2 G)
    (Z : Submodule (ZMod 2) M) (hZ : ∀ g (z : Z), ρ g z = z)
    (π : M →ₗ[ZMod 2] Z) (hπ : ∀ z : Z, π z = z)
    (hS : ∀ (s : S) m, π (ρ s m) = π m) :
    ∃ f : M →ₗ[ZMod 2] Z, (∀ g m, f (ρ g m) = f m) ∧
      ∀ z : Z, f z = z := by
  let σ := Representation.linHom ρ (1 : Representation (ZMod 2) G Z)
  let U : Submodule (ZMod 2) (M →ₗ[ZMod 2] Z) := {
    carrier := {f | ∀ z : Z, f z = 0}
    zero_mem' := by intro z; rfl
    add_mem' := by intro f g hf hg z; simp only [LinearMap.add_apply, hf z, hg z, add_zero]
    smul_mem' := by intro a f hf z; simp only [LinearMap.smul_apply, hf z, smul_zero] }
  have hU (g : G) (f : M →ₗ[ZMod 2] Z) : σ g f - f ∈ U := by
    intro z
    change f (ρ g⁻¹ z) - f z = 0
    rw [hZ, sub_self]
  have hfixed : π ∈ fixedSpace σ S := by
    intro s
    apply LinearMap.ext
    intro m
    exact hS s⁻¹ m
  obtain ⟨f,hf,hmod⟩ := BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient
    σ S U hU π hfixed
  refine ⟨f, ?_, ?_⟩
  · intro g m
    have hh := LinearMap.congr_fun (hf g⁻¹) m
    change f (ρ (g⁻¹)⁻¹ m) = f m at hh
    simpa only [inv_inv] using hh
  · intro z
    have hh : π z - f z = 0 := hmod z
    exact (sub_eq_zero.mp hh).symm.trans (hπ z)


private theorem central_eq_bot_of_sylow_complement
    {G : Type*} [Group G] [Finite G]
    (R Z C : Subgroup G) [R.Normal] [IsElementaryAbelian 2 R]
    (S : Sylow 2 G) (hZR : Z ≤ R) (hCR : C ≤ R)
    (hZ : Z ≤ center G) (hdis : Disjoint Z C) (hgen : Z ⊔ C = R)
    (hS : (S : Subgroup G) ≤ normalizer (C : Set G))
    (hmoved : ⁅R, (⊤ : Subgroup G)⁆ = R) : Z = ⊥ := by
  let e : Subgroup R ≃o Submodule (ZMod 2) (Additive R) :=
    (AddSubgroup.toSubgroup' : AddSubgroup (Additive R) ≃o Subgroup R).symm.trans
      (AddSubgroup.toZModSubmodule 2)
  let U := e (Z.subgroupOf R)
  let W := e (C.subgroupOf R)
  have hc : IsCompl U W := by
    apply e.isCompl_iff.mp
    refine ⟨?_, codisjoint_iff.mpr ?_⟩
    · apply Subgroup.disjoint_def.mpr
      intro x hx hy
      exact Subtype.ext (Subgroup.disjoint_def.mp hdis hx hy)
    · rw [← subgroupOf_sup hZR hCR, hgen, subgroupOf_self]
  let α : G →* MulAut R := MulAut.conjNormal
  let ρ := elementaryRepresentation (p := 2) α
  have hU (g : G) (z : U) : ρ g z = z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change g * (z.val.toMul : G) * g⁻¹ = z.val.toMul
    have hz : (z.val.toMul : G) ∈ Z := z.property
    rw [mem_center_iff.mp (hZ hz) g, mul_inv_cancel_right]
  let π := U.projectionOnto W hc
  have hπS (s : S) (m : Additive R) : π (ρ s m) = π m := by
    have hm : m ∈ U ⊔ W := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨z,hz,w,hw,rfl⟩ := Submodule.mem_sup.mp hm
    have hsw : ρ s w ∈ W := by
      change (s : G) * (w.toMul : G) * (s : G)⁻¹ ∈ C
      exact (mem_normalizer_iff.mp (hS s.property) _).mp hw
    rw [map_add, map_add, map_add, hU s ⟨z,hz⟩,
      Submodule.projectionOnto_apply_of_mem_right hc hsw,
      Submodule.projectionOnto_apply_of_mem_right hc hw]
  obtain ⟨f,hf,hfid⟩ := invariant_retraction ρ S U hU π
    (Submodule.projectionOnto_apply_left hc) hπS
  let fG : R →* Multiplicative U := {
    toFun r := Multiplicative.ofAdd (f (Additive.ofMul r))
    map_one' := f.map_zero
    map_mul' r s := f.map_add (Additive.ofMul r) (Additive.ofMul s) }
  let N := fG.ker.map R.subtype
  have hcomm : ⁅R, (⊤ : Subgroup G)⁆ ≤ N := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro g _ r hr
    let v : R := ⟨r,hr⟩
    let c : R := α g v * v⁻¹
    refine ⟨c, ?_, rfl⟩
    change f (ρ g (Additive.ofMul v) + -Additive.ofMul v) = 0
    rw [map_add, map_neg, hf, add_neg_cancel]
  have hzero (v : Additive R) : f v = 0 := by
    have hv : (v.toMul : G) ∈ N := (hmoved ▸ hcomm) v.toMul.property
    obtain ⟨r,hr,he⟩ := hv
    have he' : r = v.toMul := Subtype.ext he
    subst r
    exact hr
  apply bot_unique
  intro z hz
  have he : (⟨Additive.ofMul ⟨z,hZR hz⟩,hz⟩ : U) = 0 :=
    (hfid _).symm.trans (hzero _)
  exact congrArg (fun x : U => (x.val.toMul : G)) he



open Matrix.PSL3Four Matrix.PSL3Four.ElementaryParabolic

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

theorem parabolic_kernel_eq_bot_of_sylow_invariant_complement
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hs : ∀ z ∈ f.ker, z ^ 2 = 1) (b : Bool)
    (S : Sylow 2 (liftedParabolic f b)) (C : Subgroup (liftedParabolic f b))
    (hC : C ≤ pCore 2 (liftedParabolic f b))
    (hd : Disjoint (parabolicAffine f b).ker C)
    (hgen : (parabolicAffine f b).ker ⊔ C = pCore 2 (liftedParabolic f b))
    (hn : (S : Subgroup (liftedParabolic f b)) ≤ normalizer (C : Set (liftedParabolic f b))) :
    f.ker = ⊥ := by
  have hk : IsPGroup 2 f.ker := fun z =>
    ⟨1, by simpa using Subtype.ext (hs z z.property)⟩
  have hpk : IsPGroup 2 (parabolicAffine f b).ker := by
    rw [parabolicAffine_ker]
    exact hk.comap_of_injective _ (liftedParabolic f b).subtype_injective
  have hkR : (parabolicAffine f b).ker ≤ pCore 2 (liftedParabolic f b) :=
    le_sSup ⟨inferInstance,hpk⟩
  have hcentral : (parabolicAffine f b).ker ≤ center (liftedParabolic f b) := by
    intro z hz
    rw [parabolicAffine_ker] at hz
    exact mem_center_iff.mpr (fun x => Subtype.ext (mem_center_iff.mp (hc hz) x))
  let := parabolicCore_elementary f hf hc hs b
  have hzero := central_eq_bot_of_sylow_complement _ _ C S hkR hC hcentral hd hgen hn
    (parabolicCore_commutator f hf hc hs b)
  apply bot_unique
  intro z hz
  have hzP : z ∈ liftedParabolic f b := by
    change f z ∈ Matrix.PSL3.RootPlaneGeometry.parabolic F b
    rw [MonoidHom.mem_ker.mp hz]
    exact one_mem _
  have hzK : (⟨z,hzP⟩ : liftedParabolic f b) ∈ (parabolicAffine f b).ker := by
    rw [parabolicAffine_ker]
    exact hz
  rw [hzero] at hzK
  exact congrArg Subtype.val hzK



/-- The literal affine image discharges the supplement and core containments.
The covering kernel may initially have exponent four. -/
theorem parabolic_kernel_eq_bot_of_abelian_image
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker) (b : Bool)
    (S : Sylow 2 (liftedParabolic f b)) (C : Subgroup (liftedParabolic f b))
    [IsMulCommutative C]
    (hd : Disjoint (parabolicAffine f b).ker C)
    (him : C.map (parabolicAffine f b) = Matrix.SL2.translations F)
    (hn : (S : Subgroup (liftedParabolic f b)) ≤ normalizer (C : Set (liftedParabolic f b))) :
    f.ker = ⊥ := by
  let a := parabolicAffine f b
  have hak : IsPGroup 2 a.ker := by
    rw [parabolicAffine_ker]
    exact hk.comap_of_injective _ (liftedParabolic f b).subtype_injective
  have hcentral : a.ker ≤ center (liftedParabolic f b) := by
    rw [parabolicAffine_ker]
    intro z hz
    exact mem_center_iff.mpr (fun x => Subtype.ext (mem_center_iff.mp (hc hz) x))
  have hcore : (Matrix.SL2.translations F).comap a = pCore 2 (liftedParabolic f b) := by
    rw [← Matrix.SL2.affine_twoCore_eq]
    exact a.comap_pCore_of_ker_isPGroup (parabolicAffine_surjective f hf b) hak
  have hgen : a.ker ⊔ C = pCore 2 (liftedParabolic f b) := by
    rw [sup_comm, ← comap_map_eq, him, hcore]
  let : IsMulCommutative (pCore 2 (liftedParabolic f b)) := by
    rw [← hgen]
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact hcentral.trans (center_le_centralizer _)
    · exact le_centralizer_iff.mpr
        (sup_le (hcentral.trans (center_le_centralizer _)) C.le_centralizer)
  have hs := Matrix.PSL3Four.NonElementaryKernel.kernel_pow_two_of_abelian_core f hf hc hk b
  exact parabolic_kernel_eq_bot_of_sylow_invariant_complement f hf hc hs b S C
    (le_sup_right.trans_eq hgen) hd hgen hn

/-- Application to the original quotient by the centre; no elementary-centre
or Frattini-triviality hypothesis is needed. -/
theorem source_center_eq_bot_of_abelian_image
    (e : (E ⧸ center E) ≃* PSL) (hz : IsPGroup 2 (center E)) (b : Bool)
    (S : Sylow 2 (liftedParabolic (centerProjection e) b))
    (C : Subgroup (liftedParabolic (centerProjection e) b)) [IsMulCommutative C]
    (hd : Disjoint (parabolicAffine (centerProjection e) b).ker C)
    (him : C.map (parabolicAffine (centerProjection e) b) = Matrix.SL2.translations F)
    (hn : (S : Subgroup (liftedParabolic (centerProjection e) b)) ≤
      normalizer (C : Set (liftedParabolic (centerProjection e) b))) : center E = ⊥ := by
  have hh := parabolic_kernel_eq_bot_of_abelian_image (centerProjection e)
    (centerProjection_surjective e) (centerProjection_ker e).le
    ((centerProjection_ker e).symm ▸ hz) b S C hd him hn
  rwa [centerProjection_ker] at hh



/-- The obstruction in the original ambient cover, with its actual Sylow and
subgroup. Restriction to the lifted parabolic preserves both normality and
the literal affine image. -/
theorem original_cover_kernel_eq_bot
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker) (b : Bool)
    (T : Sylow 2 E) (hT : (T : Subgroup E) ≤ liftedParabolic f b)
    (A : Subgroup E) [IsMulCommutative A] (hA : A ≤ liftedParabolic f b)
    (hd : Disjoint f.ker A)
    (him : (A.subgroupOf (liftedParabolic f b)).map (parabolicAffine f b) =
      Matrix.SL2.translations F)
    (hn : (T : Subgroup E) ≤ normalizer (A : Set E)) : f.ker = ⊥ := by
  let P := liftedParabolic f b
  let C := A.subgroupOf P
  let e := subgroupOfEquivOfLe hA
  let : IsMulCommutative C := ⟨⟨fun x y => e.injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  have hd' : Disjoint (parabolicAffine f b).ker C := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hy
    rw [parabolicAffine_ker] at hx
    exact Subtype.ext (Subgroup.disjoint_def.mp hd hx hy)
  have hn' : (T.subtype hT : Subgroup P) ≤ normalizer (C : Set P) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    change (t : E) * (x : E) * (t : E)⁻¹ ∈ A
    exact (mem_normalizer_iff.mp (hn ht) x).mp hx
  exact parabolic_kernel_eq_bot_of_abelian_image f hf hc hk b (T.subtype hT) C hd' him hn'



/-- Odd central factors are retained: the invariant complement rules out the
two-part of the covering kernel, rather than asserting that the kernel is trivial. -/
theorem parabolic_kernel_odd_of_abelian_image
    (f : E →* PSL) (hf : Function.Surjective f) (hc : f.ker ≤ center E) (b : Bool)
    (S : Sylow 2 (liftedParabolic f b)) (C : Subgroup (liftedParabolic f b))
    [IsMulCommutative C]
    (hd : Disjoint (parabolicAffine f b).ker C)
    (him : C.map (parabolicAffine f b) = Matrix.SL2.translations F)
    (hn : (S : Subgroup (liftedParabolic f b)) ≤ normalizer (C : Set (liftedParabolic f b))) :
    ¬ 2 ∣ Nat.card f.ker := by
  let c : PerfectCentralCovering.Cover E PSL := {
    toMonoidHom := f
    surjective := hf
    isPerfect := inferInstance
    ker_le_center := hc }
  intro htwo
  obtain ⟨N,hNn,hN,hcard⟩ := c.exists_prime_kernel_quotient htwo
  let : N.Normal := hNn
  let d := c.quotientKernelSubgroup N hN
  let g := d.toMonoidHom
  let q := QuotientGroup.mk' N
  let P := liftedParabolic f b
  let P' := liftedParabolic g b
  let r : P →* P' := (q.comp P.subtype).codRestrict P' (fun x => x.property)
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective N y.val
    have hp : x ∈ P := by
      change f x ∈ Matrix.PSL3.RootPlaneGeometry.parabolic F b
      have hh : g (q x) ∈ Matrix.PSL3.RootPlaneGeometry.parabolic F b := hx.symm ▸ y.property
      exact hh
    exact ⟨⟨x,hp⟩,Subtype.ext hx⟩
  have hfac : (parabolicAffine g b).comp r = parabolicAffine f b := by
    apply MonoidHom.ext
    intro x
    rfl
  have hd' : Disjoint (parabolicAffine g b).ker (C.map r) := by
    apply Subgroup.disjoint_def.mpr
    intro y hy hyC
    obtain ⟨x,hx,rfl⟩ := hyC
    have hxK : x ∈ (parabolicAffine f b).ker := by
      rw [← hfac]
      exact hy
    rw [Subgroup.disjoint_def.mp hd hxK hx,map_one]
  have him' : (C.map r).map (parabolicAffine g b) = Matrix.SL2.translations F := by
    rw [map_map,hfac,him]
  have hn' : (S.mapSurjective hr : Subgroup P') ≤ normalizer (C.map r : Set P') :=
    (map_mono hn).trans (C.le_normalizer_map r)
  let : Group.IsPerfect (E ⧸ N) := d.isPerfect
  have hk : IsPGroup 2 g.ker := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hz := parabolic_kernel_eq_bot_of_abelian_image g d.surjective d.ker_le_center hk b
    (S.mapSurjective hr) (C.map r) hd' him' hn'
  change Nat.card g.ker = 2 at hcard
  simp [hz] at hcard



/-- The actual central quotient has odd centre under the invariant-complement
hypotheses, with any odd central factors left in place. -/
theorem source_center_odd_of_abelian_image
    (e : (E ⧸ center E) ≃* PSL) (b : Bool)
    (S : Sylow 2 (liftedParabolic (centerProjection e) b))
    (C : Subgroup (liftedParabolic (centerProjection e) b)) [IsMulCommutative C]
    (hd : Disjoint (parabolicAffine (centerProjection e) b).ker C)
    (him : C.map (parabolicAffine (centerProjection e) b) = Matrix.SL2.translations F)
    (hn : (S : Subgroup (liftedParabolic (centerProjection e) b)) ≤
      normalizer (C : Set (liftedParabolic (centerProjection e) b))) :
    ¬ 2 ∣ Nat.card (center E) := by
  have hh := parabolic_kernel_odd_of_abelian_image (centerProjection e)
    (centerProjection_surjective e) (centerProjection_ker e).le b S C hd him hn
  rwa [centerProjection_ker] at hh

omit [Group.IsPerfect E] in
/-- The two-core of the original quasisimple cover vanishes; its odd centre
is not discarded. This is the covering-group conclusion needed on p.774. -/
theorem source_twoCore_eq_bot_of_abelian_image [Theory.GroupTheory.IsQuasisimple E]
    (e : (E ⧸ center E) ≃* PSL) (b : Bool)
    (S : Sylow 2 (liftedParabolic (centerProjection e) b))
    (C : Subgroup (liftedParabolic (centerProjection e) b)) [IsMulCommutative C]
    (hd : Disjoint (parabolicAffine (centerProjection e) b).ker C)
    (him : C.map (parabolicAffine (centerProjection e) b) = Matrix.SL2.translations F)
    (hn : (S : Subgroup (liftedParabolic (centerProjection e) b)) ≤
      normalizer (C : Set (liftedParabolic (centerProjection e) b))) : pCore 2 E = ⊥ := by
  have ho := source_center_odd_of_abelian_image e b S C hd him hn
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := E)).exists_card_eq
  have hd := card_dvd_of_le (Theory.GroupTheory.IsQuasisimple.pCore_le_center (G := E) 2)
  have hk0 : k = 0 := by
    by_contra hk0
    exact ho ((dvd_pow_self 2 hk0).trans (hk ▸ hd))
  exact (pCore 2 E).eq_bot_of_card_eq (by simpa [hk0] using hk)

omit [Group.IsPerfect E] in
/-- Recovery above the original normal two-subgroup, using its literal quotient.
Applied inside L with U = V.subgroupOf L, this removes the exceptional
covering two-core once the actual invariant complement has been supplied. -/
theorem source_core_recovery_of_abelian_image
    (U : Subgroup E) [U.Normal] (hU : IsPGroup 2 U)
    [Theory.GroupTheory.IsQuasisimple (E ⧸ U)]
    (e : ((E ⧸ U) ⧸ center (E ⧸ U)) ≃* PSL) (b : Bool)
    (S : Sylow 2 (liftedParabolic (centerProjection e) b))
    (C : Subgroup (liftedParabolic (centerProjection e) b)) [IsMulCommutative C]
    (hd : Disjoint (parabolicAffine (centerProjection e) b).ker C)
    (him : C.map (parabolicAffine (centerProjection e) b) = Matrix.SL2.translations F)
    (hn : (S : Subgroup (liftedParabolic (centerProjection e) b)) ≤
      normalizer (C : Set (liftedParabolic (centerProjection e) b))) : pCore 2 E = U := by
  have hquot := source_twoCore_eq_bot_of_abelian_image e b S C hd him hn
  have hk : IsPGroup 2 (QuotientGroup.mk' U).ker := by
    rwa [QuotientGroup.ker_mk']
  have hh := (QuotientGroup.mk' U).comap_pCore_of_ker_isPGroup
    (QuotientGroup.mk'_surjective U) hk
  rw [hquot, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hh
  exact hh.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.FieldFour
