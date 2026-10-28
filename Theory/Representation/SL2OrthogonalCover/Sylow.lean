module
public import Theory.Representation.SL2OrthogonalCover.Universal
public import Theory.Representation.SL2NaturalFixedLifting
import Mathlib.Tactic.FinCases

/-!
# Orthogonal-cover geometry at arbitrary Sylow roots

Conjugation by the actual SL₂ matrices transports the explicit upper-root
calculation to every Sylow two-subgroup. The transport retains the quadratic
form, the fixed radical, individual displacement images, and the complete
commutator space. The unique singular point is characterized by all singular
vectors of the fixed plane.

For every central binary cover, the natural fixed-lifting theorem identifies
the literal preimage of the natural fixed line with the Sylow-fixed space.
The quotient comparison then proves all of I.2.3(3), without an F-vector-space
structure on the arbitrary cover.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.3(1a,b),(3),
printed p.413/PDF p.424.
-/

public section
noncomputable section
namespace Representation.SL2OrthogonalCover
open Matrix Matrix.SpecialLinearGroup Representation.OneCohomology
section Conjugation
variable {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]

private def actorEquiv (ρ : Representation k G W) (g : G) : W ≃ₗ[k] W where
  toLinearMap := ρ g
  invFun := ρ g⁻¹
  left_inv v := by
    change ρ g⁻¹ (ρ g v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    change ρ g (ρ g⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
private lemma actor_conj (ρ : Representation k G W) (g r : G) (v : W) :
    ρ ((MulAut.conj g) r) (ρ g v) = ρ g (ρ r v) := by
  simp only [MulAut.conj_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
private lemma map_fixed_conj (ρ : Representation k G W) (R : Subgroup G) (g : G) :
    (fixed (ρ.comp R.subtype)).map (ρ g) =
      fixed (ρ.comp (R.map (MulAut.conj g).toMonoidHom).subtype) := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩ r
    obtain ⟨s,hs,he⟩ := r.property
    change (MulAut.conj g) s = r.val at he
    change ρ r.val (ρ g w) = ρ g w
    rw [← he, actor_conj]
    exact congrArg (ρ g) (hw ⟨s,hs⟩)
  · intro hv
    obtain ⟨w,rfl⟩ := (actorEquiv ρ g).surjective v
    refine ⟨w, ?_, rfl⟩
    intro r
    apply (actorEquiv ρ g).injective
    change ρ g (ρ r.val w) = ρ g w
    rw [← actor_conj]
    exact hv ⟨(MulAut.conj g) r.val, Subgroup.mem_map_of_mem _ r.property⟩
private lemma map_commutator_conj (ρ : Representation k G W) (R : Subgroup G) (g : G) :
    (Coinvariants.ker (ρ.comp R.subtype)).map (ρ g) =
      Coinvariants.ker (ρ.comp (R.map (MulAut.conj g).toMonoidHom).subtype) := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨r,v⟩,rfl⟩
    change ρ g (ρ r.val v - v) ∈ Coinvariants.ker (ρ.comp (R.map (MulAut.conj g).toMonoidHom).subtype)
    rw [map_sub, ← actor_conj]
    exact Coinvariants.sub_mem_ker
      (ρ := ρ.comp (R.map (MulAut.conj g).toMonoidHom).subtype)
      ⟨(MulAut.conj g) r.val, Subgroup.mem_map_of_mem _ r.property⟩ (ρ g v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨r,v⟩,rfl⟩
    obtain ⟨s,hs,he⟩ := r.property
    change (MulAut.conj g) s = r.val at he
    obtain ⟨w,rfl⟩ := (actorEquiv ρ g).surjective v
    refine ⟨ρ s w - w, Coinvariants.sub_mem_ker (ρ := ρ.comp R.subtype) ⟨s,hs⟩ w, ?_⟩
    change ρ g (ρ s w - w) = ρ r.val (ρ g w) - ρ g w
    rw [map_sub, ← actor_conj, he]
private lemma map_moved_conj (ρ : Representation k G W) (g r : G) :
    (LinearMap.range (ρ r - LinearMap.id)).map (ρ g) =
      LinearMap.range (ρ ((MulAut.conj g) r) - LinearMap.id) := by
  ext v
  constructor
  · rintro ⟨_,⟨w,rfl⟩,rfl⟩
    refine ⟨ρ g w, ?_⟩
    change ρ ((MulAut.conj g) r) (ρ g w) - ρ g w = ρ g (ρ r w - w)
    rw [actor_conj, map_sub]
  · rintro ⟨w,rfl⟩
    obtain ⟨u,rfl⟩ := (actorEquiv ρ g).surjective w
    refine ⟨ρ r u - u, ⟨u,rfl⟩, ?_⟩
    change ρ g (ρ r u - u) = ρ ((MulAut.conj g) r) (ρ g u) - ρ g u
    rw [actor_conj, map_sub]
end Conjugation

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private lemma sylow_conjugate (S : Sylow 2 (SL F)) :
    ∃ g : SL F, (S : Subgroup (SL F)) =
      (upperUnipotent F).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL F) (upperUnipotentSylow F 2) S
  refine ⟨g, ?_⟩
  rw [← hg]
  rfl

private lemma radical_map (g : SL F) :
    ((form (F := F)).polarBilin.ker : Submodule F (Space F)).map ((action (F := F)) g) = (form (F := F)).polarBilin.ker := by
  rw [← fixed_radical]
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    rw [hw g]
    exact hw
  · intro hv
    exact ⟨v,hv,hv g⟩

/-- The fixed plane of every Sylow has a unique singular projective point,
and splits as that point plus the fixed radical. The last equivalence specifies
all singular vectors, so the point is unique, not merely a chosen complement. -/
lemma sylow_fixed_geometry (S : Sylow 2 (SL F)) :
    ∃ P : Submodule F (Space F), Module.finrank F P = 1 ∧
      fixed ((action (F := F)).comp S.toSubgroup.subtype) = P ⊔ (form (F := F)).polarBilin.ker ∧
      Disjoint P (form (F := F)).polarBilin.ker ∧
      ∀ v ∈ fixed ((action (F := F)).comp S.toSubgroup.subtype), (form (F := F)) v = 0 ↔ v ∈ P := by
  obtain ⟨g,hS⟩ := sylow_conjugate S
  let P := (singularPoint (F := F)).map ((action (F := F)) g)
  have hfixed : fixed ((action (F := F)).comp S.toSubgroup.subtype) = (fixedPlane (F := F)).map ((action (F := F)) g) := by
    rw [hS, ← map_fixed_conj, root_fixed]
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · exact (actorEquiv (action (F := F)) g).finrank_map_eq (singularPoint (F := F)) |>.trans singularPoint_dimension
  · rw [hfixed, fixedPlane_decomposition, Submodule.map_sup, radical_map]
  · have h := Submodule.disjoint_map (f := action (F := F) g) (actorEquiv (action (F := F)) g).injective
      (singularPoint_disjoint_radical (F := F))
    rwa [radical_map] at h
  · intro v hv
    rw [hfixed] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    rw [form_invariant, singular_in_fixedPlane w hw]
    constructor
    · intro h; exact ⟨w,h,rfl⟩
    · rintro ⟨u,hu,he⟩
      exact (actorEquiv (action (F := F)) g).injective he ▸ hu

/-- The literal displacement image for an arbitrary matrix. -/
@[expose] def movedSpace (r : SL F) : Submodule F (Space F) :=
  LinearMap.range ((action (F := F)) r - LinearMap.id)

omit [Finite F] [CharP F 2] in
private lemma root_parameter (g : SL F) (r : SL F)
    (hr : r ∈ (upperUnipotent F).map (MulAut.conj g).toMonoidHom) (hr1 : r ≠ 1) :
    ∃ t : F, t ≠ 0 ∧ r = (MulAut.conj g) (upper t) := by
  obtain ⟨s,hs,he⟩ := hr
  obtain ⟨t,ht⟩ := (mem_upperUnipotent F s).mp hs
  refine ⟨t, ?_, ?_⟩
  · intro hz
    subst t
    have hs1 : s = 1 := by simpa using ht.symm
    exact hr1 (by rw [← he, hs1]; exact map_one _)
  · rw [← ht] at he
    exact he.symm

/-- I.2.3(1b) for each nonidentity element of an arbitrary Sylow root. -/
lemma sylow_displacement_geometry (S : Sylow 2 (SL F)) (r : SL F)
    (hr : r ∈ S) (hr1 : r ≠ 1) :
    Module.finrank F (movedSpace r) = 1 ∧
      movedSpace r ≤ fixed ((action (F := F)).comp S.toSubgroup.subtype) ∧
      (∀ v ∈ movedSpace r, v ≠ 0 → (form (F := F)) v ≠ 0) ∧
      movedSpace r ≠ (form (F := F)).polarBilin.ker := by
  obtain ⟨g,hS⟩ := sylow_conjugate S
  have hr' : r ∈ (S : Subgroup (SL F)) := hr
  rw [hS] at hr'
  obtain ⟨t,ht,rfl⟩ := root_parameter g r hr' hr1
  have hm : movedSpace ((MulAut.conj g) (upper t)) = (rootDisplacement t).map ((action (F := F)) g) :=
    (map_moved_conj (action (F := F)) g (upper t)).symm
  have hf : fixed ((action (F := F)).comp S.toSubgroup.subtype) = (fixedPlane (F := F)).map ((action (F := F)) g) := by
    rw [hS, ← map_fixed_conj, root_fixed]
  rw [hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (actorEquiv (action (F := F)) g).finrank_map_eq (rootDisplacement t) |>.trans
      (rootDisplacement_dimension t ht)
  · rw [hf]
    exact Submodule.map_mono (rootDisplacement_le_plane t)
  · rintro v ⟨w,hw,rfl⟩ hne
    rw [form_invariant]
    exact rootDisplacement_nonsingular t ht w hw (fun hz => hne (by rw [hz,map_zero]))
  · intro he
    apply rootDisplacement_ne_radical t ht
    apply Submodule.map_injective_of_injective (actorEquiv (action (F := F)) g).injective
    exact he.trans (radical_map g).symm

/-- Distinct nonidentity elements of an arbitrary Sylow have disjoint
one-dimensional displacement images. -/
lemma sylow_displacements_disjoint (S : Sylow 2 (SL F)) (r s : SL F)
    (hr : r ∈ S) (hs : s ∈ S) (hr1 : r ≠ 1) (hs1 : s ≠ 1) (hrs : r ≠ s) :
    Disjoint (movedSpace r) (movedSpace s) := by
  obtain ⟨g,hS⟩ := sylow_conjugate S
  have hr' : r ∈ (S : Subgroup (SL F)) := hr
  have hs' : s ∈ (S : Subgroup (SL F)) := hs
  rw [hS] at hr' hs'
  obtain ⟨t,ht,hrt⟩ := root_parameter g r hr' hr1
  obtain ⟨u,hu,hsu⟩ := root_parameter g s hs' hs1
  have htu : t ≠ u := by intro h; apply hrs; rw [hrt,hsu,h]
  rw [hrt,hsu]
  change Disjoint (LinearMap.range _) (LinearMap.range _)
  rw [← map_moved_conj, ← map_moved_conj]
  exact Submodule.disjoint_map (actorEquiv (action (F := F)) g).injective (rootDisplacement_disjoint t u ht hu htu)

/-- The complete Sylow root commutator is its fixed plane. -/
lemma sylow_commutator (hF : 2 < Nat.card F) (S : Sylow 2 (SL F)) :
    Coinvariants.ker ((action (F := F)).comp S.toSubgroup.subtype) = fixed ((action (F := F)).comp S.toSubgroup.subtype) := by
  obtain ⟨g,hS⟩ := sylow_conjugate S
  rw [hS, ← map_commutator_conj, ← map_fixed_conj, root_commutator hF, root_fixed]


omit [Finite F] [CharP F 2] in
private lemma natural_root_fixed :
    fixed ((natural (F := F)).comp (upperUnipotent F).subtype) = Submodule.span F {![1,0]} := by
  ext v
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hv
    have h := congrFun (hv ⟨upper 1, (mem_upperUnipotent F _).mpr ⟨1,rfl⟩⟩) 0
    have hv1 : v 1 = 0 := by
      simpa [natural, specialLinearNatural_apply, upper, transvection_coe,
        mulVec, dotProduct, Fin.sum_univ_two] using h
    refine ⟨v 0, ?_⟩
    ext i; fin_cases i <;> simp [hv1]
  · rintro ⟨c,rfl⟩ g
    obtain ⟨t,ht⟩ := (mem_upperUnipotent F g.val).mp g.property
    change (natural (F := F)) g.val (c • ![1,0]) = c • ![1,0]
    rw [← ht]
    ext i; fin_cases i <;> simp [natural, specialLinearNatural_apply, transvection_coe,
      mulVec, dotProduct, Fin.sum_univ_two]

/-- The line used in arbitrary-Sylow statements is the actual fixed F-line
of the natural module, and it has field dimension one. -/
lemma natural_sylow_fixed_dimension (S : Sylow 2 (SL F)) :
    Module.finrank F (fixed ((natural (F := F)).comp S.toSubgroup.subtype)) = 1 := by
  obtain ⟨g,hS⟩ := sylow_conjugate S
  rw [hS, ← map_fixed_conj, natural_root_fixed]
  exact (actorEquiv (natural (F := F)) g).finrank_map_eq _ |>.trans (finrank_span_singleton (by simp))

section BinarySylow
variable [Algebra (ZMod 2) F]

omit [Finite F] in
/-- The preimage of the natural fixed line is the fixed space in every central
binary cover. This uses the genuine fixed-lifting theorem, with the same map. -/
lemma cover_sylow_preimage {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (SL F) W}
    (p : σ.IntertwiningMap (binaryNatural (F := F))) (hp : IsCover p) (S : Sylow 2 (SL F)) :
    (fixed ((binaryNatural (F := F)).comp S.toSubgroup.subtype)).comap p.toLinearMap = fixed (σ.comp S.toSubgroup.subtype) := by
  ext v
  constructor
  · intro hv r
    apply Representation.SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel σ
      p.toLinearMap.toAddMonoidHom hp.1
      (fun g w => by
        change p (σ g w) = (binaryNatural (F := F)) g (p w)
        exact LinearMap.congr_fun (p.isIntertwining' g) w) (fun w hw g => hp.2.1 hw g) r.val v
    change p (σ r.val v) = p v
    rw [p.isIntertwining]
    exact hv r
  · intro hv r
    change (binaryNatural (F := F)) r.val (p v) = p v
    rw [← p.isIntertwining]
    exact congrArg p (hv r)

/-- Full I.2.3(3) for an arbitrary Sylow root and an arbitrary binary cover. -/
lemma cover_sylow_geometry (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (SL F) W}
    (p : σ.IntertwiningMap (binaryNatural (F := F))) (hp : IsCover p) (S : Sylow 2 (SL F)) :
    let V₁ := (fixed ((binaryNatural (F := F)).comp S.toSubgroup.subtype)).comap p.toLinearMap
    fixed σ ≤ V₁ ∧ V₁ = Coinvariants.ker (σ.comp S.toSubgroup.subtype) ∧ V₁ ≤ fixed (σ.comp S.toSubgroup.subtype) := by
  have hcard := card_gt_two n hn hF
  have hmodel := binaryProjection_isCover (F := F) hcard
  have hcomm : (fixed ((binaryNatural (F := F)).comp S.toSubgroup.subtype)).comap (binaryProjection (F := F)).toLinearMap =
      Coinvariants.ker ((binaryAction (F := F)).comp S.toSubgroup.subtype) := by
    rw [cover_sylow_preimage (binaryProjection (F := F)) hmodel S]
    change (fixed ((action (F := F)).comp S.toSubgroup.subtype)).restrictScalars (ZMod 2) =
      Coinvariants.ker (restrictScalars ((action (F := F)).comp S.toSubgroup.subtype))
    rw [coinvariants_restrictScalars, sylow_commutator hcard S]
  have hcentral : (fixed ((binaryNatural (F := F)).comp S.toSubgroup.subtype)).comap (binaryProjection (F := F)).toLinearMap ≤
      fixed ((binaryAction (F := F)).comp S.toSubgroup.subtype) := (cover_sylow_preimage (binaryProjection (F := F)) hmodel S).le
  have hd : Module.finrank (ZMod 2) (binaryProjection (F := F)).toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 (binaryNatural (F := F)).dual) := by
    rw [binary_kernel_finrank n hF, binary_dual_H1_finrank n hn hF]
  obtain ⟨f,hf,hover⟩ := exists_quotient_of_finrank_ker_eq (k := ZMod 2)
    (ρ := binaryNatural (F := F)) (σ := binaryAction (F := F)) (binaryProjection (F := F)) hmodel hd p hp
  refine ⟨fixed_le_preimage p _ (fun v hv s => hv s.val), ?_⟩
  exact preimage_root_geometry_of_surjective (binaryProjection (F := F)) p f hf hover
    (S : Subgroup (SL F)) (fixed ((binaryNatural (F := F)).comp S.toSubgroup.subtype)) hcomm hcentral
end BinarySylow

end Representation.SL2OrthogonalCover
