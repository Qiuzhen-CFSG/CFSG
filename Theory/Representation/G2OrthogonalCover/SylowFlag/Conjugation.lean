module

public import Theory.Representation.G2OrthogonalCover.SylowFlag.Uniqueness

/-!
# Conjugating the marked G₂′ cover geometry to every Sylow

Actual conjugation in the derived group transports the Sylow and long-root
subgroups. The paired seven- and six-dimensional linear maps transport the
point and natural flag and commute with the original projection mk. Fixed
spaces, displacement spaces, dimensions, singularity, and radical complements
therefore transport together. Sylow conjugacy supplies this marking for every
Sylow; invariant-space uniqueness identifies every selected flag.

Source: Aschbacher–Smith, I.2.3(1)(a),(c), printed p.413 / PDF p.424.
-/

@[expose] public section
noncomputable section

open Atlas.SplitOctonion Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover.SylowFlag
variable (F : Type*) [Field F] [CharP F 2]

namespace Transport
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Conjugation of an actual subgroup, with its original embedding. -/
def conjugate (g : G) (T : Subgroup G) : Subgroup G :=
  T.map (MulAut.conj g).toMonoidHom

/-- The linear equivalence supplied by an actual group element. -/
def linear (ρ : Representation k G V) (g : G) : V ≃ₗ[k] V :=
  { ρ g with
    invFun := ρ g⁻¹
    left_inv := ρ.inv_self_apply g
    right_inv := ρ.self_inv_apply g }

theorem conjugate_action (ρ : Representation k G V) (g h : G) (x : V) :
    ρ ((MulAut.conj g) h) (ρ g x) = ρ g (ρ h x) := by
  simp [MulAut.conj_apply, map_mul, Module.End.mul_apply]

theorem fixed_conjugate (ρ : Representation k G V) (g : G) (T : Subgroup G) :
    fixed (ρ.comp (conjugate g T).subtype) = (fixed (ρ.comp T.subtype)).map (ρ g) := by
  apply le_antisymm
  · intro x hx
    refine ⟨ρ g⁻¹ x, ?_, ρ.self_inv_apply g x⟩
    intro t
    change ρ t.val (ρ g⁻¹ x) = ρ g⁻¹ x
    apply (ρ.apply_bijective g).injective
    rw [← conjugate_action ρ g t.val, ρ.self_inv_apply]
    exact hx ⟨(MulAut.conj g) t.val, ⟨t.val,t.property,rfl⟩⟩
  · rintro x ⟨y,hy,rfl⟩ ⟨h,hh⟩
    obtain ⟨t,ht,rfl⟩ := hh
    change ρ ((MulAut.conj g) t) (ρ g y) = ρ g y
    rw [conjugate_action, show ρ t y = y from hy ⟨t,ht⟩]

theorem invariant_map (ρ : Representation k G V) (g : G) (T : Subgroup G)
    (W : Submodule k V) (hW : ∀ t : T, W ≤ W.comap (ρ t.val)) :
    ∀ t : conjugate g T, W.map (ρ g) ≤ (W.map (ρ g)).comap (ρ t.val) := by
  rintro ⟨h,hh⟩ x ⟨y,hy,rfl⟩
  obtain ⟨t,ht,rfl⟩ := hh
  exact ⟨ρ t y, hW ⟨t,ht⟩ hy, (conjugate_action ρ g t y).symm⟩

theorem invariant_comap (ρ : Representation k G V) (g : G) (T : Subgroup G)
    (W : Submodule k V) (hW : ∀ t : conjugate g T, W ≤ W.comap (ρ t.val)) :
    ∀ t : T, W.comap (ρ g) ≤ (W.comap (ρ g)).comap (ρ t.val) := by
  intro t x hx
  change ρ g (ρ t.val x) ∈ W
  rw [← conjugate_action]
  exact hW ⟨(MulAut.conj g) t.val, ⟨t.val,t.property,rfl⟩⟩ hx

theorem finrank_map (ρ : Representation k G V) (g : G) (W : Submodule k V) :
    Module.finrank k (W.map (ρ g)) = Module.finrank k W :=
  (linear ρ g).finrank_map_eq W

theorem finrank_comap (ρ : Representation k G V) (g : G) (W : Submodule k V) :
    Module.finrank k (W.comap (ρ g)) = Module.finrank k W := by
  rw [← finrank_map ρ g (W.comap (ρ g)),
    Submodule.map_comap_eq_of_surjective (ρ.apply_bijective g).surjective]

theorem coinvariants_conjugate (ρ : Representation k G V) (g : G) (T : Subgroup G) :
    Coinvariants.ker (ρ.comp (conjugate g T).subtype) =
      (Coinvariants.ker (ρ.comp T.subtype)).map (ρ g) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨⟨h,hh⟩,x⟩, rfl⟩
    obtain ⟨t,ht,rfl⟩ := hh
    refine ⟨ρ t (ρ g⁻¹ x) - ρ g⁻¹ x,
      Coinvariants.sub_mem_ker (ρ := ρ.comp T.subtype) ⟨t,ht⟩ (ρ g⁻¹ x), ?_⟩
    change ρ g (ρ t (ρ g⁻¹ x) - ρ g⁻¹ x) = ρ ((MulAut.conj g) t) x - x
    rw [map_sub, ← conjugate_action, ρ.self_inv_apply]
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨t,x⟩, rfl⟩
    change ρ g (ρ t.val x - x) ∈ Coinvariants.ker (ρ.comp (conjugate g T).subtype)
    rw [map_sub, ← conjugate_action]
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp (conjugate g T).subtype)
      ⟨(MulAut.conj g) t.val, ⟨t.val,t.property,rfl⟩⟩ (ρ g x)

theorem central_conjugate (g : G) (T S : Subgroup G)
    (hS : S ≤ (Subgroup.center T).map T.subtype) :
    conjugate g S ≤ (Subgroup.center (conjugate g T)).map (conjugate g T).subtype := by
  rintro z ⟨s,hs,rfl⟩
  obtain ⟨t,ht,rfl⟩ := hS hs
  refine ⟨⟨(MulAut.conj g) t.val, ⟨t.val,t.property,rfl⟩⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  rintro ⟨h,hh⟩
  obtain ⟨u,hu,rfl⟩ := hh
  apply Subtype.ext
  change (MulAut.conj g) u * (MulAut.conj g) t.val =
    (MulAut.conj g) t.val * (MulAut.conj g) u
  rw [← map_mul, ← map_mul]
  exact congrArg (MulAut.conj g) (congrArg Subtype.val
    (Subgroup.mem_center_iff.mp ht ⟨u,hu⟩))

theorem displacement_conjugate (ρ : Representation k G V) (g : G) (T : Subgroup G)
    (N : Submodule k V) (x : V) :
    (∀ t : conjugate g T, ρ t.val (ρ g x) - ρ g x ∈ N.map (ρ g)) ↔
      ∀ t : T, ρ t.val x - x ∈ N := by
  constructor
  · intro h t
    have ht := h ⟨(MulAut.conj g) t.val, ⟨t.val,t.property,rfl⟩⟩
    change ρ ((MulAut.conj g) t.val) (ρ g x) - ρ g x ∈ N.map (ρ g) at ht
    rw [conjugate_action, ← map_sub] at ht
    obtain ⟨y,hy,he⟩ := ht
    exact ((ρ.apply_bijective g).injective he) ▸ hy
  · rintro h ⟨t,ht⟩
    obtain ⟨u,hu,rfl⟩ := ht
    refine ⟨ρ u x - x,h ⟨u,hu⟩, ?_⟩
    change ρ g (ρ u x - x) = ρ ((MulAut.conj g) u) (ρ g x) - ρ g x
    rw [map_sub, conjugate_action]

end Transport

/-- The point transported by an actual derived-group element upstairs. -/
def movedPoint (g : D F) := (P F).map (OrthogonalCover.action F g)
/-- The first natural space transported by the same group element. -/
def movedLine (g : D F) := (N1 F).map (derivedAction F g)
/-- The existing natural plane transported by the same group element. -/
def movedPlane (g : D F) := (naturalPlane F).map (derivedAction F g)
/-- The long-root subgroup with its conjugated derived-group embedding. -/
def movedRoot (g : D F) := Transport.conjugate g (longRoot F)
/-- The conjugated intrinsic positive-root Sylow subgroup. -/
def movedSylow (g : D F) := Transport.conjugate g (U F)

theorem movedSylow_coe [Finite F] (g : D F) :
    ((g • sylow F : Sylow 2 (D F)) : Subgroup (D F)) = movedSylow F g := by
  rw [Sylow.coe_subgroup_smul, sylow_coe]
  rfl

/-- The two linear actions transport preimages through the literal map `mk`. -/
theorem moved_preimage (g : D F) (N : Submodule F (Space F)) :
    (N.map (derivedAction F g)).comap (mk F) =
      (N.comap (mk F)).map (OrthogonalCover.action F g) := by
  apply le_antisymm
  · rintro x ⟨v,hv,hvx⟩
    refine ⟨OrthogonalCover.action F g⁻¹ x, ?_,
      (OrthogonalCover.action F).self_inv_apply g x⟩
    change mk F (OrthogonalCover.action F g⁻¹ x) ∈ N
    have he : mk F (OrthogonalCover.action F g⁻¹ x) = v := by
      apply ((derivedAction F).apply_bijective g).injective
      change derivedAction F g (derivedAction F g⁻¹ (mk F x)) = derivedAction F g v
      rw [(derivedAction F).self_inv_apply]
      exact hvx.symm
    rw [he]
    exact hv
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨mk F y,hy,rfl⟩

theorem scalarLine_map (g : D F) :
    (scalarLine F).map (OrthogonalCover.action F g) = scalarLine F := by
  have hfix (x : TraceZero F) (hx : x ∈ scalarLine F) :
      OrthogonalCover.action F g x = x :=
    (show x ∈ fixed (OrthogonalCover.action F) from (fixed_eq_scalarLine F).symm ▸ hx) g
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    rwa [hfix y hy]
  · intro x hx
    exact ⟨x,hx,hfix x hx⟩

theorem movedLine_eq_image (g : D F) : movedLine F g = (movedPoint F g).map (mk F) := by
  rw [movedLine, N1, movedPoint, ← Submodule.map_comp, ← Submodule.map_comp]
  rfl

theorem movedLine_fixed (g : D F) :
    fixed ((derivedAction F).comp (movedSylow F g).subtype) = movedLine F g := by
  rw [movedSylow, Transport.fixed_conjugate, natural_fixed]
  rfl

theorem moved_cover_fixed (g : D F) :
    fixed ((OrthogonalCover.action F).comp (movedSylow F g).subtype) =
      (movedLine F g).comap (mk F) := by
  rw [movedSylow, Transport.fixed_conjugate, cover_fixed, movedLine, moved_preimage]

theorem movedLine_preimage (g : D F) :
    (movedLine F g).comap (mk F) = movedPoint F g ⊔ scalarLine F := by
  rw [movedLine, moved_preimage, N1_preimage, Submodule.map_sup, scalarLine_map]
  rfl

theorem movedPoint_disjoint (g : D F) : Disjoint (movedPoint F g) (scalarLine F) := by
  rw [← scalarLine_map F g]
  exact Submodule.disjoint_map ((OrthogonalCover.action F).apply_bijective g).injective
    (P_disjoint_scalar F)

omit [CharP F 2] in
theorem movedPoint_finrank (g : D F) : Module.finrank F (movedPoint F g) = 1 :=
  (Transport.finrank_map _ _ _).trans (P_finrank F)

theorem movedLine_finrank (g : D F) : Module.finrank F (movedLine F g) = 1 :=
  (Transport.finrank_map _ _ _).trans (N1_finrank F)

theorem movedPlane_finrank (g : D F) : Module.finrank F (movedPlane F g) = 2 :=
  (Transport.finrank_map _ _ _).trans (naturalPlane_finrank F)

theorem movedLine_invariant (g : D F) :
    ∀ t : movedSylow F g, movedLine F g ≤
      (movedLine F g).comap (derivedAction F t.val) :=
  Transport.invariant_map _ g (U F) (N1 F) (N1_invariant F)

theorem movedPlane_invariant (g : D F) :
    ∀ t : movedSylow F g, movedPlane F g ≤
      (movedPlane F g).comap (derivedAction F t.val) :=
  Transport.invariant_map _ g (U F) (naturalPlane F) (naturalPlane_invariant F)

theorem movedLine_unique [Finite F] (g : D F) (W : Submodule F (Space F))
    (hW : ∀ t : movedSylow F g, W ≤ W.comap (derivedAction F t.val))
    (hdim : Module.finrank F W = 1) : W = movedLine F g := by
  have he := invariant_line_unique F (W.comap (derivedAction F g))
    (Transport.invariant_comap _ g (U F) W hW)
    ((Transport.finrank_comap _ _ _).trans hdim)
  have hm := congrArg (Submodule.map (derivedAction F g)) he
  rw [Submodule.map_comap_eq_of_surjective ((derivedAction F).apply_bijective g).surjective] at hm
  exact hm

theorem movedPlane_unique [Finite F] (g : D F) (W : Submodule F (Space F))
    (hW : ∀ t : movedSylow F g, W ≤ W.comap (derivedAction F t.val))
    (hdim : Module.finrank F W = 2) : W = movedPlane F g := by
  have he := invariant_plane_unique F (W.comap (derivedAction F g))
    (Transport.invariant_comap _ g (U F) W hW)
    ((Transport.finrank_comap _ _ _).trans hdim)
  have hm := congrArg (Submodule.map (derivedAction F g)) he
  rw [Submodule.map_comap_eq_of_surjective ((derivedAction F).apply_bijective g).surjective] at hm
  exact hm

theorem moved_singular_iff (g : D F) (x : TraceZero F)
    (hx : x ∈ (movedLine F g).comap (mk F)) : form F x = 0 ↔ x ∈ movedPoint F g := by
  rw [movedLine, moved_preimage] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  rw [form_invariant]
  constructor
  · intro hq
    exact ⟨y, (singular_fixed_iff F y ((cover_fixed F).symm ▸ hy)).mp hq,rfl⟩
  · rintro ⟨z,hz,he⟩
    have hzy := ((OrthogonalCover.action F).apply_bijective g).injective he
    rw [← hzy]
    exact singularPlane_singular F z (P_le_plane F hz)

theorem moved_singular_unique (g : D F) (R : Submodule F (TraceZero F))
    (hR : R ≤ (movedLine F g).comap (mk F)) (hdim : Module.finrank F R = 1)
    (hq : ∀ x ∈ R, form F x = 0) : R = movedPoint F g := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    exact (moved_singular_iff F g x (hR hx)).mp (hq x hx)
  · rw [hdim, movedPoint_finrank]

omit [CharP F 2] in
theorem movedRoot_central (g : D F) :
    movedRoot F g ≤ (Subgroup.center (movedSylow F g)).map (movedSylow F g).subtype :=
  Transport.central_conjugate g (U F) (longRoot F) (longRoot_central F)

omit [CharP F 2] in
theorem movedRoot_commutator (g : D F) :
    Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype) =
      (singularPlane F).map (OrthogonalCover.action F g) := by
  rw [movedRoot, Transport.coinvariants_conjugate, longRoot_commutator]

theorem movedRoot_geometry (g : D F) :
    Module.finrank F (Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype)) = 2 ∧
    (∀ x ∈ Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype), form F x = 0) ∧
    Disjoint (Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype)) (scalarLine F) ∧
    (movedPlane F g).comap (mk F) =
      Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype) ⊔ scalarLine F := by
  rw [movedRoot_commutator]
  refine ⟨(Transport.finrank_map _ _ _).trans (singularPlane_finrank F), ?_, ?_, ?_⟩
  · rintro x ⟨y,hy,rfl⟩
    rw [form_invariant]
    exact singularPlane_singular F y hy
  · rw [← scalarLine_map F g]
    exact Submodule.disjoint_map ((OrthogonalCover.action F).apply_bijective g).injective
      (singularPlane_disjoint_scalar F)
  · rw [movedPlane, moved_preimage, naturalPlane_preimage,
      Submodule.map_sup, scalarLine_map]

/-- Every actual derived Sylow is reached by this paired transport. -/
theorem exists_marking [Finite F] (Q : Sylow 2 (D F)) :
    ∃ g : D F, (Q : Subgroup (D F)) = movedSylow F g := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (D F) (sylow F) Q
  exact ⟨g, hg ▸ movedSylow_coe F g⟩

/-- The fixed-space description modulo the first line is preserved by the same transport. -/
theorem moved_displacement_iff (g : D F) (x : Space F) :
    (∀ t : movedSylow F g, derivedAction F t.val x - x ∈ movedLine F g) ↔
      x ∈ movedPlane F g := by
  obtain ⟨y,rfl⟩ := ((derivedAction F).apply_bijective g).surjective x
  rw [movedSylow, movedLine, Transport.displacement_conjugate, displacement_mem_N1_iff]
  change y ∈ naturalPlane F ↔
    y ∈ ((naturalPlane F).map (derivedAction F g)).comap (derivedAction F g)
  rw [Submodule.comap_map_eq_of_injective ((derivedAction F).apply_bijective g).injective]

/-- Quotient action for an arbitrary transported marking. -/
def movedQuotientAction (g : D F) :
    Representation F (movedSylow F g) (Space F ⧸ movedLine F g) :=
  Representation.quotient ((derivedAction F).comp (movedSylow F g).subtype)
    (movedLine F g) (movedLine_invariant F g)

theorem moved_quotient_fixed_preimage (g : D F) :
    (fixed (movedQuotientAction F g)).comap (movedLine F g).mkQ = movedPlane F g := by
  ext x
  change (∀ t : movedSylow F g,
    (movedLine F g).mkQ (derivedAction F t.val x) = (movedLine F g).mkQ x) ↔ _
  rw [← moved_displacement_iff]
  apply forall_congr'
  intro t
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

omit [CharP F 2] in
/-- The transported projective point is totally singular. -/
theorem movedPoint_singular (g : D F) (x : TraceZero F) (hx : x ∈ movedPoint F g) :
    form F x = 0 := by
  obtain ⟨y,hy,rfl⟩ := hx
  rw [form_invariant]
  exact singularPlane_singular F y (P_le_plane F hy)

/-- The actual source flag is nested after conjugation. -/
theorem movedLine_le_plane (g : D F) : movedLine F g ≤ movedPlane F g :=
  Submodule.map_mono (N1_le_naturalPlane F)

omit [CharP F 2] in
/-- The transported long root is contained in the transported Sylow, with both
subgroups regarded inside the original derived group. -/
theorem movedRoot_le (g : D F) : movedRoot F g ≤ movedSylow F g :=
  Subgroup.map_mono (longRoot_le F)


end Atlas.G2.Natural.OrthogonalCover.SylowFlag
