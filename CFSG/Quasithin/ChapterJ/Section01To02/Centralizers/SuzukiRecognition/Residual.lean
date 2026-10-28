module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Transfer
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreImage

/-!
# Sylow and involution-centralizer reductions inside the J.2.9 residual

After transfer separates S₀ from L_s, the actual intersection T_s∩L_s
is S₁. Normal Sylow intersection consequently gives a Sylow subgroup of
L_s with exactly this underlying subgroup. The earlier equality
C_H(s)=T_s computes C_{L_s}(z), and the seven-group orbit transports this
calculation to every nonidentity element of V.

These deductions retain the preceding local product and fusion inputs.
They do not assume or assert a Suzuki recognition isomorphism.

Source: Aschbacher–Smith, J.2.9, printed p.438 (PDF p.449).
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- The embedded residual remains two-perfect on its actual carrier. -/
theorem Ls_isPPerfect : IsPPerfect 2 c.Ls :=
  (isPPerfect_pResidual (G := c.Gs) 2).of_surjective
    ((pResidual 2 c.Gs).equivMapOfInjective c.Gs.subtype c.Gs.subtype_injective).toMonoidHom
    ((pResidual 2 c.Gs).equivMapOfInjective c.Gs.subtype c.Gs.subtype_injective).surjective

/-- Transfer and the local factorization compute the Sylow intersection. -/
theorem Ts_inf_Ls
    (hdisjoint : Disjoint c.S0 c.Ls)
    (hproduct : ∀ x ∈ c.Ts, ∃ a ∈ c.S0, ∃ b ∈ c.S1, x = a * b) :
    c.Ts ⊓ c.Ls = c.S1 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hproduct x hx.1
    have hal : a ∈ c.Ls := by
      have := c.Ls.mul_mem hx.2 (c.Ls.inv_mem (c.S1_le_Ls hb))
      simpa only [mul_inv_cancel_right] using this
    have ha1 : a = 1 := disjoint_def.mp hdisjoint ha hal
    simpa only [ha1, one_mul] using hb
  · exact le_inf c.S1_le_Ts c.S1_le_Ls

/-- The source Sylow group restricts to the literal S₁ inside L_s. -/
theorem exists_sylow_Ls
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (hintersection : c.Ts ⊓ c.Ls = c.S1) :
    ∃ Q : Sylow 2 c.Ls, (Q : Subgroup c.Ls) = c.S1.subgroupOf c.Ls := by
  let R := c.Ls.subgroupOf c.Gs
  let : R.Normal := normal_subgroupOf_of_le_normalizer c.Gs_normalizes_Ls
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal R
  let e : R ≃* c.Ls := subgroupOfEquivOfLe c.Ls_le_Gs
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (Q : Subgroup R).map e.toMonoidHom = c.S1.subgroupOf c.Ls
  rw [hQ, hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ((y : c.Gs) : G) ∈ c.S1
    rw [← hintersection]
    exact ⟨hy, y.property⟩
  · intro hx
    have hxT : (x : G) ∈ c.Ts := c.S1_le_Ts hx
    exact ⟨⟨⟨x, c.Ls_le_Gs x.property⟩, x.property⟩, hxT, rfl⟩

/-- The centralizer of z in L_s follows from the earlier H-centralizer
calculation and the Sylow intersection. -/
theorem Ls_inf_centralizer_z
    (hH : centralizer ({c.z} : Set G) = d.toTypeRuSetup.H)
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (hintersection : c.Ts ⊓ c.Ls = c.S1) :
    c.Ls ⊓ centralizer ({c.z} : Set G) = c.S1 := by
  rw [hH, ← hintersection, ← hHs]
  apply le_antisymm
  · intro x hx
    exact ⟨⟨hx.2, c.Ls_le_Gs hx.1⟩, hx.1⟩
  · intro x hx
    exact ⟨hx.2, hx.1.1⟩

/-- Transport the z-centralizer along the actual seven-group orbit. -/
theorem Ls_inf_centralizer_of_B7_conjugate
    (hz : c.Ls ⊓ centralizer ({c.z} : Set G) = c.S1)
    {v b : G} (hb : b ∈ c.B7) (hv : b * c.z * b⁻¹ = v) :
    c.Ls ⊓ centralizer ({v} : Set G) = c.S1 := by
  let f := MulAut.conj b
  have hL : c.Ls.map f.toMonoidHom = c.Ls :=
    mem_normalizer_iff_map_conj_eq.mp
      (c.Gs_normalizes_Ls (c.B7_le_Gs hb))
  have hS : c.S1.map f.toMonoidHom = c.S1 :=
    mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right c.Ts c.B7 hb)
  have hfz : f c.z = v := hv
  have hm : (c.Ls ⊓ centralizer ({c.z} : Set G)).map f.toMonoidHom ≤
      c.Ls ⊓ centralizer ({v} : Set G) := by
    apply le_inf
    · exact (map_mono inf_le_left).trans_eq hL
    · have hc := (map_mono (f := f.toMonoidHom)
          (show c.Ls ⊓ centralizer ({c.z} : Set G) ≤ centralizer ({c.z} : Set G)
            from inf_le_right)).trans
        (map_centralizer_le_centralizer_image ({c.z} : Set G) f.toMonoidHom)
      simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, hfz] using hc
  have hle : c.S1 ≤ c.Ls ⊓ centralizer ({v} : Set G) := by
    simpa only [hz, hS] using hm
  apply le_antisymm ?_ hle
  intro x hx
  have hxL : f.symm x ∈ c.Ls := by
    have hm : x ∈ c.Ls.map f.toMonoidHom := hL.symm ▸ hx.1
    obtain ⟨y, hy, rfl⟩ := hm
    change f.symm (f y) ∈ c.Ls
    rwa [f.symm_apply_apply]
  have hxC : f.symm x ∈ centralizer ({c.z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply, hfz] using
      mem_centralizer_singleton_iff.mp hx.2
  have hxS : f.symm x ∈ c.S1 := hz ▸ ⟨hxL, hxC⟩
  have hm := mem_map_of_mem f.toMonoidHom hxS
  simpa only [hS, MulEquiv.coe_toMonoidHom, f.apply_symm_apply] using hm

/-- The uniform intrinsic centralizers consumed by the TI criterion. -/
theorem uniform_Ls_centralizers
    (hz : c.Ls ⊓ centralizer ({c.z} : Set G) = c.S1)
    (horbit : ∀ v ∈ d.V, v ≠ 1 → ∃ b ∈ c.B7, b * c.z * b⁻¹ = v) :
    ∀ v : c.Ls, v ∈ d.V.subgroupOf c.Ls → v ≠ 1 →
      centralizer ({v} : Set c.Ls) = c.S1.subgroupOf c.Ls := by
  intro v hv hv1
  obtain ⟨b, hb, he⟩ := horbit v hv (fun h => hv1 (Subtype.ext h))
  have hC := c.Ls_inf_centralizer_of_B7_conjugate hz hb he
  ext x
  constructor
  · intro hx
    have hxc : (x : G) ∈ centralizer ({(v : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))
    exact hC ▸ ⟨x.property, hxc⟩
  · intro hx
    have hxc : (x : G) ∈ centralizer ({(v : G)} : Set G) :=
      ((hC.symm ▸ hx : (x : G) ∈ c.Ls ⊓ centralizer ({(v : G)} : Set G))).2
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hxc))

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
