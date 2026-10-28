module

public import CFSG.Quasithin.ChapterG.Section12.Defs

/-!
# Hyperplane geometry for the G.12.12 application

An invariant symplectic form identifies the input hyperplane with the
perpendicular of its center, and the literal transvection actors then lie
in the source point radical. Irreducibility ensures that the center's orbit
escapes the hyperplane. These implications use the source inputs; existence
of the invariant form and recognition of the resulting group remain separate.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.12.12(2)--(3),
printed p.374.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section12
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A full hyperplane transvection is automatically in the literal quotient
kernel. Thus one may verify (*) using the ambient acting group. -/
theorem goodVector_iff
    {G : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.IsAlt) (hG : G ≤ formStabilizer B) (v : V) :
    GoodVector G B hB v ↔ v ≠ 0 ∧
      ∀ φ : Module.Dual (ZMod 2) (B v).ker, φ ⟨v, hB v⟩ = 0 →
        ∃ g ∈ G, ∀ w : (B v).ker, g w = (w : V) + φ w • v := by
  constructor
  · intro h
    refine ⟨h.nonzero, ?_⟩
    intro φ hφ
    obtain ⟨g, hg⟩ := h.full φ hφ
    exact ⟨g.val, g.property.1, hg⟩
  · rintro ⟨hv, hfull⟩
    refine ⟨hv, fun a => a.property.2.1,
      fun a w => a.property.2.2.2 w w.property, ?_⟩
    intro φ hφ
    obtain ⟨g, hg, he⟩ := hfull φ hφ
    have hgv : g v = v := by simpa only [hφ, zero_smul, add_zero] using he ⟨v, hB v⟩
    have hrad : g ∈ pointRadical G B v := by
      apply (mem_pointRadical_iff hG).mpr
      refine ⟨hg, hgv, ?_⟩
      intro w hw
      rw [he ⟨w, hw⟩, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    exact ⟨⟨g, hrad⟩, he⟩

/-- Enlarging the form-preserving group preserves condition (*). -/
theorem GoodVector.mono
    {G H : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
    {hB : B.IsAlt} {v : V} (h : GoodVector G B hB v)
    (hGH : G ≤ H) (hH : H ≤ formStabilizer B) : GoodVector H B hB v := by
  rw [goodVector_iff hB hH]
  refine ⟨h.nonzero, ?_⟩
  intro φ hφ
  obtain ⟨g, hg⟩ := h.full φ hφ
  exact ⟨g.val, hGH g.property.1, hg⟩

/-- Irreducibility forces a nonzero vector's orbit to escape every proper
subspace, without requiring that subspace to be invariant. -/
theorem Irreducible.exists_outside
    {K : Subgroup (V ≃ₗ[ZMod 2] V)} (hK : Irreducible K)
    {W : Submodule (ZMod 2) V} (hW : W ≠ ⊤) {v : V} (hv : v ≠ 0) :
    ∃ k ∈ K, k v ∉ W := by
  by_contra! hn
  let S : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {w | ∃ k ∈ K, k v = w}
  have hstable : ∀ k ∈ K, ∀ w ∈ S, k w ∈ S := by
    intro k hk w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, hg, rfl⟩ := hw
      exact Submodule.subset_span ⟨k * g, K.mul_mem hk hg, rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using S.add_mem hx hy
    | smul t x _ hx => simpa only [map_smul] using S.smul_mem t hx
  have hvS : v ∈ S := Submodule.subset_span ⟨1, K.one_mem, rfl⟩
  have htop : S = ⊤ := (hK S hstable).resolve_left (by
    intro he
    rw [he, Submodule.mem_bot] at hvS
    exact hv hvS)
  have hle : S ≤ W := Submodule.span_le.mpr (by
    rintro w ⟨k, hk, rfl⟩
    exact hn k hk)
  exact hW (top_unique (by simpa only [htop] using hle))

/-- A full action on an identified perpendicular hyperplane supplies (*).
The same actors realize every functional after transport of the hyperplane. -/
theorem goodVector_of_fullCenterAction
    {G Q : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.IsAlt) (hG : G ≤ formStabilizer B) (hQ : Q ≤ G)
    {W : Submodule (ZMod 2) V} {v : W}
    (h : BinaryTransvection.FullCenterAction Q.subtype W v)
    (hW : W = (B v).ker) : GoodVector G B hB v := by
  rw [goodVector_iff hB hG]
  refine ⟨h.nonzero, ?_⟩
  intro φ hφ
  let i : W →ₗ[ZMod 2] (B v).ker := W.subtype.codRestrict _ (fun w => hW.le w.property)
  have hi : i v = ⟨(v : V), hB v⟩ := rfl
  obtain ⟨g, hg⟩ := h.full (φ.comp i) (by simpa only [LinearMap.comp_apply, hi] using hφ)
  refine ⟨g.val, hQ g.property, ?_⟩
  intro w
  let w' : W := ⟨w, hW.ge w.property⟩
  exact hg w'

variable [FiniteDimensional (ZMod 2) V]

/-- G.12.12(2), with the still-independent existence of the invariant
symplectic form left explicit. -/
theorem ModuleHypotheses.hyperplane_eq
    {H K Q : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {v : W}
    (h : ModuleHypotheses H K Q W v)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hpres : K ⊔ Q ≤ formStabilizer B) : W = (B v).ker :=
  h.transvections.hyperplane_eq_orthogonal B hB hnd
    (fun q => hpres ((show Q ≤ K ⊔ Q from le_sup_right) q.property)) h.hyperplane h.dimension

/-- The specified vector satisfies condition (*) in the actual subgroup KQ. -/
theorem ModuleHypotheses.goodVector
    {H K Q : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {v : W}
    (h : ModuleHypotheses H K Q W v)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hpres : K ⊔ Q ≤ formStabilizer B) : GoodVector (K ⊔ Q) B hB v :=
  goodVector_of_fullCenterAction hB hpres le_sup_right h.transvections
    (h.hyperplane_eq B hB hnd hpres)

/-- The orbit-escape assertion in G.12.12(3), proved already from irreducibility. -/
theorem ModuleHypotheses.exists_outside
    {H K Q : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {v : W}
    (h : ModuleHypotheses H K Q W v) : ∃ k ∈ K, k v ∉ W := by
  apply h.irreducible.exists_outside _ h.transvections.nonzero
  intro he
  have hd := h.hyperplane
  rw [he, finrank_top] at hd
  omega

end CFSG.Quasithin.ChapterG.Section12
