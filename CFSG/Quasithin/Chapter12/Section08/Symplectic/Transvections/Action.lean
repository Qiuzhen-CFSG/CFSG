module

public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Quotients
public import Theory.GroupAction.BinaryTransvectionImage
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.FieldTheory.Finiteness

/-!
# Full transvection image on the literal intersection quotient

The conjugation equation identifies displacements with ambient commutators.
The earlier class-two bound puts these in V₁^g, whose image is contained in
V₂hat. Disjointness V₁^g ∩ Z(U)=1 identifies fixed quotient vectors with
commuting representatives. The extraspecial center calculation and the
exact two center-intersection cuts therefore determine the fixed space.
Finite binary duality then realizes every entire functional, and proves
both inclusions of the full transvection action image.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
12.8.11(3–4), printed p.854 / PDF p.871. The geometric bridge premises
`hcenter`, `hcut`, and the nonzero marked-line witness remain explicit;
these conditional transport theorems do not claim to discharge them.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The original faithful quotient acts linearly on the original central quotient. -/
def linearAction (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) :
    Hdot F ρ →* (Additive F.Uhat ≃ₗ[ZMod 2] Additive F.Uhat) where
  toFun h := { (faithfulAction F ρ h).toAdditive with
    map_smul' := ZMod.map_smul (faithfulAction F ρ h).toAdditive }
  map_one' := by
    apply LinearEquiv.ext
    intro q
    change Additive.ofMul (faithfulAction F ρ 1 q.toMul) = q
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearEquiv.ext
    intro q
    change Additive.ofMul (faithfulAction F ρ (a*b) q.toMul) =
      Additive.ofMul (faithfulAction F ρ a (faithfulAction F ρ b q.toMul))
    rw [map_mul]
    rfl

@[simp] theorem linearAction_mk_apply (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (h : F.H) (q : F.Uhat) :
    linearAction F ρ (QuotientGroup.mk' ρ.ker h) (Additive.ofMul q) =
      Additive.ofMul (ρ h q) := rfl

/-- Membership in an image is membership in the subgroup times the actual center. -/
theorem mem_hatImage_mk_iff (F : InvariantFlag T V n) (A : Subgroup G)
    (hA : A ≤ F.U) (u : F.U) :
    QuotientGroup.mk' (center F.U) u ∈ hatImage F A ↔ (u : G) ∈ A ⊔ F.ZU := by
  have hZ : F.ZU.subgroupOf F.U = center F.U := by
    ext u
    constructor
    · rintro ⟨z, hz, he⟩
      exact (Subtype.ext he : z = u) ▸ hz
    · intro hu
      exact ⟨u, hu, rfl⟩
  change u ∈ ((A.subgroupOf F.U).map (QuotientGroup.mk' (center F.U))).comap
    (QuotientGroup.mk' (center F.U)) ↔ _
  rw [comap_map_eq, QuotientGroup.ker_mk', ← hZ,
    ← subgroupOf_sup hA (show F.ZU ≤ F.U from map_subtype_le (center F.U))]
  rfl

private theorem actor_le_H (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2) :
    F.X g ≤ F.H := (F.X_le_plane_centralizer g hg).trans
  ((centralizer_le (F.monotone (by omega : 1 ≤ 2))).trans (centralizer_le_normalizer _))

/-- The class-two commutator bound transports to the conjugate actor. -/
theorem commutator_X_E_le_conjugate_point (F : InvariantFlag T V n) (g : G)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) :
    ⁅F.X g, F.E g⁆ ≤ conjugate (F.Vi 1) g := by
  have hX : F.X g ≤ conjugate F.U g := map_mono inf_le_left
  calc
    ⁅F.X g, F.E g⁆ ≤ ⁅conjugate F.U g, conjugate F.U g⁆ :=
      commutator_mono hX (inf_le_right.trans hX)
    _ = conjugate ⁅F.U,F.U⁆ g := (map_commutator _ _ _).symm
    _ ≤ conjugate (F.Vi 1) g := map_mono hcomm

/-- The conjugate commutator center lies in the marked plane. -/
theorem conjugate_point_le_plane (F : InvariantFlag T V n) (g : G)
    (hg : g ∈ F.Gi 2) : conjugate (F.Vi 1) g ≤ F.Vi 2 := by
  rintro z ⟨a, ha, rfl⟩
  exact (mem_normalizer_iff.mp ((normalizer (F.Vi 2 : Set G)).inv_mem hg) a).mp
    (F.monotone (by omega : 1 ≤ 2) ha)

/-- Each displacement of Ehat is in the actual image of V₂. -/
theorem Ehat_displacement_mem_plane (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hg : g ∈ F.Gi 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (x : dotImage F F.uhatAction (F.X g))
    (e : hatSpace F (F.E g)) :
    linearAction F F.uhatAction x e - e ∈ hatSpace F (F.Vi 2) := by
  obtain ⟨h, hh, hx⟩ := x.property
  obtain ⟨u, hu, he⟩ := (show e.val.toMul ∈ hatImage F (F.E g) from e.property)
  have hR := commutator_X_E_le_conjugate_point F g hcomm
    (commutator_mem_commutator hh hu)
  have hc := conjugate_point_le_plane F g hg hR
  have hd : ((F.uAction h u / u : F.U) : G) = ⁅(h : G),(u : G)⁆ := by
    change ((h : G) * (u : G) * (h : G)⁻¹) / (u : G) = _
    simp only [commutatorElement_def, div_eq_mul_inv]
  have hm : F.uAction h u / u ∈ (F.Vi 2).subgroupOf F.U := by
    change ((F.uAction h u / u : F.U) : G) ∈ F.Vi 2
    rw [hd]
    exact hc
  have him : QuotientGroup.mk' (center F.U) (F.uAction h u / u) ∈ hatImage F (F.Vi 2) :=
    ⟨_, hm, rfl⟩
  have he' : (e : Additive F.Uhat) = Additive.ofMul (QuotientGroup.mk' (center F.U) u) :=
    (congrArg Additive.ofMul he).symm
  rw [← hx, he', linearAction_mk_apply, F.uhatAction_apply_mk]
  change QuotientGroup.mk' (center F.U) (F.uAction h u) /
    QuotientGroup.mk' (center F.U) u ∈ hatImage F (F.Vi 2)
  simpa only [map_div] using him

/-- Disjointness of the conjugate commutator line and Z(U) identifies fixed
vectors with actual commuting representatives. -/
theorem Ehat_fixed_iff_centralizes_X (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hg : g ∈ F.Gi 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (u : F.U) (hu : (u : G) ∈ F.E g) :
    (∀ x : dotImage F F.uhatAction (F.X g),
      linearAction F F.uhatAction x (Additive.ofMul (QuotientGroup.mk' (center F.U) u)) =
        Additive.ofMul (QuotientGroup.mk' (center F.U) u)) ↔
      (u : G) ∈ centralizer (F.X g : Set G) := by
  constructor
  · intro hfix x hx
    let h : F.H := ⟨x, actor_le_H F g hg hx⟩
    have hf := hfix (dotMap F F.uhatAction (F.X g) (actor_le_H F g hg) ⟨x,hx⟩)
    change Additive.ofMul (F.uhatAction h (QuotientGroup.mk' (center F.U) u)) = _ at hf
    have he := Additive.ofMul.injective hf
    rw [F.uhatAction_apply_mk] at he
    have hc : F.uAction h u / u ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp he
    have hd : ((F.uAction h u / u : F.U) : G) = ⁅x,(u : G)⁆ := by
      change (x * (u : G) * x⁻¹) / (u : G) = _
      simp only [commutatorElement_def, div_eq_mul_inv]
    have hz : ⁅x,(u : G)⁆ ∈ F.ZU := ⟨_,hc,hd⟩
    have hr := commutator_X_E_le_conjugate_point F g hcomm
      (commutator_mem_commutator hx hu)
    have hone := mem_bot.mp (hdis.le_bot ⟨hr,hz⟩)
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  · intro hc x
    obtain ⟨h, hh, hx⟩ := x.property
    rw [← hx, linearAction_mk_apply, F.uhatAction_apply_mk]
    have he : F.uAction h u = u := by
      apply Subtype.ext
      rw [F.uAction_apply, hc h hh, mul_inv_cancel_right]
    rw [he]

/-- Fixed-space transport from the extraspecial center and the two exact
center-intersection cuts. These geometric premises are retained explicitly. -/
theorem Ehat_fixed_of_center_geometry (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hg : g ∈ F.Gi 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (hcenter : centerIn (F.X g) = F.Vi 2 ⊔ conjugate F.ZU g)
    (hcut : F.E g ⊓ (F.Vi 2 ⊔ conjugate F.ZU g) = F.E g ⊓ (F.Vi 2 ⊔ F.ZU))
    (e : hatSpace F (F.E g)) :
    (∀ x : dotImage F F.uhatAction (F.X g), linearAction F F.uhatAction x e = e) ↔
      (e : Additive F.Uhat) ∈ hatSpace F (F.Vi 2) := by
  obtain ⟨u, hu, he⟩ := (show e.val.toMul ∈ hatImage F (F.E g) from e.property)
  have he' : (e : Additive F.Uhat) = Additive.ofMul (QuotientGroup.mk' (center F.U) u) :=
    (congrArg Additive.ofMul he).symm
  rw [he', Ehat_fixed_iff_centralizes_X F g hg hcomm hdis u hu]
  change (u : G) ∈ centralizer (F.X g : Set G) ↔
    QuotientGroup.mk' (center F.U) u ∈ hatImage F (F.Vi 2)
  rw [mem_hatImage_mk_iff F (F.Vi 2) ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))]
  have hux : (u : G) ∈ F.X g := hu.2
  have hcen : (u : G) ∈ centralizer (F.X g : Set G) ↔ (u : G) ∈ centerIn (F.X g) := by
    constructor
    · intro hc
      refine ⟨⟨u, hux⟩, mem_center_iff.mpr ?_, rfl⟩
      intro x
      exact Subtype.ext (hc x x.property)
    · rintro ⟨z, hz, hez⟩ x hx
      rw [← hez]
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hx⟩)
  rw [hcen, hcenter]
  exact ⟨fun h => (hcut.le ⟨hu,h⟩).2, fun h => (hcut.ge ⟨hu,h⟩).2⟩

/-- Full image surjectivity on the literal Ehat from the geometric bridge.
Every functional is realized by one element of the actual quotient image Xdot. -/
theorem full_transvections_of_center_geometry (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hg : g ∈ F.Gi 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (hcenter : centerIn (F.X g) = F.Vi 2 ⊔ conjugate F.ZU g)
    (hcut : F.E g ⊓ (F.Vi 2 ⊔ conjugate F.ZU g) = F.E g ⊓ (F.Vi 2 ⊔ F.ZU))
    (v : hatSpace F (F.E g)) (hv : (v : Additive F.Uhat) ≠ 0)
    (hline : Submodule.span (ZMod 2) {(v : Additive F.Uhat)} = hatSpace F (F.Vi 2)) :
    (∀ x : dotImage F F.uhatAction (F.X g),
      ∃ φ : Module.Dual (ZMod 2) (hatSpace F (F.E g)), φ v = 0 ∧
        ∀ e : hatSpace F (F.E g), linearAction F F.uhatAction x e =
          (e : Additive F.Uhat) + φ e • (v : Additive F.Uhat)) ∧
    (∀ φ : Module.Dual (ZMod 2) (hatSpace F (F.E g)), φ v = 0 →
      ∃ x : dotImage F F.uhatAction (F.X g),
        ∀ e : hatSpace F (F.E g), linearAction F F.uhatAction x e =
          (e : Additive F.Uhat) + φ e • (v : Additive F.Uhat)) := by
  apply BinaryTransvection.full_action_of_fixed_space
    ((linearAction F F.uhatAction).comp (dotImage F F.uhatAction (F.X g)).subtype)
    (hatSpace F (F.E g)) v hv
  · intro x e
    rw [hline]
    exact Ehat_displacement_mem_plane F g hg hcomm x e
  · intro e
    change (∀ x : dotImage F F.uhatAction (F.X g), linearAction F F.uhatAction x e = e) ↔ _
    rw [Ehat_fixed_of_center_geometry F g hg hcomm hdis hcenter hcut, ← hline]
    constructor
    · intro he
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp he
      exact Submodule.mem_span_singleton.mpr ⟨t, Subtype.ext ht⟩
    · intro he
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp he
      exact Submodule.mem_span_singleton.mpr ⟨t, congrArg Subtype.val ht⟩

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
