module
public import Theory.GroupTheory.UniqueFixedCosetFusion
public import Theory.GroupTheory.UniqueFixedCosetQuotient
import Mathlib.Tactic.Group

/-!
# Subgroup fusion and maximal-normalizer fixed cosets

An element central in a Sylow p-subgroup and fixing a unique coset of X
controls pointwise fusion of entire subgroups of the Sylow into that Sylow. For an
X-invariant subgroup U of the Sylow, choose W maximal among subgroups of U
whose normalizer escapes X. The resulting normalizer barriers force every
nonidentity element of U/W to fix a unique coset of X_W/W in N(W)/W.
The quotient retains all of W; its normality is relative to N(W).

Source: the fusion argument of Aschbacher, *Sporadic Groups* (1994), 7.4,
and Aschbacher–Smith, F.4.42, printed p.296 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup
namespace UniqueFixedCoset
variable {G : Type*} [Group G] [Finite G]

/-- One local conjugator agrees on an entire subgroup of the Sylow. -/
theorem sylow_subgroup_fusion {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    {z : G} (hzT : z ∈ (T : Subgroup G))
    (hzcentral : ∀ t ∈ (T : Subgroup G), Commute z t)
    (hunique : ∃! q : G ⧸ M, z • q = q)
    (R : Subgroup G) (hRT : R ≤ T) (g : G)
    (hgR : R.map (MulAut.conj g).toMonoidHom ≤ T) :
    ∃ m ∈ M, ∀ r ∈ R, m*r*m⁻¹ = g*r*g⁻¹ := by
  let B := R.map (MulAut.conj g).toMonoidHom
  let C := centralizer (B : Set G)
  have hzC : z ∈ C := by
    intro b hb
    exact (hzcentral b (hgR hb)).eq.symm
  have hZp : IsPGroup p (zpowers z) := T.isPGroup'.of_injective
    (inclusion (zpowers_le.mpr hzT)) (inclusion_injective _)
  obtain ⟨P,hP⟩ := (hZp.comap_subtype (K := C)).exists_le_sylow
  have hzP : z ∈ (P : Subgroup C).map C.subtype :=
    ⟨⟨z,hzC⟩,hP (mem_zpowers z),rfl⟩
  have hPM : (P : Subgroup C).map C.subtype ≤ M :=
    (p_overgroup_and_normalizer_le (hTM hzT) hunique (P.isPGroup'.map C.subtype) hzP).1
  have hgzC : g*z*g⁻¹ ∈ C := by
    rintro b ⟨r,hr,rfl⟩
    exact (map_mul (MulAut.conj g) r z).symm.trans
      ((congrArg (MulAut.conj g) (hzcentral r (hRT hr)).eq.symm).trans
        (map_mul (MulAut.conj g) z r))
  have hgZp : IsPGroup p (zpowers (⟨g*z*g⁻¹,hgzC⟩ : C)) := by
    have hp := hZp.map (MulAut.conj g).toMonoidHom
    have hle : zpowers (⟨g*z*g⁻¹,hgzC⟩ : C) ≤
        ((zpowers z).map (MulAut.conj g).toMonoidHom).subgroupOf C :=
      zpowers_le.mpr ⟨z,mem_zpowers z,rfl⟩
    exact (hp.comap_subtype (K := C)).of_injective (inclusion hle) (inclusion_injective hle)
  obtain ⟨c,_,hc⟩ := p_element_conjugate_into_sylow P le_top (mem_top _) hgZp
  have hcgM : (c : G)*g ∈ M := by
    apply transporter_mem (hTM hzT) hunique
    have hh := hPM (mem_map.mpr ⟨_,hc,rfl⟩)
    change (c : G)*(g*z*g⁻¹)*(c : G)⁻¹ ∈ M at hh
    simpa only [mul_inv_rev,mul_assoc] using hh
  refine ⟨(c : G)*g,hcgM,?_⟩
  intro r hr
  calc
    ((c : G)*g)*r*((c : G)*g)⁻¹ = (c : G)*(g*r*g⁻¹)*(c : G)⁻¹ := by group
    _ = g*r*g⁻¹ := mul_inv_eq_iff_eq_mul.mpr
      (c.property _ (mem_map_of_mem (MulAut.conj g).toMonoidHom hr)).symm

theorem transporter_mem_of_maximal_normalizers {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {X : Subgroup G} (hTX : (T : Subgroup G) ≤ X)
    {z : G} (hzT : z ∈ (T : Subgroup G))
    (hzcentral : ∀ t ∈ (T : Subgroup G), Commute z t)
    (hunique : ∃! q : G ⧸ X, z • q = q)
    (U W : Subgroup G) (hUT : U ≤ T) (hXU : X ≤ normalizer (U : Set G))
    (hWU : W ≤ U)
    (hmax : ∀ R : Subgroup G, W < R → R ≤ U → normalizer (R : Set G) ≤ X)
    (u g : G) (hu : u ∈ U) (huW : u ∉ W)
    (hgW : g ∈ normalizer (W : Set G)) (hguX : g*u*g⁻¹ ∈ X) : g ∈ X := by
  have huT := hUT hu
  have hup : IsPGroup p (zpowers u) := T.isPGroup'.to_le (zpowers_le.mpr huT)
  obtain ⟨a,ha,hea⟩ := p_element_fusion T hTX hzT hzcentral hunique
    (hTX huT) hguX hup (isConj_iff.mpr ⟨g,rfl⟩)
  have hguU : g*u*g⁻¹ ∈ U := hea ▸ (mem_normalizer_iff.mp (hXU ha) u).mp hu
  let R := W ⊔ zpowers u
  have hRU : R ≤ U := sup_le hWU (zpowers_le.mpr hu)
  have hWR : W < R := lt_of_le_of_ne le_sup_left (by
    intro he
    have huR : u ∈ R := (show zpowers u ≤ R from le_sup_right) (mem_zpowers u)
    exact huW (he.symm ▸ huR))
  have hgRT : R.map (MulAut.conj g).toMonoidHom ≤ T := by
    apply map_le_iff_le_comap.mpr
    refine sup_le ?_ (zpowers_le.mpr (hUT hguU))
    intro w hw
    exact hUT (hWU ((mem_normalizer_iff.mp hgW w).mp hw))
  obtain ⟨x,hx,hpoint⟩ := sylow_subgroup_fusion T hTX hzT hzcentral hunique
    R (hRU.trans hUT) g hgRT
  have hc : x⁻¹*g ∈ centralizer (R : Set G) := by
    intro r hr
    have hh := hpoint r hr
    calc
      r*(x⁻¹*g) = x⁻¹*(x*r*x⁻¹)*g := by group
      _ = x⁻¹*(g*r*g⁻¹)*g := by rw [hh]
      _ = (x⁻¹*g)*r := by group
  have hcX : x⁻¹*g ∈ X := hmax R hWR hRU (centralizer_le_normalizer _ hc)
  simpa only [mul_inv_cancel_left] using X.mul_mem hx hcX

/-- The literal maximal-subgroup quotient has unique fixed cosets for
all surviving elements of U. The kernel is the whole subgroup W. -/
theorem maximal_normalizer_fixed_cosets {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {X : Subgroup G} (hTX : (T : Subgroup G) ≤ X)
    {z : G} (hzT : z ∈ (T : Subgroup G))
    (hzcentral : ∀ t ∈ (T : Subgroup G), Commute z t)
    (hunique : ∃! q : G ⧸ X, z • q = q)
    (U W : Subgroup G) (hUT : U ≤ T) (hXU : X ≤ normalizer (U : Set G))
    (hWU : W ≤ U)
    (hmax : ∀ R : Subgroup G, W < R → R ≤ U → normalizer (R : Set G) ≤ X) :
    let N := normalizer (W : Set G)
    let f := QuotientGroup.mk' (W.subgroupOf N)
    ∀ v ∈ (U.subgroupOf N).map f, v ≠ 1 →
      ∃! q : (N ⧸ W.subgroupOf N) ⧸ (X.subgroupOf N).map f, v • q = q := by
  dsimp only
  intro v hv hv1
  obtain ⟨u,hu,rfl⟩ := hv
  have huW : u.val ∉ W := by
    intro hh
    exact hv1 ((QuotientGroup.eq_one_iff _).mpr hh)
  have huX : u ∈ X.subgroupOf (normalizer (W : Set G)) := hTX (hUT hu)
  apply unique_map_of_surjective _ (QuotientGroup.mk'_surjective _)
    (by
      rw [QuotientGroup.ker_mk']
      exact comap_mono (hWU.trans (hUT.trans hTX))) huX
  apply unique_of_transporter huX
  intro g hg
  exact transporter_mem_of_maximal_normalizers T hTX hzT hzcentral hunique U W
    hUT hXU hWU hmax u.val g.val hu huW g.property hg

/-- Choose the source maximal W between a central seed and a subgroup
with prescribed normalizer. Its proper overgroups in U have no escaping normalizers. -/
theorem exists_maximal_normalizer_escape (X U Z : Subgroup G)
    (hX : X ≠ ⊤) (hZU : Z ≤ U) (hZ : Z ≤ center G)
    (hNU : normalizer (U : Set G) = X) :
    ∃ W : Subgroup G, Z ≤ W ∧ W < U ∧ ¬ normalizer (W : Set G) ≤ X ∧
      ∀ R : Subgroup G, W < R → R ≤ U → normalizer (R : Set G) ≤ X := by
  classical
  have hNZ : normalizer (Z : Set G) = ⊤ := by
    let : Z.Normal := ⟨by
      intro z hz g
      rw [mem_center_iff.mp (hZ hz) g,mul_inv_cancel_right]
      exact hz⟩
    exact normalizer_eq_top Z
  have hstart : Z ≤ Z ∧ Z ≤ U ∧ ¬ normalizer (Z : Set G) ≤ X := by
    refine ⟨le_rfl,hZU,?_⟩
    rw [hNZ]
    exact fun hh => hX (top_unique hh)
  obtain ⟨W,_,hW⟩ := Finite.exists_le_maximal
    (p := fun W : Subgroup G => Z ≤ W ∧ W ≤ U ∧ ¬ normalizer (W : Set G) ≤ X) hstart
  have hWU : W < U := lt_of_le_of_ne hW.prop.2.1 (by
    intro he
    exact hW.prop.2.2 (he ▸ hNU.le))
  refine ⟨W,hW.prop.1,hWU,hW.prop.2.2,?_⟩
  intro R hWR hRU
  by_contra hR
  exact (not_le_of_gt hWR) (hW.2 ⟨hW.prop.1.trans hWR.le,hRU,hR⟩ hWR.le)

end UniqueFixedCoset
