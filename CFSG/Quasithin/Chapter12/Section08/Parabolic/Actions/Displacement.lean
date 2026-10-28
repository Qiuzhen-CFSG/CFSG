module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import CFSG.Quasithin.Chapter12.Section08.Actions.Comparison
public import Theory.GroupTheory.CommutatorQuotientHom

/-!
# Displacement on the marked parabolic quotients

We prove 12.8.9(4) from the fixed-space assertion of (3), using the literal
map into H/V₁. The fixed-space input is related explicitly to the actual
quotient of I₂ by E. We also construct the source homomorphism X → W/E,
identify its kernel, and express its inverse image of Z(U)E/E as ambient
commutator membership. The natural-module calculation identifying this
inverse image with Z(U)^g E remains a separate obligation.

The two X-action kernels below use the previously constructed actions on
U/Z(U) and the image of U in H/V₁. The easy inclusions are proved from
12.8.4(2); their reverse inclusions require the source Frattini argument.
No assertion of 12.8.9(5) or (6) is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.9(3–6), printed p.853, PDF p.870.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The actual X-action on Ũ. -/
def xTildeAction (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2) :
    F.X g →* MulAut (F.tilde F.U) :=
  F.tildeAction (F.X g) F.U (F.X_le_H g hg) (F.X_normalizes_U g hg)

/-- The actual X-action on Û = U/Z(U). -/
def xHatAction (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2) :
    F.X g →* MulAut F.Uhat :=
  F.uhatAction.comp (inclusion (F.X_le_H g hg))

def xTildeKernel (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2) : Subgroup G :=
  (F.xTildeAction g hg).ker.map (F.X g).subtype

def xHatKernel (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2) : Subgroup G :=
  (F.xHatAction g hg).ker.map (F.X g).subtype

/-- A pointwise fixed-vector criterion for the literal tilde action. -/
theorem xTildeAction_fixed_iff (F : InvariantFlag T V n) [IsMulCommutative V]
    (g : G) (hg : g ∈ F.Gi 2) (x : F.X g) (u : F.U) :
    F.xTildeAction g hg x (F.tildeMap F.U F.U_le_H u) =
      F.tildeMap F.U F.U_le_H u ↔ ⁅(x : G), (u : G)⁆ ∈ F.Vi 1 := by
  rw [xTildeAction, F.tildeAction_apply_map]
  rw [Subtype.ext_iff]
  change F.tildeProjection _ = F.tildeProjection _ ↔ _
  constructor
  · intro h
    have hm := QuotientGroup.eq_iff_div_mem.mp h
    change (x : G) * u * (x : G)⁻¹ / u ∈ F.Vi 1 at hm
    simpa only [commutatorElement_def, div_eq_mul_inv] using hm
  · intro h
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (x : G) * u * (x : G)⁻¹ / u ∈ F.Vi 1
    simpa only [commutatorElement_def, div_eq_mul_inv] using h

/-- A pointwise fixed-vector criterion for the literal central quotient. -/
theorem xHatAction_fixed_iff (F : InvariantFlag T V n)
    (g : G) (hg : g ∈ F.Gi 2) (x : F.X g) (u : F.U) :
    F.xHatAction g hg x (QuotientGroup.mk' (center F.U) u) =
      QuotientGroup.mk' (center F.U) u ↔ ⁅(x : G), (u : G)⁆ ∈ F.ZU := by
  change F.uhatAction _ (QuotientGroup.mk' (center F.U) u) = _ ↔ _
  rw [F.uhatAction_apply_mk]
  constructor
  · intro h
    refine ⟨_, QuotientGroup.eq_iff_div_mem.mp h, ?_⟩
    change (x : G) * u * (x : G)⁻¹ / u = ⁅(x : G), (u : G)⁆
    simp only [commutatorElement_def, div_eq_mul_inv]
  · intro h
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨z, hz, he⟩ := h
    have he' : z = F.uAction (inclusion (F.X_le_H g hg) x) u / u := by
      apply Subtype.ext
      change F.U.subtype z = (x : G) * u * (x : G)⁻¹ / u
      simpa only [commutatorElement_def, div_eq_mul_inv] using he
    exact he' ▸ hz

theorem mem_xTildeKernel (F : InvariantFlag T V n) [IsMulCommutative V]
    (g : G) (hg : g ∈ F.Gi 2) (x : G) :
    x ∈ F.xTildeKernel g hg ↔ x ∈ F.X g ∧ ∀ u ∈ F.U, ⁅x, u⁆ ∈ F.Vi 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, (F.mem_tildeAction_ker_iff (F.X g) F.U
      (F.X_le_H g hg) F.U_le_H (F.X_normalizes_U g hg) x).mp hx⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, (F.mem_tildeAction_ker_iff (F.X g) F.U
      (F.X_le_H g hg) F.U_le_H (F.X_normalizes_U g hg) ⟨x, hx⟩).mpr h, rfl⟩

theorem mem_xHatKernel (F : InvariantFlag T V n)
    (g : G) (hg : g ∈ F.Gi 2) (x : G) :
    x ∈ F.xHatKernel g hg ↔ x ∈ F.X g ∧ ∀ u ∈ F.U, ⁅x, u⁆ ∈ F.ZU := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, (F.mem_uhatAction_ker_iff
      (inclusion (F.X_le_H g hg) x)).mp hx⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, (F.mem_uhatAction_ker_iff
      (inclusion (F.X_le_H g hg) ⟨x, hx⟩)).mpr h, rfl⟩

/-- The easy inclusions in 12.8.9(5), from the source commutator bound
`[U,U] ≤ V₁` in 12.8.4(2). -/
theorem E_le_action_kernels (F : InvariantFlag T V n) [IsMulCommutative V]
    (hn : 1 ≤ n) (g : G) (hg : g ∈ F.Gi 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) :
    F.E g ≤ F.xTildeKernel g hg ∧ F.xTildeKernel g hg ≤ F.xHatKernel g hg := by
  constructor
  · intro e he
    apply (F.mem_xTildeKernel g hg e).mpr
    exact ⟨he.2, fun u hu => hcomm (commutator_mem_commutator he.1.1 hu)⟩
  · intro x hx
    obtain ⟨hxX, hx⟩ := (F.mem_xTildeKernel g hg x).mp hx
    exact (F.mem_xHatKernel g hg x).mpr ⟨hxX, fun u hu => F.point_le_ZU hn (hx u hu)⟩

/-- Pull back the actual fixed-space equality `C_{S/E}(u)=W/E` from (3).
Here S is literally W ⊔ X; no quotient or action convention is suppressed. -/
theorem fixedSpace_lift (F : InvariantFlag T V n) (L : Subgroup G) (g : G)
    (hUI : F.U ≤ F.I₂ L) (hXI : F.X g ≤ F.I₂ L)
    [(F.E g |>.subgroupOf (F.I₂ L)).Normal]
    (u : F.U)
    (hfixed :
      ((F.W ⊔ F.X g).subgroupOf (F.I₂ L)).map
          (QuotientGroup.mk' ((F.E g).subgroupOf (F.I₂ L))) ⊓
        centralizer ({QuotientGroup.mk' ((F.E g).subgroupOf (F.I₂ L))
          ⟨u, hUI u.property⟩} : Set ((F.I₂ L) ⧸ (F.E g).subgroupOf (F.I₂ L))) =
      (F.W.subgroupOf (F.I₂ L)).map
        (QuotientGroup.mk' ((F.E g).subgroupOf (F.I₂ L))))
    (s : G) (hs : s ∈ F.W ⊔ F.X g) (hc : ⁅s, (u : G)⁆ ∈ F.E g) : s ∈ F.W := by
  let I := F.I₂ L
  let q := QuotientGroup.mk' ((F.E g).subgroupOf I)
  have hsI : s ∈ I := (sup_le ((show F.W ≤ F.U from inf_le_left).trans hUI) hXI) hs
  let si : I := ⟨s, hsI⟩
  let ui : I := ⟨u, hUI u.property⟩
  have hcq : ⁅q si, q ui⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hc
  have hsq : q si ∈ (F.W.subgroupOf I).map q := by
    rw [← hfixed]
    refine ⟨⟨si, hs, rfl⟩, ?_⟩
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcq).symm
  have hpre : si ∈ ((F.W.subgroupOf I).map q).comap q := hsq
  rw [comap_map_eq, QuotientGroup.ker_mk'] at hpre
  have hEW : (F.E g).subgroupOf I ≤ F.W.subgroupOf I := fun _ he => he.1
  rwa [sup_eq_left.mpr hEW] at hpre

/-- Source 12.8.9(4). Its fixed-space premise is the ambient pullback of (3),
as proved by `fixedSpace_lift`; point containment comes from the actual flag. -/
theorem tilde_displacement (F : InvariantFlag T V n) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) (hn : 2 ≤ n)
    (g : G) (hgP : g ∈ F.P L)
    (hfixed : ∀ u ∈ F.U, u ∉ F.W → ∀ s ∈ F.W ⊔ F.X g,
      ⁅s, u⁆ ∈ F.E g → s ∈ F.W)
    (y : F.X g) (hy : (y : G) ∉ F.W) (a : F.tilde F.U)
    (ha : F.xTildeAction g (F.P_le_G₂ hn L hL hgP) y a = a) :
    (a : F.G₁tilde) ∈ F.tilde F.W := by
  obtain ⟨u, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H a
  have hc := (F.xTildeAction_fixed_iff g (F.P_le_G₂ hn L hL hgP) y u).mp ha
  have hpointE : F.Vi 1 ≤ F.E g := (F.le_seed 1).trans
    (F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L hL hgP))
  have huW : (u : G) ∈ F.W := by
    by_contra h
    exact hy (hfixed u u.property h y
      ((le_sup_right : F.X g ≤ F.W ⊔ F.X g) y.property) (hpointE hc))
  exact ⟨⟨u, F.U_le_H u.property⟩, huW, rfl⟩

/-- The literal commutator homomorphism used for the remaining assertion (6). -/
def parabolicCommutator (F : InvariantFlag T V n) (g : G)
    [((F.E g).subgroupOf F.W).Normal] (u : F.U)
    (hcomm : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.W)
    (habel : ⁅F.W ⊔ F.X g, F.W ⊔ F.X g⁆ ≤ F.E g) :
    F.X g →* F.W ⧸ (F.E g).subgroupOf F.W :=
  commutatorQuotientHom (F.X g) F.W (F.E g) u hcomm habel

/-- Clause (3) gives exactly E as the kernel of the source commutator map. -/
theorem parabolicCommutator_ker (F : InvariantFlag T V n) (g : G)
    [((F.E g).subgroupOf F.W).Normal] (u : F.U)
    (hcomm : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.W)
    (habel : ⁅F.W ⊔ F.X g, F.W ⊔ F.X g⁆ ≤ F.E g)
    (hfixed : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.E g ↔ x ∈ F.W) :
    (F.parabolicCommutator g u hcomm habel).ker = (F.E g).subgroupOf (F.X g) := by
  ext x
  rw [parabolicCommutator, mem_commutatorQuotientHom_ker, hfixed x x.property]
  exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩

/-- Exact formulation of the inverse image D in the printed proof. The
remaining natural-module calculation must identify this subgroup with Z(U)^g E. -/
theorem parabolicCommutator_preimage (F : InvariantFlag T V n) (g : G)
    [((F.E g).subgroupOf F.W).Normal] (u : F.U)
    (hcomm : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.W)
    (habel : ⁅F.W ⊔ F.X g, F.W ⊔ F.X g⁆ ≤ F.E g) (x : F.X g) :
    F.parabolicCommutator g u hcomm habel x ∈
      (F.ZU.subgroupOf F.W).map (QuotientGroup.mk' ((F.E g).subgroupOf F.W)) ↔
      ⁅(x : G), (u : G)⁆ ∈ F.ZU ⊔ F.E g :=
  commutatorQuotientHom_mem_image_iff (F.X g) F.W (F.E g) F.ZU u hcomm habel
    inf_le_left F.ZU_le_W x

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
