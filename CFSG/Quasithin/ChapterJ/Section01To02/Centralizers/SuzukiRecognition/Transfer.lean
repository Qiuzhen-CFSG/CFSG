module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.RecognitionReduction
public import Theory.GroupTheory.CentralInvolutionResidualTransfer
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The transfer step for the J.2.9 residual

The two-residual is taken in the actual centralizer of s. The seven-group
lies in it, so its commutators with T_s do too. The derived-subgroup
identification of T_s puts its normalizer in L. The earlier calculation
C_L(s)=T_s B_7 then makes that normalizer centralize S_0. Burnside fusion
and transfer, using the projection of the actual internal product
T_s=S_0×S_1, separate S_0 from O²(C_G(s)).

The local product, derived subgroup and involution-centrality inputs are
explicit here. They must be supplied by the J.2.3 Suzuki two-group geometry;
the Sylow input is J.2.7(10). No residual separation is assumed.

Source: Aschbacher–Smith, J.2.9, printed p.438 (PDF p.449).
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

theorem Ls_le_Gs : c.Ls ≤ c.Gs := map_subtype_le _

/-- Normality is relative to C_G(s), not to G. -/
theorem Gs_normalizes_Ls : c.Gs ≤ normalizer (c.Ls : Set G) := by
  have h := (pResidual 2 c.Gs).le_normalizer_map c.Gs.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h

theorem B7_normalizes_Ts : c.B7 ≤ normalizer (c.Ts : Set G) := by
  apply (le_inf (c.B7_le.trans d.ru1.steinberg.normalized)
    (c.B7_le_Gs.trans le_normalizer)).trans
  exact inf_normalizer_le_normalizer_inf

theorem S1_le_Ts : c.S1 ≤ c.Ts :=
  le_normalizer_iff_commutator_le_left.mp c.B7_normalizes_Ts

/-- The literal moving factor belongs to the two-residual before recognition. -/
theorem S1_le_Ls : c.S1 ≤ c.Ls :=
  (commutator_mono le_rfl c.B7_le_Ls).trans
    (le_normalizer_iff_commutator_le_right.mp
      (inf_le_right.trans c.Gs_normalizes_Ls))

/-- The derived subgroup calculation in the local product forces every
Sylow normalizer in C_G(s) to centralize S₀. -/
theorem sylow_normalizer_centralizes_S0
    (hderived : (_root_.commutator c.Ts).map c.Ts.subtype = d.V)
    (hCL : d.L ⊓ c.Gs = c.Ts ⊔ c.B7)
    (hcentral : c.S0 ≤ centralizer (c.Ts : Set G)) :
    c.Gs ⊓ normalizer (c.Ts : Set G) ≤ centralizer (c.S0 : Set G) := by
  have hNL : normalizer (c.Ts : Set G) ≤ d.L := by
    rw [d.ru1.normalizer_eq, ← hderived]
    exact normalizer_le_normalizer_characteristic_image c.Ts (_root_.commutator c.Ts)
  have hle : c.Gs ⊓ normalizer (c.Ts : Set G) ≤ d.L ⊓ c.Gs :=
    le_inf (inf_le_right.trans hNL) inf_le_left
  rw [hCL] at hle
  exact hle.trans (sup_le (le_centralizer_iff.mp hcentral)
    (le_centralizer_iff.mp inf_le_right))

/-- Generalized Thompson transfer in J.2.9, with an actual marked internal
product and the literal Sylow subgroup of C_G(s). -/
theorem disjoint_S0_Ls_of_local_product
    [IsElementaryAbelian 2 c.S0]
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (e : P ≃* c.S0 × c.S1)
    (he : ∀ x : P, ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G))
    (hderived : (_root_.commutator c.Ts).map c.Ts.subtype = d.V)
    (hCL : d.L ⊓ c.Gs = c.Ts ⊔ c.B7)
    (hcentral : c.S0 ≤ centralizer (c.Ts : Set G))
    (hinvol : ∀ x : P, x ^ 2 = 1 → (x : c.Gs) ∈ centralizer (P : Set c.Gs)) :
    Disjoint c.S0 c.Ls := by
  let : CommGroup c.S0 := IsMulCommutative.instCommGroup
  let character : P →* c.S0 := (MonoidHom.fst _ _).comp e.toMonoidHom
  apply disjoint_def.mpr
  intro a ha hres
  by_contra hne
  let a0 : c.S0 := ⟨a, ha⟩
  let x : P := e.symm (a0, 1)
  have hxG : ((x : c.Gs) : G) = a := by simpa [x, a0] using he x
  have hx : x ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    change (e (e.symm (a0, 1))) ^ 2 = 1
    rw [e.apply_symm_apply]
    exact Prod.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 c.S0) a0) (by simp)
  have hfix : normalizer (P : Set c.Gs) ≤ centralizer ({(x : c.Gs)} : Set c.Gs) := by
    intro n hn
    have hnG : (n : G) ∈ normalizer (c.Ts : Set G) := by
      change n ∈ normalizer ((P : Subgroup c.Gs) : Set c.Gs) at hn
      rw [hP, ← subgroupOf_normalizer_eq (show c.Ts ≤ c.Gs from inf_le_right)] at hn
      exact hn
    have hcomm := c.sylow_normalizer_centralizes_S0 hderived hCL hcentral
      ⟨n.property, hnG⟩ a ha
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change (n : G) * ((x : c.Gs) : G) = ((x : c.Gs) : G) * (n : G)
    simpa only [hxG] using hcomm.symm
  have hdetect : character x ≠ 1 := by
    intro hz
    have heq : a0 = 1 := by simpa [character, x] using hz
    exact hne (congrArg Subtype.val heq)
  apply P.not_mem_twoResidual_of_central_involution hinvol character x hx hfix hdetect
  obtain ⟨r, hr, heq⟩ := mem_map.mp hres
  have hrx : r = (x : c.Gs) := Subtype.ext (heq.trans hxG.symm)
  exact hrx ▸ hr

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
