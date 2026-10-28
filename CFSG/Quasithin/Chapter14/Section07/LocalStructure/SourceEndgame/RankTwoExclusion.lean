module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.FixedPoint
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Excluding rank-two U₀ on the original source configuration

With the generation identities R = VU₀ and [R,L] ≤ V and the source
centralization R ≤ C_G(Q), the kernel of the original qL centralizes R.
The cardinal bound |U₀| ≤ 4 and V ∩ U₀ = V₁ make any proper extension
U₀ > V₁ a four-group and make R have order sixteen. The proved splitting
and fixed-point contradiction give U₀ = V₁.

The consumer uses genuine CriticalFusion.Source.Data, its original fixed
space, and exactly the fixed-modulo-V₁ premise of 14.7.68(2). The marked Sylow image is constructed from T normalizing L. Generation
and centralization premises remain to be discharged in
the 14.7.71–72 source argument; this is not a proof of the whole lemma.
No legacy CriticalFusion.Setup.Input is imported.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076,
combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

theorem source_U₀_eq_point_of_generated_four
    (earlier : d.ModuleSeparation)
    (R : Subgroup G) [IsElementaryAbelian 2 R]
    (hVR : V ≤ R) (hU₀R : d.U₀ ≤ R)
    (hU₀T : d.U₀ ≤ (T : Subgroup G))
    (hNR : L ≤ normalizer R)
    (hfour : Nat.card d.U₀ = 4) (hRcard : Nat.card R = 16)
    (hcore : L.pCoreIn 2 ≤ Q T L)
    (hRQ : R ≤ centralizer (Q T L : Set G))
    (P : Sylow 2 BinaryLinearThree.Group)
    (hP : (d.qL.comp (Subgroup.inclusion
      (inf_le_right : (T : Subgroup G) ⊓ L ≤ L))).range = (P : Subgroup _))
    (hcomm : ⁅R,L⁆ ≤ V)
    (hL₁L : F.Li L 1 ≤ L)
    (hU₀fix : d.U₀ ≤ centralizer (F.Li L 1 : Set G))
    (hVfix : V ⊓ centralizer (F.Li L 1 : Set G) = F.Vi 1)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hTR : (T : Subgroup G) ≤ normalizer R)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H)
    (hLH : ¬ L ≤ F.H) : d.U₀ = F.Vi 1 := by
  have hk : ∀ l ∈ d.qL.ker, (l : G) ∈ centralizer (R : Set G) := by
    intro l hl
    rw [d.qL_ker] at hl
    exact (le_centralizer_iff.mp hRQ) (hcore hl)
  have hle := four_space_obstruction L (F.Li L 1) (T : Subgroup G) F.H R V (F.Vi 1)
    ((T : Subgroup G) ⊓ L) d.U₀ hVR inf_le_right inf_le_left hU₀T hU₀R
    ((F.invariant 1).trans d.H_normalizes_U₀) hNR T.isPGroup' hfour hRcard
    d.qL d.qL_surjective hk d.natural.chosen.normalizes d.naturalCoordinates
    d.naturalCoordinates_bijective d.naturalCoordinates_equivariant P hP hcomm
    d.point_le_U₀ hL₁L hU₀fix hVfix hTL hTR ?_ hLH
  · rw [← d.seed_inf_U₀ earlier]
    exact le_antisymm (le_inf hle le_rfl) inf_le_right
  · intro c hc hc1 hcT
    let v : F.U := ⟨c,d.U₀_le_U hc⟩
    apply h68 v hc hc1
    intro t
    have hh := d.conjugationSection.equivariant ⟨t,F.invariant 1 t.property⟩ v
    change d.action ⟨t,F.invariant 1 t.property⟩ (d.conjugationSection.coordinates v).toAdd = _
    rw [← hh]
    congr 2
    apply Subtype.ext
    change (t : G) * c * (t : G)⁻¹ = c
    rw [hcT t t.property, mul_inv_cancel_right]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

theorem source_U₀_eq_point_of_generation
    (earlier : d.ModuleSeparation)
    (R : Subgroup G) [IsElementaryAbelian 2 R]
    (hR : R = V ⊔ d.U₀)
    (hbound : Nat.card d.U₀ ≤ 4)
    (hU₀T : d.U₀ ≤ (T : Subgroup G))
    (hNR : L ≤ normalizer R)
    (hcore : L.pCoreIn 2 ≤ Q T L)
    (hRQ : R ≤ centralizer (Q T L : Set G))
    (hcomm : ⁅R,L⁆ ≤ V)
    (hL₁L : F.Li L 1 ≤ L)
    (hU₀fix : d.U₀ ≤ centralizer (F.Li L 1 : Set G))
    (hVfix : V ⊓ centralizer (F.Li L 1 : Set G) = F.Vi 1)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hTR : (T : Subgroup G) ≤ normalizer R)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H)
    (hLH : ¬ L ≤ F.H) : d.U₀ = F.Vi 1 := by
  by_contra hne
  have hpoint : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hindex : 2 ≤ (F.Vi 1).relIndex d.U₀ := by
    have hzero := ((F.Vi 1).subgroupOf d.U₀).index_ne_zero_of_finite
    have hone : (F.Vi 1).relIndex d.U₀ ≠ 1 := by
      intro hh
      exact hne (le_antisymm (relIndex_eq_one.mp hh) d.point_le_U₀)
    change (F.Vi 1).relIndex d.U₀ ≠ 0 at hzero
    omega
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (F.Vi 1) d.U₀ bot_le d.point_le_U₀
  simp only [relIndex_bot_left, hpoint] at hh
  have hfour : Nat.card d.U₀ = 4 := by omega
  have hVR : V ≤ R := hR ▸ le_sup_left
  have hU₀R : d.U₀ ≤ R := hR ▸ le_sup_right
  have hNV : d.U₀ ≤ normalizer V := by
    apply le_trans ?_ (centralizer_le_normalizer (V : Set G))
    intro u hu v hv
    exact congrArg (fun r : R => (r : G))
      (mul_comm (⟨v,hVR hv⟩ : R) ⟨u,hU₀R hu⟩)
  have hRcard : Nat.card R = 16 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes V d.U₀ hNV
    rw [d.seed_inf_U₀ earlier, ← hR, hfour, hpoint, ← F.last, F.card 3 (by decide)] at hh
    norm_num at hh
    omega
  obtain ⟨P,hP⟩ := d.source_sylow_image hTL
  exact hne (source_U₀_eq_point_of_generated_four d earlier R hVR hU₀R hU₀T hNR
    hfour hRcard hcore hRQ P hP hcomm hL₁L hU₀fix hVfix hTL hTR h68 hLH)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
