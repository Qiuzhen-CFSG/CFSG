module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.AlternatingLocals
public import Theory.GroupAction.SmallSylowCenter
public import Theory.Mathieu.M23.Properties.ElementarySylowFixers
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.HeptadAutomorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore

/-!
# The original M₂₃ exclusion in E.6.8

The actual inner source involution fixes the quotient Sylow subgroup pointwise.
Its center has order at most two, so every Sylow-preserving automorphism fixes
the involution and its actual heptad stabilizer. That local has characteristic
two and two-kernel quotient A₇. Its central component coordinates exclude
chi-zero blocks; E.6.7 places the complete lift in M. The source residual
condition then makes the involution fix the entire local of order 40320,
contrary to its native involution-centralizer order 2688.
The original component, quotient, full two-kernel and action are retained.

Source: Aschbacher–Smith E.6.8, printed p.248 (PDF p.259), GLS3 Table 5.3d.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
open _root_.Sporadic.Mathieu _root_.Sporadic.Mathieu.M23Geometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G} {K : GroupClass} {z : G}
open Chapter15.Section03.Candidates.ComponentStructure

theorem m23_excluded (h : HypothesisE61 K T M V)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hz : z ∈ sylowFixedSpace (T : Subgroup G) V)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (ha : TwoCentralInner α) (e : (L ⧸ pCore 2 L) ≃* M23) : False := by
  obtain ⟨S,hS⟩ := component_sylow_intersection h hU hL
  let R := S.mapSurjective (f := modelMap e) (modelMap_surjective e)
  let a := modelAction e α
  have ho : orderOf a = 2 :=
    (orderOf_injective (modelAction e) (modelAction_injective hL e) α).trans ha.2.1
  have hi : a ∈ (MulAut.conj (G := M23)).range := by
    obtain ⟨l,hl⟩ := ha.1
    exact ⟨modelMap e l, by dsimp [a]; rw [← hl, modelAction_conj]⟩
  have hfix := modelAction_fixed_sylow e hz α hα S hS
  obtain ⟨t,ht,hta,htR⟩ := Theory.GroupAction.exists_inner_involution_in_sylow_center
    m23_center_eq_bot R a ho hi hfix
  let B := fixedHeptad t
  have hB : B ∈ m23Blocks := fixedHeptad_mem ht
  let P := MulAction.stabilizer M23 B
  have hinv (b : MulAut M23) (hb : (R : Subgroup M23).map b.toMonoidHom = R) :
      P.map b.toMonoidHom = P :=
    fixedHeptad_stabilizer_map_of_aut_fix ht b
      (Theory.GroupAction.fixes_small_sylow_center R (m23_sylow_center_card_le_two R) t htR b hb)
  obtain ⟨_,hPc,f,hf,hk⟩ := heptad_stabilizer_local_structure hB (MulEquiv.refl P)
  have hplace := seedLift_le_M_of_central_coordinates h67 hU hL e m23_center_eq_bot S hS P
    hinv hPc
    (by
      intro C _ hC n q hqc hqs
      exact no_chiZero_central_coordinates_alternating hC (Or.inr rfl) f hf hk q hqc hqs)
  have hpf := modelAction_fixes_placed_seed hU hL e P hplace
    (primeToResidual_top_of_alternating_two_kernel (Or.inr rfl) f hf hk) hz.1 α hα
  have hle : P ≤ centralizer ({t} : Set M23) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have he : a x = x := hpf x hx
    rw [← hta] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hcardP : Nat.card P = 40320 := by
    obtain ⟨g,hg⟩ := exists_smul_omega_eq hB
    exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv).symm.trans
      heptadStabilizer_card
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (involutions_isConj involutionRepresentative t involutionRepresentative_order ht)
  have hm : (centralizer ({involutionRepresentative} : Set M23)).map
      (MulAut.conj g).toMonoidHom = centralizer ({t} : Set M23) := by
    ext x
    rw [mem_map_equiv,mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    rw [← (MulAut.conj g).injective.eq_iff]
    simp only [map_mul,MulEquiv.apply_symm_apply]
    rw [show MulAut.conj g involutionRepresentative = t from hg]
  have hcardC : Nat.card (centralizer ({t} : Set M23)) = 2688 := by
    rw [← hm,card_map_of_injective (MulAut.conj g).injective]
    exact involutionRepresentative_centralizer_card
  have hlecard := card_le_of_le hle
  rw [hcardP,hcardC] at hlecard
  omega
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
