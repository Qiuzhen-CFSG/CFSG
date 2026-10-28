module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.ResidualCentralizer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.ResidualNine

/-!
# The residual centralizer in the swapping branch at the original G,T

An element of O²(H) centralizing the generated elementary sixteen fixes an
elementary eight in U. Its induced automorphism squares to one, whereas its
image modulo O₂(H) has exponent three. Thus it lies in O₂(H).

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open DimensionFour.SplitImage
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_swapping_residual_centralizer (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (q : QuaternionCentralProductData F.U) (a : G) (ha : a ^ 2 = 1) (hout : a ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj a).toMonoidHom =
      q.right.map F.U.subtype) :
    (pResidual 2 F.H).map F.H.subtype ⊓
      centralizer ((zpowers a ⊔ ⁅F.U, zpowers a⁆ : Subgroup G) : Set G) ≤ F.H.pCoreIn 2 := by
  let A := zpowers a ⊔ ⁅F.U, zpowers a⁆
  let D := ⁅F.U, zpowers a⁆
  obtain ⟨hD, he, hc⟩ := q.elementary_sixteen_of_swap F.U a ha hout hswap
  have hDU : D ≤ F.U := by
    change ⁅F.U, zpowers a⁆ ≤ F.U
    rw [hD]
    exact inf_le_left
  let : IsElementaryAbelian 2 A := he
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
    (inclusion (show D ≤ A from le_sup_right)) (inclusion_injective _)
  have hDa : a ∈ normalizer (D : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((show x ∈ F.U ⊓ centralizer ({a} : Set G) from hD ▸ hx).2)
  have hDc : Nat.card D = 8 := by
    have h := card_sup_zpowers_of_normalizing_involution D a ha (fun hm => hout (hDU hm)) hDa
    have heq : D ⊔ zpowers a = A := sup_comm _ _
    rw [heq, hc] at h
    omega
  let E := D.subgroupOf F.U
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hDU
  have hEc : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hDU).toEquiv).trans hDc
  have hres := (source_residual_nine d setup structural alternatives F hne hZ hcard).1
  let : IsElementaryAbelian 3 ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) := hres
  rintro x ⟨⟨y,hy,rfl⟩,hcA⟩
  change (y : G) ∈ centralizer (A : Set G) at hcA
  have hfix (v : F.U) (hv : v ∈ E) : F.uAction y v = v := by
    apply Subtype.ext
    change (y : G) * (v : G) * (y : G)⁻¹ = v
    rw [← hcA v (show (v : G) ∈ A from mem_sup_right hv), mul_inv_cancel_right]
  have hsquare : (F.uAction y) ^ 2 = 1 := q.square_eq_one_of_fixes_eight E hEc _ hfix
  have hy2 : y ^ 2 ∈ pCore 2 F.H := by
    rw [← source_uhat_kernel d setup structural alternatives F hZ]
    change quotientAut (center F.U) (F.uAction (y ^ 2)) = 1
    rw [map_pow, hsquare, map_one]
  let π := QuotientGroup.mk' (pCore 2 F.H)
  have hp2 : (π y) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (y ^ 2)).mpr hy2
  have hp3 : (π y) ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem π hy)
  have hp1 : π y = 1 := by
    rw [pow_succ (π y) 2, hp2, one_mul] at hp3
    exact hp3
  exact mem_map_of_mem F.H.subtype ((QuotientGroup.eq_one_iff y).mp hp1)

theorem source_quaternion_generators_of_outer_index (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (q : QuaternionCentralProductData F.U)
    (g a : G) (hgL : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (haX : a ∈ F.X g) (ha : a ^ 2 = 1) (hout : a ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj a).toMonoidHom =
      q.right.map F.U.subtype)
    (hthree : (F.H.pCoreIn 2).relIndex
      ((pResidual 2 F.H).map F.H.subtype ⊓
        normalizer ((zpowers a ⊔ ⁅F.U, zpowers a⁆ : Subgroup G) : Set G)) = 3) :
    Nonempty (QuaternionGenerators (zpowers a ⊔ ⁅F.U, zpowers a⁆)
      ((pResidual 2 F.H).map F.H.subtype) ((T : Subgroup G) ⊓ L)) := by
  apply source_quaternion_generators_of_outer_indices d setup structural alternatives
    F hne hZ hcard q g a hgL hgP hgH haX ha hout hswap _ hthree
  exact (inf_le_inf_right _ inf_le_left).trans
    (source_swapping_residual_centralizer d setup structural alternatives F hne hZ hcard
      q a ha hout hswap)
end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
