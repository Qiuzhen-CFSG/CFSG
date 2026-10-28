module

public import CFSG.Quasithin.Chapter13.Section09.SourceSetup
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.UniqueFixedCosetFusion
public import Theory.GroupTheory.CentralizerResidualFusion

/-!
# The two transfer arguments in Lemma 13.9.5

The first argument combines weak closure in `B`, the marked local classes,
and the unique-fixed-coset theorem to control fusion of the swapping
involution. Thompson transfer contradicts its local class avoiding `J(T)`.
The second argument uses the two ambient classes in `J(T)` and transports
the literal residual of `C_M(s)` into the residual of a conjugate centralizer.

These are conditional source steps. The six local classes come from
13.9.3--4; the normalizer action and centralizer residual analysis on
pp.970--971 must still supply the last theorem's two fusion premises.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.9.5, printed pp.970–971 (PDF pp.987–988).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conjugate_order {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

omit [Finite G] in
private theorem index_ne_two_of_simple [IsSimpleGroup G]
    (hnonabelian : ¬ IsMulCommutative G) (N : Subgroup G) (hN : N.Normal) :
    N.index ≠ 2 := by
  intro hindex
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · have hc : Nat.card G = 2 := by simpa only [hbot, index_bot] using hindex
    let : IsCyclic G := isCyclic_of_prime_card hc
    exact hnonabelian inferInstance
  · rw [htop, index_top] at hindex
    omega

/-- Thompson transfer places the original swapping involution in the index-two
subgroup `J(T)`; the ambient group is the original simple QTKE group. -/
theorem exists_conjugate_in_index_two
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G) (d : Configuration G)
    (J : Subgroup G)
    (hindex : (J.subgroupOf (d.T : Subgroup G)).index = 2)
    {s : G} (hsT : s ∈ (d.T : Subgroup G)) (hs : orderOf s = 2) :
    ∃ x ∈ J, IsConj s x := by
  let : IsSimpleGroup G := hG.simple
  obtain ⟨x, hxconj, hx⟩ := d.T.exists_isConj_mem_of_index_two
    (index_ne_two_of_simple hG.nonabelian) (J.subgroupOf (d.T : Subgroup G)) hindex
    ⟨s, hsT⟩ ((Subgroup.orderOf_coe (⟨s, hsT⟩ : d.T)).symm.trans hs)
  exact ⟨x, hx, hxconj⟩

/-- The weakly-closed branch's fixed-coset/transfer contradiction. The fusion
and local class hypotheses are the preceding 13.9.3--4 deductions. -/
theorem false_of_unique_fixed_coset
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G) (d : Configuration G)
    (J : Subgroup G) (hJT : J ≤ (d.T : Subgroup G))
    (hindex : (J.subgroupOf (d.T : Subgroup G)).index = 2)
    {z s : G} (hzT : z ∈ (d.T : Subgroup G))
    (hzcentral : ∀ a ∈ (d.T : Subgroup G), Commute z a)
    (hsT : s ∈ (d.T : Subgroup G)) (hs : orderOf s = 2)
    (hunique : ∃! q : G ⧸ d.M, z • q = q)
    (hsclass : ∀ m ∈ d.M, m * s * m⁻¹ ∉ J) : False := by
  obtain ⟨x, hx, hsx⟩ := exists_conjugate_in_index_two hG d J hindex hsT hs
  obtain ⟨m, hm, he⟩ := UniqueFixedCoset.sylow_fusion d.T d.sylow_le
    hzT hzcentral hunique hsT (hJT hx) hsx
  exact hsclass m hm (he.symm ▸ hx)

omit [Finite G] in
/-- If all local involution classes except `sᴹ` meet `B`, weak closure of `z`
in `B` gives local control of the entire ambient `z`-class in `M`. -/
theorem local_fusion_of_weakly_closed
    (M B : Subgroup G) {z s : G} (hz : orderOf z = 2) (hsz : ¬ IsConj z s)
    (hcover : ∀ x ∈ M, orderOf x = 2 →
      IsConj s x ∨ ∃ m ∈ M, m * x * m⁻¹ ∈ B)
    (hweak : ∀ x ∈ B, IsConj z x → x = z) :
    ∀ g : G, g * z * g⁻¹ ∈ M →
      ∃ m ∈ M, g * z * g⁻¹ = m * z * m⁻¹ := by
  intro g hg
  have hzg : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  rcases hcover _ hg ((conjugate_order hzg).symm.trans hz) with hs | hB
  · exact (hsz (hzg.trans hs.symm)).elim
  · obtain ⟨m, hm, hmem⟩ := hB
    have he := hweak _ hmem (hzg.trans (isConj_iff.mpr ⟨m, rfl⟩))
    refine ⟨m⁻¹, M.inv_mem hm, ?_⟩
    calc
      g * z * g⁻¹ = m⁻¹ * (m * (g * z * g⁻¹) * m⁻¹) * (m⁻¹)⁻¹ := by group
      _ = m⁻¹ * z * (m⁻¹)⁻¹ := by rw [he]

/-- Under `C_G(z)=T`, the weakly-closed alternative contradicts transfer.
The covering clause is supplied by the six marked classes and their intersections
with `B`, rather than by assuming ambient fusion control. -/
theorem not_weakly_closed_of_centralizer_eq
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G) (d : Configuration G)
    (J B : Subgroup G) (hJT : J ≤ (d.T : Subgroup G))
    (hindex : (J.subgroupOf (d.T : Subgroup G)).index = 2)
    {z s : G} (hzT : z ∈ (d.T : Subgroup G)) (hz : orderOf z = 2)
    (hzcentral : ∀ a ∈ (d.T : Subgroup G), Commute z a)
    (hsT : s ∈ (d.T : Subgroup G)) (hs : orderOf s = 2)
    (hC : centralizer ({z} : Set G) = (d.T : Subgroup G))
    (hsz : ¬ IsConj z s)
    (hsclass : ∀ m ∈ d.M, m * s * m⁻¹ ∉ J)
    (hcover : ∀ x ∈ d.M, orderOf x = 2 →
      IsConj s x ∨ ∃ m ∈ d.M, m * x * m⁻¹ ∈ B) :
    ¬ (∀ x ∈ B, IsConj z x → x = z) := by
  intro hweak
  have hunique := UniqueFixedCoset.unique_of_fusion_and_centralizer
    (d.sylow_le hzT) (hC ▸ d.sylow_le)
    (local_fusion_of_weakly_closed d.M B hz hsz hcover hweak)
  exact false_of_unique_fixed_coset hG d J hJT hindex hzT hzcentral hsT hs hunique hsclass

/-- The terminal contradiction of 13.9.5. Transfer fuses `s` to `t` or `z`;
the first choice contradicts the involutions in the literal local residual,
and the second contradicts the non-two-group centralizer of `s`. -/
theorem false_of_centralizer_residual_fusion
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G) (d : Configuration G)
    (J : Subgroup G)
    (hindex : (J.subgroupOf (d.T : Subgroup G)).index = 2)
    {z t s : G} (hsT : s ∈ (d.T : Subgroup G)) (hs : orderOf s = 2)
    (htz : ¬ IsConj t z) (hsz : ¬ IsConj z s)
    (hclasses : ∀ x ∈ J, orderOf x = 2 → IsConj t x ∨ IsConj z x)
    (hlocal : ∃ x ∈ (pResidual 2 (d.M ⊓ centralizer ({s} : Set G) : Subgroup G)).map
        (d.M ⊓ centralizer ({s} : Set G)).subtype, orderOf x = 2 ∧ IsConj z x)
    (hresidual : ∀ x ∈ (pResidual 2 (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype, orderOf x = 2 → IsConj t x) : False := by
  obtain ⟨x, hx, hsx⟩ := exists_conjugate_in_index_two hG d J hindex hsT hs
  rcases hclasses x hx ((conjugate_order hsx).symm.trans hs) with htx | hzx
  · exact Theory.GroupTheory.not_isConj_of_local_residual_classes
      (d.M ⊓ centralizer ({s} : Set G)) inf_le_right htz hlocal hresidual
      (hsx.trans htx.symm)
  · exact hsz (hzx.trans hsx.symm)

end CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth
