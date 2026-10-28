module
public import Theory.Mathieu.M23.OrdinarySource
-- Internal continuation of the native certificate: reuse its private kernel
-- enumeration without exposing those implementation tables in the public API.
import all Theory.Mathieu.M23.OrdinarySource
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.HeptadAutomorphisms
public import Theory.GroupTheory.PerfectHalfOrderImage
public import Theory.GroupTheory.EvenCentralizerFixedInvolution
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.GroupTheory.PerfectMovedElementaryRank
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# The moved-subgroup normalizer obstruction in M₂₃

An even centralizer of a Sylow-normalized subgroup supplies an involution.
The order of its perfect centralizer, together with an elementary normal
section of order at least eight and a two-core quotient divisible by 168,
forces equality with that centralizer. Its fourteen noncentral kernel elements
form one orbit, certified by short words in the existing native generators.
Thus the section is the whole heptad kernel. Its normalizer is the larger
heptad stabilizer and cannot normalize the original involution centralizer.

The comparison uses the actual moved normalizer, not just a carrier name.
The Chapter 10 point-control consumer supplies that restriction before taking
the central quotient. Source: Aschbacher--Smith 10.2.9, printed pp.750--751;
the intrinsic M₂₃ geometry is H.14.2 and GLS3 Table 5.3d.
-/

public section
open Subgroup
open scoped commutatorElement
noncomputable section
namespace Sporadic.Mathieu.M23Geometry.InvolutionCentralizer
private def orbitWords : Fin 16 → Fin 4 → List (Fin 7) :=
![
![[],[],[],[]],
![[],[4,5,4],[6,6],[5,4]],
![[4,5,4],[],[5,4,4],[4,4]],
![[4,5,4,6],[6],[5,4,4,6],[4,4,6]],
![[6],[5,4,4],[],[5,5]],
![[6,6],[5,4,4,6],[6],[5,5,6]],
![[],[],[],[]],
![[5,4,4],[6,6],[4,5,4],[4,5]],
![[6,5],[4],[5],[]],
![[4,4],[4,5],[5,5],[5]],
![[4,5],[4,4],[5,4],[4]],
![[4],[6,6,5],[6,6,4],[4,6]],
![[5,5],[5,4],[4,4],[5,6]],
![[5],[6,6,4],[6,6,5],[4,5,4]],
![[6,4],[5],[4],[5,5,4]],
![[5,4],[5,5],[4,5],[4,6,6]]
]
private def actor : List (Fin 7) → representativeCentralizer
  | [] => 1
  | j :: w => involutionCentralizerGenerator j * actor w
private def actorPerm : List (Fin 7) → Equiv.Perm (Fin 23)
  | [] => 1
  | j :: w => involutionCentralizerGeneratorPerm j * actorPerm w
private theorem actor_coe (w : List (Fin 7)) : (actor w).val.val = actorPerm w := by
  induction w with
  | nil => rfl
  | cons j w ih => change _ * (actor w).val.val = _; rw [ih]; rfl
private theorem orbit_basis (i : Fin 16) (hi : i ≠ 0) (hi6 : i ≠ 6) (j : Fin 4) :
    actor (orbitWords i j) * wordElement (words i) * (actor (orbitWords i j))⁻¹ = basis j := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (actor (orbitWords i j)).val.val
    ((wordElement (words i)).val.val ((actor (orbitWords i j)).val.val.symm x)) = _
  rw [actor_coe, wordElement_apply, basis_apply]
  revert i j x
  decide +kernel

private theorem kernel_map : kernel.map representativeCentralizer.subtype = heptadKernelAmbient := by
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨toHeptad g,hg,rfl⟩
  · rintro ⟨g,hg,rfl⟩
    exact ⟨kernelInclusion ⟨g,hg⟩,hg,rfl⟩

private theorem core_eq_kernel : pCore 2 representativeCentralizer = kernel := by
  apply map_injective representativeCentralizer.subtype_injective
  change representativeCentralizer.pCoreIn 2 = _
  rw [kernel_map, fixedHeptad_centralizer_core_eq involutionRepresentative_order,
    fixedHeptad_involutionRepresentative]
  exact heptadPointwiseKernel_omega

theorem normal_elementary_large_eq_kernel (E : Subgroup representativeCentralizer)
    [E.Normal] (hp : IsPGroup 2 E) (hc : 8 ≤ Nat.card E) : E = kernel := by
  have hE : E ≤ kernel := core_eq_kernel ▸ (show E ≤ pCore 2 representativeCentralizer from
    le_sSup ⟨inferInstance,hp⟩)
  have hn : ¬ E ≤ center representativeCentralizer := by
    intro h
    have hh := card_le_of_le h
    rw [representative_center_card] at hh
    omega
  obtain ⟨x,hx,hxz⟩ := Set.not_subset.mp hn
  obtain ⟨i,hi⟩ := kernelWord_surjective ⟨x,hE hx⟩
  have hiv : wordElement (words i) = x := congrArg Subtype.val hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hxz (hiv ▸ (one_mem _))
  have hi6 : i ≠ 6 := by
    rintro rfl
    rw [word_six] at hiv
    exact hxz (hiv ▸ (show markedInvolution ∈ center representativeCentralizer from
      mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.property)))
  apply le_antisymm hE
  intro y hy
  obtain ⟨k,hk⟩ := kernelWord_surjective ⟨y,hy⟩
  rw [← show wordElement (words k) = y from congrArg Subtype.val hk]
  apply word_mem
  intro j
  rw [← orbit_basis i hi0 hi6 j,hiv]
  exact (inferInstance : E.Normal).conj_mem x hx _
end Sporadic.Mathieu.M23Geometry.InvolutionCentralizer

namespace Sporadic.Mathieu.M23Geometry
open InvolutionCentralizer Theory.GroupTheory.PerfectHalfOrderImage

theorem centralizer_odd_of_moved_normalizer
    (S : Sylow 2 M23) (B E : Subgroup M23)
    (hSB : (S : Subgroup M23) ≤ normalizer (B : Set M23))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B)
    (hBE : B ≤ normalizer (E : Set M23))
    (hc : 8 ≤ Nat.card E) (h168 : 168 ∣ Nat.card (B ⧸ pCore 2 B))
    (hN : normalizer (E : Set M23) ≤ normalizer (B : Set M23)) :
    ¬ 2 ∣ Nat.card (centralizer (B : Set M23)) := by
  intro heven
  obtain ⟨z,hz,h⟩ := Theory.GroupTheory.exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup M23) S.isPGroup' hSB heven
  let K := centralizer ({z} : Set M23)
  have hBK : B ≤ K := le_sup_left.trans h
  let := InvolutionCentralizer.isPerfect_of_involution hz
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (involutions_isConj z involutionRepresentative hz involutionRepresentative_order)
  let a := MulAut.conj g
  have hmap : K.map a.toMonoidHom = representativeCentralizer := by
    have haz : a z = involutionRepresentative := hg
    ext x
    rw [mem_map_equiv,mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    rw [←a.injective.eq_iff]
    simp only [map_mul,MulEquiv.apply_symm_apply,haz]
  have hKcard : Nat.card K = 2688 := by
    rw [←card_map_of_injective (f := a.toMonoidHom) a.injective (K := K),hmap]
    exact involutionRepresentative_centralizer_card
  have hcore : E ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes
    (by let := hE; exact IsElementaryAbelian.isPGroup 2 E) hEB hBE
  have hcorecard : 8 ≤ Nat.card (pCore 2 B) := by
    have hh := card_le_of_le hcore
    rw [pCoreIn,card_map_of_injective B.subtype_injective] at hh
    exact hc.trans hh
  have hBcard : 1344 ≤ Nat.card B := by
    have hh := Nat.mul_le_mul hcorecard (Nat.le_of_dvd (Nat.card_pos) h168)
    rw [←index_eq_card,card_mul_index] at hh
    exact hh
  have hidx : (B.subgroupOf K).index ≤ 2 := by
    have hh := (B.subgroupOf K).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv,hKcard] at hh
    nlinarith
  have htop : B.subgroupOf K = ⊤ := by
    have hh := commutator_le_of_index_le_two (B.subgroupOf K) hidx
    rw [Group.IsPerfect.commutator_eq_top] at hh
    exact top_unique hh
  have hBK' : B = K := le_antisymm hBK (subgroupOf_eq_top.mp htop)
  have hEKa : E.map a.toMonoidHom ≤ representativeCentralizer := by
    rw [←hmap]
    exact map_mono (hEB.trans hBK)
  let F := (E.map a.toMonoidHom).subgroupOf representativeCentralizer
  have hn : representativeCentralizer ≤ normalizer (E.map a.toMonoidHom : Set M23) := by
    rw [←hmap,←hBK']
    exact (map_mono hBE).trans (le_normalizer_map _)
  let : F.Normal := normal_subgroupOf_of_le_normalizer hn
  have hFc : 8 ≤ Nat.card F := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEKa).toEquiv,card_map_of_injective a.injective]
    exact hc
  have hFp : IsPGroup 2 F := by
    let := hE
    exact ((IsElementaryAbelian.isPGroup 2 E).map a.toMonoidHom).comap_of_injective
      representativeCentralizer.subtype representativeCentralizer.subtype_injective
  have hFk := normal_elementary_large_eq_kernel F hFp hFc
  have hEk : E.map a.toMonoidHom = heptadKernelAmbient := by
    have hh := congrArg (map representativeCentralizer.subtype) hFk
    rwa [map_subgroupOf_eq_of_le hEKa,kernel_map] at hh
  have hN' := map_mono (f := a.toMonoidHom) hN
  rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq,hEk,hBK',hmap,
    heptadKernelAmbient_normalizer,
    self_normalizing_of_involution involutionRepresentative_order] at hN'
  have hh := card_le_of_le hN'
  rw [heptadStabilizer_card,involutionRepresentative_centralizer_card] at hh
  norm_num at hh


/-- Every involutory automorphism fixing the original actor is trivial. -/
theorem eq_one_of_fixes_moved_normalizer
    (S : Sylow 2 M23) (B E : Subgroup M23)
    (hSB : (S : Subgroup M23) ≤ normalizer (B : Set M23))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B)
    (hBE : B ≤ normalizer (E : Set M23))
    (hc : 8 ≤ Nat.card E) (h168 : 168 ∣ Nat.card (B ⧸ pCore 2 B))
    (hN : normalizer (E : Set M23) ≤ normalizer (B : Set M23))
    (a : MulAut M23) (ha : a^2=1) (hf : ∀ x ∈ B, a x=x) : a=1 := by
  obtain ⟨x,hx⟩ := m23_conj_surjective a
  have hx2 : x^2=1 := MulAut.conj_injective_of_center_eq_bot m23_center_eq_bot (by
    rw [map_pow,hx,ha,map_one])
  have hxc : x ∈ centralizer (B : Set M23) := by
    intro b hb
    have hh := hf b hb
    rw [←hx,MulAut.conj_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  by_contra hne
  have hxn : x ≠ 1 := fun he => hne (by rw [←hx,he,map_one])
  exact centralizer_odd_of_moved_normalizer S B E hSB hE hEB hBE hc h168 hN
    (by simpa only [Subgroup.orderOf_mk,orderOf_eq_prime_iff.mpr ⟨hx2,hxn⟩]
      using orderOf_dvd_natCard (⟨x,hxc⟩ : centralizer (B : Set M23)))

end Sporadic.Mathieu.M23Geometry
