module
public import Theory.SpecificGroups.SymmetricSeven.NoFiftySix
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.KernelNormalizer
public import Theory.Mathieu.M23.QuasithinGeometry.FourNormalizers.Geometry

/-!
# The seven-point obstruction in the native M₂₃ action

A subgroup of order 896 containing a Sylow two-subgroup has orbit one or
seven on the point fixed by that Sylow. In the seven-point case, the native
sixteen-point orbit forces this orbit to be the marked Witt heptad. Its
pointwise kernel has order sixteen and lies in the Sylow, so restriction
would give a permutation group of order 56 on the heptad, which is impossible.
Sylow conjugacy transports the resulting fixed point to any prescribed Sylow.

The orbit calculation reuses the native point table and the argument of
`Theory.Mathieu.M23.QuasithinGeometry.SylowEscape`. Its actual Cartan consumer
restricts the whole witness to the M₂₂ point stabilizer.
Source: Aschbacher--Smith, Proposition 7.3.4, printed p.699.
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M23Cartan
open Sporadic.Mathieu M23Geometry FusionCertificate

private theorem heptad_no_896 (J : Subgroup heptadStabilizer)
    (T : Sylow 2 heptadStabilizer) (hT : (T : Subgroup heptadStabilizer) ≤ J)
    (hJ : Nat.card J = 896) : False := by
  have hk : heptadKernel ≤ J := (heptadKernel_isTwoGroup.le_sylow_of_normal T).trans hT
  have hc := (heptadKernel.subgroupOf J).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv, heptadKernel_card, hJ] at hc
  change 16 * heptadAction.ker.relIndex J = 896 at hc
  rw [relIndex_ker] at hc
  exact SymmetricSeven.subgroup_card_ne_fiftysix (J.map heptadAction) (by omega)

private theorem no_heptad_overgroup (H : Subgroup M23) (S : Sylow 2 M23)
    (hSH : (S : Subgroup M23) ≤ H) (hcard : Nat.card H = 896)
    (B : Finset (Fin 23)) (hB : B ∈ m23Blocks) (hHB : H ≤ stabilizer M23 B) : False := by
  obtain ⟨g,hg⟩ := exists_smul_omega_eq hB
  let e : stabilizer M23 B ≃* heptadStabilizer := (stabilizerEquivStabilizer hg.symm).symm
  let J := (H.subgroupOf (stabilizer M23 B)).map e.toMonoidHom
  let T := (S.subtype (hSH.trans hHB)).mapSurjective (f := e.toMonoidHom) e.surjective
  have hTJ : (T : Subgroup heptadStabilizer) ≤ J := map_mono (comap_mono hSH)
  have hJ : Nat.card J = 896 := by
    rw [card_map_of_injective e.injective, Nat.card_congr (subgroupOfEquivOfLe hHB).toEquiv]
    exact hcard
  exact heptad_no_896 J T hTJ hJ

private def orbitOneIndex : Fin 23 → Fin 128 :=
  ![0, 0, 8, 16, 24, 0, 0, 32, 40, 48, 56, 0, 0, 64, 72, 80, 88, 0, 0, 96, 104, 112, 120]

private theorem orbit_one (a : Fin 23) (ha : a ∉ FourNormalizers.fixedSet) :
    pointTable (orbitOneIndex a) 1 = a := by
  revert ha a
  decide +kernel

private theorem invariant_seven_eq (B : Finset (Fin 23)) (hc : B.card = 7)
    (hP : subgroup ≤ stabilizer M23 B) : B = FourNormalizers.fixedSet := by
  have hclosed {a : Fin 23} (ha : a ∈ B) (i : Fin 128) : pointTable i a ∈ B :=
    mem_stabilizer_finset'.mp
      (hP (show (⟨perm i,rawSubgroup_le (perm_mem i)⟩ : M23) ∈ subgroup from perm_mem i)) ha
  have hsub : B ⊆ FourNormalizers.fixedSet := by
    intro a ha
    by_contra han
    have h1 : (1 : Fin 23) ∈ B := by
      let g : M23 := ⟨perm (orbitOneIndex a),rawSubgroup_le (perm_mem _)⟩
      have hg : g ∈ subgroup := perm_mem _
      have hb := mem_stabilizer_finset'.mp (hP (subgroup.inv_mem hg)) ha
      have he : g • (1 : Fin 23) = a := orbit_one a han
      rw [← he, inv_smul_smul] at hb
      exact hb
    have houtside : FourNormalizers.fixedSetᶜ ⊆ B := by
      intro b hb
      have hn : b ∉ FourNormalizers.fixedSet := Finset.mem_compl.mp hb
      rw [← orbit_one b hn]
      exact hclosed h1 _
    have hd := Finset.card_le_card houtside
    have hn : FourNormalizers.fixedSetᶜ.card = 16 := by decide +kernel
    rw [hc,hn] at hd
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hc]; decide +kernel)

private theorem marked_fixes_point (H : Subgroup M23) (hS : subgroup ≤ H)
    (hcard : Nat.card H = 896) : H ≤ stabilizer M23 (0 : Fin 23) := by
  classical
  have hfixed : subgroup ≤ stabilizer M23 (0 : Fin 23) := by
    intro x hx
    obtain ⟨i,hi⟩ := exists_perm ⟨x.val,hx⟩
    change x.val 0 = 0
    rw [←hi]
    exact (by decide +kernel : ∀ i : Fin 128, pointTable i 0 = 0) i
  let K := stabilizer H (0 : Fin 23)
  have hi : (subgroup.subgroupOf H).index = 7 := by
    have hc := (subgroup.subgroupOf H).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv, subgroup_card,hcard] at hc
    omega
  have hK : K.index ∣ 7 := by
    rw [←hi]
    exact index_dvd_of_le (show subgroup.subgroupOf H ≤ K from fun x hx => hfixed hx)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hK with h | h
  · have ht : K = ⊤ := index_eq_one.mp h
    intro x hx
    exact (show (⟨x,hx⟩ : H) ∈ K from ht ▸ mem_top _)
  · let B := (orbit H (0 : Fin 23)).toFinite.toFinset
    have hc : B.card = 7 := by
      change (orbit H (0 : Fin 23)).toFinite.toFinset.card = 7
      rw [← Set.ncard_eq_toFinset_card]
      exact (index_stabilizer H (0 : Fin 23)).symm.trans h
    have hHB : H ≤ stabilizer M23 B := by
      intro g hg
      apply mem_stabilizer_finset'.mpr
      intro x hx
      have hx' : x ∈ orbit H (0 : Fin 23) := by simpa only [B, Set.Finite.mem_toFinset] using hx
      obtain ⟨a,rfl⟩ := mem_orbit_iff.mp hx'
      have hh : g • (a • (0 : Fin 23)) ∈ orbit H (0 : Fin 23) :=
        ⟨(⟨g,hg⟩ : H) * a, mul_smul _ _ _⟩
      simpa only [B, Set.Finite.mem_toFinset] using hh
    have he := invariant_seven_eq B hc (hS.trans hHB)
    exact (no_heptad_overgroup H sylow hS hcard B (he ▸ FourNormalizers.fixedSet_mem) hHB).elim

/-- A Sylow overgroup of order 896 fixes a natural point of M₂₃. -/
theorem seven_overgroup_preserves_point (H : Subgroup M23) (S : Sylow 2 M23)
    (hS : (S : Subgroup M23) ≤ H) (hcard : Nat.card H = 896) :
    ∃ a : Fin 23, H ≤ stabilizer M23 a := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 S sylow
  let e := MulAut.conj g
  have hmap : (S : Subgroup M23).map e.toMonoidHom = subgroup := congrArg Sylow.toSubgroup hg
  have hH := marked_fixes_point (H.map e.toMonoidHom) (hmap ▸ map_mono hS)
    (by rw [card_map_of_injective e.injective]; exact hcard)
  refine ⟨g⁻¹ • (0 : Fin 23), ?_⟩
  intro x hx
  have hh := hH (mem_map_of_mem e.toMonoidHom hx)
  change (g*x*g⁻¹) • (0 : Fin 23) = 0 at hh
  have he := congrArg (fun a : Fin 23 => g⁻¹ • a) hh
  change x • (g⁻¹ • (0 : Fin 23)) = g⁻¹ • 0
  simpa only [mul_smul, inv_smul_smul] using he
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M23Cartan
