module

public import Theory.GroupTheory.CommonNormalSubgroup
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The escaping module conjugate in C.5.5

The orbit of a block module under M₀ cannot lie in O₂(H): otherwise its
commutator bound makes that orbit a nontrivial subgroup of R normal in
⟨M₀,H⟩. If every conjugate commuted with the original module, the orbit
would be abelian. Transitivity on the block modules and the source
centralizer equality would then put the orbit back in O₂(H).

These are the group-theoretic steps of Aschbacher–Smith C.5.5, printed
p.155. The preceding block construction supplies the module family and
its commutator and centralizer identities; no escaping conjugate is assumed.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] {ι : Type*}

/-- Transitivity places every original block module in the M₀-orbit span
of the selected one. We retain the source's right-conjugation convention. -/
theorem modules_le_orbitSpan (U : ι → Subgroup G) (i₀ : ι)
    (T M : Subgroup G) (hTM : T ≤ M)
    (horbit : ∀ i, ∃ t ∈ T, U i = (U i₀).map (MulAut.conj t⁻¹).toMonoidHom) :
    (⨆ i, U i) ≤ conjugateSpanBy (U i₀) M := by
  apply iSup_le
  intro i
  obtain ⟨t, ht, hi⟩ := horbit i
  rw [hi, conjugateSpanBy_eq_iSup_conj]
  exact le_iSup (fun t : M => (U i₀).map (MulAut.conj (t : G)).toMonoidHom)
    ⟨t⁻¹, M.inv_mem (hTM ht)⟩

/-- The first assertion of C.5.5, using the actual module orbit and the
absence of a common normal subgroup from C.5.2. -/
theorem orbitSpan_not_le_twoCore (M H K R Q T : Subgroup G)
    (U : ι → Subgroup G) (i₀ : ι)
    (hH : H ≤ K ⊔ M) (hRM : R ≤ M) (hTM : T ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hno : ∀ N : Subgroup G, N ≤ R → (N.subgroupOf (M ⊔ H)).Normal → N = ⊥)
    (hU : U i₀ ≠ ⊥) (hUR : U i₀ ≤ R)
    (horbit : ∀ i, ∃ t ∈ T, U i = (U i₀).map (MulAut.conj t⁻¹).toMonoidHom)
    (hcomm : ⁅Q, K⁆ ≤ ⨆ i, U i) :
    ¬ conjugateSpanBy (U i₀) M ≤ Q := by
  have hUV := modules_le_orbitSpan U i₀ T M hTM horbit
  have hUne : (⨆ i, U i) ≠ ⊥ := by
    intro he
    exact hU (eq_bot_iff.mpr (he ▸ le_iSup U i₀))
  exact not_le_of_no_common_normal_subgroup M H K R Q (⨆ i, U i)
    (conjugateSpanBy (U i₀) M) hH (hRM.trans le_sup_left) hno hUV hUne
    (conjugateSpanBy_le hUR hMR) (le_normalizer_conjugateSpanBy _ _) hcomm

/-- C.5.5 supplies an actual element of M₀ whose right conjugate does not
commute with the selected original module. The centralizer inclusion is
the C.5.4(4) identity restricted to R. -/
theorem exists_noncommuting_conjugate (M H K R Q T : Subgroup G)
    (U : ι → Subgroup G) (i₀ : ι)
    (hH : H ≤ K ⊔ M) (hRM : R ≤ M) (hTM : T ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hno : ∀ N : Subgroup G, N ≤ R → (N.subgroupOf (M ⊔ H)).Normal → N = ⊥)
    (hU : U i₀ ≠ ⊥) (hUR : U i₀ ≤ R)
    (horbit : ∀ i, ∃ t ∈ T, U i = (U i₀).map (MulAut.conj t⁻¹).toMonoidHom)
    (hcomm : ⁅Q, K⁆ ≤ ⨆ i, U i)
    (hcentralizer : R ⊓ centralizer ((⨆ i, U i : Subgroup G) : Set G) ≤ Q) :
    ∃ x ∈ M, ⁅U i₀, (U i₀).map (MulAut.conj x⁻¹).toMonoidHom⁆ ≠ ⊥ := by
  classical
  by_contra hn
  push Not at hn
  have hV : conjugateSpanBy (U i₀) M ≤ centralizer (U i₀ : Set G) := by
    rw [conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro x
    have hc := hn x.val⁻¹ (M.inv_mem x.property)
    rw [inv_inv, commutator_comm] at hc
    exact commutator_eq_bot_iff_le_centralizer.mp hc
  have hab : IsMulCommutative (conjugateSpanBy (U i₀) M) :=
    (conjugateSpanBy_commutative_iff _ _).mpr (le_centralizer_iff.mp hV)
  have hVU : conjugateSpanBy (U i₀) M ≤
      centralizer ((⨆ i, U i : Subgroup G) : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr hab).trans
      (centralizer_le (modules_le_orbitSpan U i₀ T M hTM horbit))
  exact orbitSpan_not_le_twoCore M H K R Q T U i₀ hH hRM hTM hMR hno
    hU hUR horbit hcomm ((le_inf (conjugateSpanBy_le hUR hMR) hVU).trans hcentralizer)

/-- The conjugator chosen in C.5.5 lies outside any subgroup that
normalizes the original abelian module, in particular outside Baum(R). -/
theorem noncommuting_conjugator_not_mem (U S : Subgroup G)
    [IsMulCommutative U] (hSU : S ≤ normalizer (U : Set G)) {x : G}
    (hx : ⁅U, U.map (MulAut.conj x⁻¹).toMonoidHom⁆ ≠ ⊥) : x ∉ S := by
  intro hxs
  have he := mem_normalizer_iff_map_conj_eq.mp (hSU (S.inv_mem hxs))
  change U.map (MulAut.conj x⁻¹).toMonoidHom = U at he
  rw [he] at hx
  exact hx (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff_isMulCommutative.mpr inferInstance))

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
