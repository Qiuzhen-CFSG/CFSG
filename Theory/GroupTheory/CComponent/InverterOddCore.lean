module
public import Theory.GroupTheory.CComponent.CentralInvolution
public import Theory.GroupTheory.CComponent.TwoComponent
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.SolvableRadical.Transport

/-! A C-component with quasisimple two-core quotient is ordinary or has trivial
odd core when the original actor centralizes the ambient two-core and inverts
the ambient odd core. In the nonordinary branch its commutators lie in the
radical; perfect central-cover uniqueness makes the actor trivial modulo the
two-core, so inversion kills the intrinsic odd core. This repairs the Fitting
step in Aschbacher–Smith 2.4.25, printed p.542, retaining the actual actor. -/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem IsCComponent.component_or_oddCore_eq_bot_of_inverter
    {K : Subgroup G} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (z : G) (hcentral : ∀ b ∈ pCore 2 G, b * z = z * b)
    (hinv : ∀ b ∈ pPrimeCore 2 G, z * b * z⁻¹ = b⁻¹) :
    IsComponent G K ∨ pPrimeCore 2 K = ⊥ := by
  by_cases hcomp : IsComponent G K
  · exact Or.inl hcomp
  right
  have hcomm : ⁅K,zpowers z⁆ ≤ solvableRadical G := by
    rcases hK.commutator_le_radical_or_eq_iSup_conjugates (zpowers z) with hh|hh
    · exact hh
    · have hKC : K ≤ centralizer (fittingSubgroup G : Set G) :=
        ((le_iSup_conjugates K (zpowers z)).trans_eq hh.symm).trans
          ((commutator_mono le_top le_rfl).trans
            (commutator_top_le_centralizer_fitting z hcentral hinv))
      exact (hcomp ⟨hK.subnormal,hK.isQuasisimple_of_fitting_centralizes
        (le_centralizer_iff.mp hKC)⟩).elim
  let r := QuotientGroup.mk' (solvableRadical G)
  have hzC : r z ∈ centralizer (K.map r : Set (G ⧸ solvableRadical G)) := by
    have hh : ⁅K.map r,(zpowers z).map r⁆ = ⊥ := by
      rw [←map_commutator]
      exact (map_eq_bot_iff _).mpr (by simpa only [r,QuotientGroup.ker_mk'] using hcomm)
    rw [commutator_comm] at hh
    exact (commutator_eq_bot_iff_le_centralizer.mp hh)
      (mem_map_of_mem r (mem_zpowers z))
  have hzN : z ∈ normalizer (K : Set G) := by
    rw [←normalizer_cComponent_quotient hK (solvableRadical G)]
    exact Subgroup.centralizer_le_normalizer _ hzC
  let a : MulAut K := K.normalizerMonoidHom ⟨z,hzN⟩
  let q := QuotientGroup.mk' (pCore 2 K)
  let t := QuotientGroup.mk' (center (K ⧸ pCore 2 K))
  let := hK.perfect
  have hq : q.comp a.toMonoidHom = q := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq t
      (by rw [QuotientGroup.ker_mk'])
    ext k
    change t (q (a k)) = t (q k)
    apply mul_inv_eq_one.mp
    rw [←map_inv,←map_mul,←map_inv,←map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply IsQuasisimple.solvableRadical_le_center
    apply map_solvableRadical_le_of_surjective q (QuotientGroup.mk'_surjective _)
    apply mem_map_of_mem
    have hc : a k * k⁻¹ ∈ (solvableRadical G).subgroupOf K := by
      change z * (k:G) * z⁻¹ * (k:G)⁻¹ ∈ solvableRadical G
      exact hcomm (commutator_comm K (zpowers z) ▸
        commutator_mem_commutator (mem_zpowers z) k.property)
    let : Group.IsSolvable ((solvableRadical G).subgroupOf K) :=
      Group.isSolvable_of_isSolvable_injective
        (f := K.subtype.subgroupComap (solvableRadical G))
        (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun t : solvableRadical G => (t:G)) he)))
    exact (le_solvableRadical ((solvableRadical G).subgroupOf K)
      inferInstance inferInstance) hc
  have hdis : Disjoint (pCore 2 K) (pPrimeCore 2 K) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=K)).exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p:=2) (G:=K)).pow_left n
  apply eq_bot_iff.mpr
  intro k hk
  have hai : a k = k⁻¹ := Subtype.ext (hinv k
    (hK.subnormal.pPrimeCore_map_le (mem_map_of_mem K.subtype hk)))
  have he : q (k ^ 2) = 1 := by
    have hh := congrArg (fun f : K →* (K ⧸ pCore 2 K) => f k) hq
    change q (a k) = q k at hh
    rw [hai,map_inv] at hh
    calc
      q (k^2) = q k * q k := by rw [map_pow,pow_two]
      _ = (q k)⁻¹ * q k := congrArg (fun w => w * q k) hh.symm
      _ = 1 := inv_mul_cancel _
  have hk2 : k ^ 2 = 1 := disjoint_def.mp hdis
    ((QuotientGroup.eq_one_iff _).mp he) ((pPrimeCore 2 K).pow_mem hk 2)
  have hord : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one hk2
  have hodd : Nat.Coprime 2 (orderOf k) :=
    (pPrimeCore_coprime_card (p:=2) (G:=K)).of_dvd_right
      ((pPrimeCore 2 K).orderOf_dvd_natCard hk)
  exact mem_bot.mpr (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hodd hord dvd_rfl))
end Subgroup
