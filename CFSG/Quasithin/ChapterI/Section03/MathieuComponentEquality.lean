module
public import CFSG.Quasithin.ChapterI.Section03.MathieuOvercomponent
public import CFSG.Quasithin.ChapterI.Section03.MathieuCentralCubic
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleModels

/-!
# Equality of the original central cubic Mathieu component

A full M₂₂ cover centralizes every odd prime core of rank at most two,
and then the whole odd core. Its odd-E orbit is therefore ordinary. Proper
containment gives a faithful involution on the literal central quotient.
The original central cubic excludes the remaining Lie models by their
multipliers and McL by its local three-rank. Thus the original seed equals
the containing component, including when the induced quotient action is trivial.

Without a small-core premise the result exhibits an actual odd prime core
of rank at least three; A.1.28 then bounds the ambient two-rank by three.
The literal Hall application is MathieuGeneration.HallFaithfulness.CubicResolution.
Source: Aschbacher--Smith 4.2.13, printed p.612; A.1.9 and A.1.28,
pp.21 and 26; the covering comparisons in MathieuCentralCubic.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.MathieuPumpup

private def centerQuotientCongr {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) : (P ⧸ center P) ≃* (Q ⧸ center Q) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr e ⟨z,hz⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

/-- The small odd-prime-core bounds suffice for the full Mathieu cover to centralize the odd core. -/
theorem cover_centralizes_oddCore_of_core_rank
    {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* Sporadic.Mathieu.M22)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (pCore p G) ≤ 2) :
    B ≤ centralizer (pPrimeCore 2 G : Set G) := by
  have hpcores (p : ℕ) [Fact p.Prime] (hp : Odd p) :
      B ≤ centralizer (pCore p G : Set G) := by
    have ha := mathieu_cover_small_odd_action e hp pCore_isPGroup
      (hr p Fact.out hp)
      ((MulAut.conjNormal : G →* MulAut (pCore p G)).comp B.subtype)
    intro b hb
    rw [← MulAut.conjNormal_ker_eq_centralizer (pCore p G)]
    exact DFunLike.congr_fun ha ⟨b,hb⟩
  let S : Sylow 2 B := Classical.choice inferInstance
  let R := (S : Subgroup B).map B.subtype
  have hR : R ≤ centralizer (pPrimeCore 2 G : Set G) :=
    ChapterA.centralizes_oddCore_of_centralizes_odd_pCores R (S.isPGroup'.map B.subtype)
      (fun p _ hp => (map_subtype_le _).trans (hpcores p hp))
  apply perfect_le_of_normalizes_of_odd_relIndex B _ R le_normalizer_of_normal hR
  have he : R.subgroupOf B = (S : Subgroup B) := comap_map_eq_self_of_injective B.subtype_injective _
  rw [he]
  exact Nat.not_even_iff_odd.mp (fun hh => S.not_dvd_index hh.two_dvd)

/-- Small odd cores force equality with the original full central cubic residual. -/
theorem central_cubic_orbit_eq_of_core_rank
    {G : Type*} [Group G] [Finite G]
    (hqt : IsQuasithin G) (hkg : IsKGroup KnownSimple.IsKnownSimple G)
    (t : G) (ht : orderOf t = 2) (D : Subgroup G)
    (hD : IsComponentIn D (centralizer ({t} : Set G)))
    (eD : (D ⧸ center D) ≃* Sporadic.Mathieu.M22)
    (c : center G) (hc : orderOf c = 3) (hcD : (c : G) ∈ D)
    (hE : (componentOrbit D (oddELayer G)).IsTwoComponent)
    (hinv : (componentOrbit D (oddELayer G)).map (MulAut.conj t).toMonoidHom =
      componentOrbit D (oddELayer G))
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (pCore p G) ≤ 2) :
    D = componentOrbit D (oddELayer G) := by
  let E := componentOrbit D (oddELayer G)
  let := hD.quasisimple
  have hDE : D ≤ E := le_componentOrbit D _
  have hEc : E ≤ centralizer (pPrimeCore 2 G : Set G) :=
    iSup_conjugates_le_of_le_normalizer D (oddELayer G) _
      (cover_centralizes_oddCore_of_core_rank D eD hr)
      (by rw [normalizer_eq_top]; exact le_top)
  have hcomp : IsComponent G E := hE.isComponent_of_centralizes_oddCore hEc
  let := hcomp.2
  have hm := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
    (hqt.subgroup E) (hkg.subgroup E)
  let C := centralizer ({t} : Set G)
  let B := D.subgroupOf C
  have hmap : B.map C.subtype = D := map_subgroupOf_eq_of_le hD.1
  have hBE : B.map C.subtype ≤ E := hmap ▸ hDE
  have hcase := fixed_component_eq_or_involution t ht B hD.2 E hcomp hBE hinv
  rw [hmap] at hcase
  rcases hcase with heq | ⟨a,ha,hact,haq⟩
  · exact heq
  have hf := fixed_component_in_overgroup t B hD.2 E hBE a hact
  rw [hmap] at hf
  obtain ⟨hQ,heQ⟩ := fixed_mathieu_central_quotient a (D.subgroupOf E) hf
    ((centerQuotientCongr (subgroupOfEquivOfLe hDE)).trans eD)
  let z : E := ⟨c,hDE hcD⟩
  have hz : z ∈ center E := mem_center_iff.mpr
    (fun y => Subtype.ext (mem_center_iff.mp c.property y))
  have hz3 : orderOf (⟨z,hz⟩ : center E) = 3 :=
    (orderOf_coe _).symm.trans ((orderOf_coe z).symm.trans ((orderOf_coe c).trans hc))
  have h3 : 3 ∣ Nat.card (center E) := hz3 ▸ orderOf_dvd_natCard (⟨z,hz⟩ : center E)
  exact (no_central_cubic_mathieu_fixed_component (hqt.subgroup E) h3
    ⟨_,haq,_,hQ,heQ⟩ hm).elim

/-- Either the original residual exhausts its orbit, or a specific large odd core obstructs promotion. -/
theorem central_cubic_orbit_eq_or_large_odd_core
    {G : Type*} [Group G] [Finite G]
    (hqt : IsQuasithin G) (hkg : IsKGroup KnownSimple.IsKnownSimple G)
    (t : G) (ht : orderOf t = 2) (D : Subgroup G)
    (hD : IsComponentIn D (centralizer ({t} : Set G)))
    (eD : (D ⧸ center D) ≃* Sporadic.Mathieu.M22)
    (c : center G) (hc : orderOf c = 3) (hcD : (c : G) ∈ D)
    (hE : (componentOrbit D (oddELayer G)).IsTwoComponent)
    (hinv : (componentOrbit D (oddELayer G)).map (MulAut.conj t).toMonoidHom =
      componentOrbit D (oddELayer G)) :
    D = componentOrbit D (oddELayer G) ∨
      (primeRank 2 G ≤ 3 ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 < primeRank p (pCore p G)) := by
  by_cases hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (pCore p G) ≤ 2
  · exact Or.inl (central_cubic_orbit_eq_of_core_rank hqt hkg t ht D hD eD c hc hcD hE hinv hr)
  push Not at hr
  obtain ⟨p,hp,ho,hr⟩ := hr
  let : Fact p.Prime := ⟨hp⟩
  have hl := (isQuasithin_iff_twoLocalPrimeRank.mp hqt) p hp ho
  exact Or.inr ⟨(ChapterA.lemma_A_1_28_group ho hl hr).1,p,hp,ho,hr⟩
end CFSG.Quasithin.ChapterI.MathieuPumpup
