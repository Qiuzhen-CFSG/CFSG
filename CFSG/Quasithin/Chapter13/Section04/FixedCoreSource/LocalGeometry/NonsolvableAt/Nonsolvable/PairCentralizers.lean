module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CentralFourAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFullSixQuotientAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.PairCentralizers
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullWeightComparison
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.Generation

/-!
# Relative centralizers for the two escaping parabolics: structure at the original group

For two distinct escaping central points, neither outside parabolic fixes
the other point. If their join contained a full point centralizer, local
uniqueness would make its faithful component normal in the join. The
proved component-generation theorem would then force the join to fix that
point, a contradiction. Maximality inside each point centralizer therefore
identifies both literal intersections with their selected parabolics.

The Sylow supplement identifies the centralizer of each residual fixed
line with that same parabolic. Its S₃ quotient gives both O^{3′} identities
and relative normality, exactly 13.4.7(c) for the P₂/P₄ application.
No whole-centralizer maximality or substituted residual is assumed.
Source: Aschbacher–Smith 13.4.12, printed pp.910–911.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/PairCentralizers` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V P Q : Subgroup G}

private theorem escaping_parabolic_moves_other_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z w : V) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z ≠ w)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (Q : Subgroup G)
    (hQ : Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hQw : Q ≤ centralizer ({w.val} : Set G)) : ¬ Q ≤ centralizer ({z.val} : Set G) := by
  classical
  intro hQz
  have hfix := m.central_four_fixed_of_escape_at h structural w hw1 hwT Q hQw hQ.1.2
  have hm : z.val ∈ zpowers w.val := hfix ▸
    (show z.val ∈ (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (Q : Set G) from
      ⟨⟨z.property,hzT⟩,fun q hq => mem_centralizer_singleton_iff.mp (hQz hq)⟩)
  let := D.elementary
  have ho : orderOf w.val = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian w.val w.property)
    (fun he => hw1 (Subtype.ext he))
  rw [mem_zpowers_iff_mem_range_orderOf,ho] at hm
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · exact hz1 (Subtype.ext (by simpa using he.symm))
  · exact hzw (Subtype.ext (by simpa using he.symm))

/-- Both original relative centralizers, their residual normality, and both
prime-to-three residual identities for two distinct escaping central points. -/
theorem escaping_pair_residual_centralizers_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (h1332 : Source1332OneTwo T)
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (z w : V) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z ≠ w)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hQ : Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPz : P ⋖ centralizer ({z.val} : Set G))
    (hQw : Q ⋖ centralizer ({w.val} : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eQ : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3))
    (K N : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hN : N ∈ Chapter1.cComponentsIn (centralizer ({w.val} : Set G)))
    (hfN : N ∈ MainForward.faithfulLocalComponents T) :
    let X := P ⊔ Q
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let R := (pResidual 2 P).map P.subtype
    let S := (pResidual 2 Q).map Q.subtype
    let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (R : Set G) : Subgroup G) : Set G)
    let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (S : Set G) : Subgroup G) : Set G)
    X ⊓ centralizer ({z.val} : Set G) = P ∧
    X ⊓ centralizer ({w.val} : Set G) = Q ∧
    C₁ = P ∧ C₂ = Q ∧ (R.subgroupOf C₁).Normal ∧ (S.subgroupOf C₂).Normal ∧
    (primeToResidual 3 C₁).map C₁.subtype = R ∧
    (primeToResidual 3 C₂).map C₂.subtype = S := by
  have hQz := escaping_parabolic_moves_other_at h structural D m z w hz1 hw1 hzw hzT hwT Q hQ hQw.le
  have hPw := escaping_parabolic_moves_other_at h structural D m w z hw1 hz1 hzw.symm hwT hzT P hP hPz.le
  have hne : P ≠ Q := fun he => hQz (he ▸ hPz.le)
  have hiP := escaping_residual_fixed_index_at h structural m z hz1 hzT P hP hPz.le
  have hiQ := escaping_residual_fixed_index_at h structural m w hw1 hwT Q hQ hQw.le
  rw [inf_eq_right.mpr hZV,Amalgam.omega_fixed_twoResidual P hP.1.1.2] at hiP
  rw [inf_eq_right.mpr hZV,Amalgam.omega_fixed_twoResidual Q hQ.1.1.2] at hiQ
  have h₁ := pair_point_centralizer_eq h₀ D m h1332 hP.1.1.2 hQ.1.1.2
    eP eQ hne hiP hiQ z.val hzT hPz hQz K hK hfK
  have h₂ := pair_point_centralizer_eq h₀ D m h1332 hQ.1.1.2 hP.1.1.2
    eQ eP hne.symm hiQ hiP w.val hwT hQw hPw N hN hfN
  rw [sup_comm Q P] at h₂
  obtain ⟨he₁,hn₁,hr₁⟩ := Solvable.residual_fixed_cubic_centralizer_of_intersection
    z.val hzT P (P ⊔ Q) hP.1.1.2 le_sup_left hPz.le h₁ eP
  obtain ⟨he₂,hn₂,hr₂⟩ := Solvable.residual_fixed_cubic_centralizer_of_intersection
    w.val hwT Q (P ⊔ Q) hQ.1.1.2 le_sup_right hQw.le h₂ eQ
  exact ⟨h₁,h₂,he₁,he₂,hn₁,hn₂,hr₁,hr₂⟩
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
