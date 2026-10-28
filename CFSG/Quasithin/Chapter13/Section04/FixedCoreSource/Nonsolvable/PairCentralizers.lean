module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullWeightComparison
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.Generation

/-!
# Relative centralizers for the two escaping parabolics

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
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V P Q : Subgroup G}

/-- If a point centralizer were contained in the pair join, its actual
faithful component would be normal there and generate the join with T.
Thus the other parabolic could not move that point. -/
theorem pair_point_centralizer_eq
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTP : (T : Subgroup G) ≤ P) (hTQ : (T : Subgroup G) ≤ Q)
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eQ : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3)) (hne : P ≠ Q)
    (hiP : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiQ : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (Q : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hPz : P ⋖ centralizer ({z} : Set G))
    (hQz : ¬ Q ≤ centralizer ({z} : Set G))
    (K : Subgroup G) (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z} : Set G)))
    (hfK : K ∈ MainForward.faithfulLocalComponents T) :
    (P ⊔ Q) ⊓ centralizer ({z} : Set G) = P := by
  let X := P ⊔ Q
  rcases hPz.eq_or_eq (le_inf le_sup_left hPz.le) inf_le_right with he | he
  · exact he
  · have hHX : centralizer ({z} : Set G) ≤ X := he ▸ inf_le_left
    have hKX := hK.1.trans hHX
    have hTK := (h1332 K hfK).1
    have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun H _ _ => ChapterA.Section02.theoremA_knownSimple (G := H))
      (fun H _ _ => ChapterA.Section02.theoremC_knownSimple (G := H)) h₀.qtke T hstar
    have horb : componentOrbit K (T : Subgroup G) = K :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer K _ K le_rfl hTK)
        (le_componentOrbit K _)
    have hlocal := Amalgam.original_pair_local D m hTP hTQ eP eQ hne hiP hiQ
    have hcore : pCore 2 X ≠ ⊥ := by
      intro hh
      exact hlocal.1 (by change (pCore 2 X).map X.subtype = ⊥; rw [hh,Subgroup.map_bot])
    obtain ⟨Y,hY,hXY⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot X hcore
    have hYeq := hu.normalizer_unique Y hY
      ((sup_le hKX (hTP.trans le_sup_left)).trans hXY)
    change Y = normalizer (componentOrbit K (T : Subgroup G) : Set G) at hYeq
    rw [horb] at hYeq
    have hXN : X ≤ normalizer (K : Set G) := hXY.trans_eq hYeq
    let : (K.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXN
    have htop : (⊤ : Subgroup K).IsCComponent := by
      simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le (le_refl K) hK.1
    let e := subgroupOfEquivOfLe hKX
    have htopX : (⊤ : Subgroup (K.subgroupOf X)).IsCComponent := by
      simpa only [map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using
        htop.map_equiv e.symm
    have hcomp : (K.subgroupOf X).IsCComponent := by
      simpa only [←MonoidHom.range_eq_map,range_subtype] using
        htopX.map_subtype (inferInstance : (K.subgroupOf X).Normal).isSubnormal
    have hgen := (Amalgam.original_pair_component_is_residual h₀ D m h1332
      hTP hTQ eP eQ hne hiP hiQ (K.subgroupOf X) hcomp).2
    rw [map_subgroupOf_eq_of_le hKX] at hgen
    exact (hQz (le_sup_right.trans (hgen.le.trans
      (sup_le hK.1 (Solvable.original_sylow_le_centralizer hz))))).elim

private theorem escaping_parabolic_moves_other
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z w : V) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z ≠ w)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (Q : Subgroup G)
    (hQ : Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hQw : Q ≤ centralizer ({w.val} : Set G)) : ¬ Q ≤ centralizer ({z.val} : Set G) := by
  classical
  intro hQz
  have hfix := m.central_four_fixed_of_escape h structural w hw1 hwT Q hQw hQ.1.2
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
theorem escaping_pair_residual_centralizers
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  have hQz := escaping_parabolic_moves_other h structural D m z w hz1 hw1 hzw hzT hwT Q hQ hQw.le
  have hPw := escaping_parabolic_moves_other h structural D m w z hw1 hz1 hzw.symm hwT hzT P hP hPz.le
  have hne : P ≠ Q := fun he => hQz (he ▸ hPz.le)
  have hiP := escaping_residual_fixed_index h structural m z hz1 hzT P hP hPz.le
  have hiQ := escaping_residual_fixed_index h structural m w hw1 hwT Q hQ hQw.le
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
