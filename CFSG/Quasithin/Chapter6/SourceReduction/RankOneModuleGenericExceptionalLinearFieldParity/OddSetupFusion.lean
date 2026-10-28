module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupNatural
public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import Theory.GroupTheory.TINormalizerControl
public import Theory.GroupTheory.AbelianConjugateSpan
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# Point fusion and the normalizer span in the odd-exponent setup

The actual natural action is transitive on nonidentity module elements.
Local TI then makes the point normalizer transitive on the nonidentity
points. The proved residual centralizer containment and I.6.1 extend TI
from N_G(O²(H)) to G. A.1.7 supplies an explicit transporter in N_G(Z₁)
for every conjugate of V meeting Z₁. Hence an abelian span under this
normalizer supplies the conjugate-commutation clause of F.8.1.

The final constructor derives reducedness, the Sylow-centralizer equality
and triviality of the generated two-core from the original FSU and the
maximal-local uniqueness theorem. It retains G.2.1, the abelian span,
the quotient-centralizer core bound and TI inside N_G(O²(H)). Their
source construction, including 5.1.16(2), remains with final assembly
owner qt-d-1222-linear-field-parity. No unconditional parity is claimed.

Source: Aschbacher–Smith 5.1.17, printed pp.640–641, with A.1.7(1),
I.6.1(1) and F.8.1 (refs/quasithin.pdf). Conjugates in F.8 use g⁻¹Vg;
the TI and transporter maps use gVg⁻¹.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G] {L V : Subgroup G} {n : ℕ}

/-- The literal natural action is transitive on nonidentity vectors. -/
theorem IsNaturalModule.nonidentity_transitive (h : IsNaturalModule L V n)
    {x y : G} (hx : x ∈ V) (hx1 : x ≠ 1) (hy : y ∈ V) (hy1 : y ≠ 1) :
    ∃ l ∈ L, (MulAut.conj l) x = y := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := h
  have hx0 : (f ⟨x,hx⟩).toAdd ≠ 0 := by
    intro hh
    apply hx1
    have he : f ⟨x,hx⟩ = 1 := Multiplicative.toAdd.injective hh
    exact congrArg Subtype.val (f.injective (he.trans f.map_one.symm))
  have hy0 : (f ⟨y,hy⟩).toAdd ≠ 0 := by
    intro hh
    apply hy1
    have he : f ⟨y,hy⟩ = 1 := Multiplicative.toAdd.injective hh
    exact congrArg Subtype.val (f.injective (he.trans f.map_one.symm))
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymplecticFour.natural_transitive hx0 hy0
  obtain ⟨q,hq⟩ := e.surjective g
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have hlg : e (QuotientGroup.mk' (pCore 2 L) l) = g := by rw [hl,hq]
  refine ⟨l,l.property,?_⟩
  have hh := hf l ⟨x,hx⟩
  rw [hlg] at hh
  change (f.symm (Multiplicative.ofAdd (g.val.mulVec (f ⟨x,hx⟩).toAdd)) : G) = _ at hh
  rw [hg,ofAdd_toAdd,f.symm_apply_apply] at hh
  exact hh.symm

namespace RankOneGeneric.LinearParity
variable [Finite G] {T : Sylow 2 G} {H A : Subgroup G}

/-- Local point TI turns a natural transporter into a point-normalizer transporter. -/
theorem fundamental_point_transitive
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    {x y : G} (hx : x ∈ (setup T L D.moduleSubgroup H A).V₁) (hx1 : x ≠ 1)
    (hy : y ∈ (setup T L D.moduleSubgroup H A).V₁) (hy1 : y ≠ 1) :
    ∃ l ∈ L ⊓ normalizer ((setup T L D.moduleSubgroup H A).V₁ : Set G),
      (MulAut.conj l) x = y := by
  obtain ⟨l,hl,he⟩ := hnat.nonidentity_transitive hx.2 hx1 hy.2 hy1
  refine ⟨l,⟨hl,?_⟩,he⟩
  rcases fundamental_point_ti_under_normalizer D hTL hpsl hodd hnat
      (L.le_normalizer hl) with hd | hn
  · have hm : y ∈ (setup T L D.moduleSubgroup H A).V₁ ⊓
        (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj l).toMonoidHom :=
      ⟨hy,⟨x,hx,he⟩⟩
    change y ∈ (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup) ⊓
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup).map
        (MulAut.conj l).toMonoidHom at hm
    rw [hd,mem_bot] at hm
    exact (hy1 hm).elim
  · exact mem_normalizer_iff_map_conj_eq.mpr hn

/-- I.6.1 globalizes point TI from the original residual normalizer. -/
theorem fundamental_point_global_ti_of_residual_ti
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hti : ∀ g ∈ normalizer (residual H : Set G),
      (setup T L D.moduleSubgroup H A).V₁ ⊓
          (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom =
          (setup T L D.moduleSubgroup H A).V₁) :
    ChapterI.Section06To08.IsTISubgroup (setup T L D.moduleSubgroup H A).V₁ := by
  let Z := (setup T L D.moduleSubgroup H A).V₁
  apply ChapterI.Section06To08.lemma_I_6_1_1_of_mem_normalizer Z
  · intro x hx hx1
    exact (le_inf (point_centralizer_le_residual_normalizer D.simpleQTKE hH hK hnf hx.1 hx1)
      le_rfl).trans
      (inf_elementCentralizer_le_normalizer_of_trivial_intersections hti hx hx1)
  · intro x y hx hy hconj
    by_cases hx1 : x = 1
    · subst x
      obtain ⟨g,hg⟩ := hconj
      have hy1 : y = 1 := by simpa using hg.symm
      exact ⟨1,by simp [hy1]⟩
    have hy1 : y ≠ 1 := by
      obtain ⟨g,hg⟩ := hconj
      intro hy1
      apply hx1
      have he : (MulAut.conj g) x = (MulAut.conj g) 1 := by simpa [hy1] using hg
      exact (MulAut.conj g).injective he
    obtain ⟨l,hl,he⟩ := fundamental_point_transitive D hTL hpsl hodd hnat hx hx1 hy hy1
    exact ⟨⟨l,hl.2⟩,he⟩

/-- A conjugate meeting the point has a transporter in the full point normalizer. -/
theorem fundamental_intersecting_conjugate_transporter
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hti : ChapterI.Section06To08.IsTISubgroup (setup T L D.moduleSubgroup H A).V₁)
    (g : G) (hg : (setup T L D.moduleSubgroup H A).V₁ ⊓
      ChapterG.Section02.Setup.conjugate D.moduleSubgroup g ≠ ⊥) :
    ∃ c ∈ (setup T L D.moduleSubgroup H A).G₁,
      D.moduleSubgroup.map (MulAut.conj c).toMonoidHom =
        ChapterG.Section02.Setup.conjugate D.moduleSubgroup g := by
  obtain ⟨x,hx,hx1⟩ := SetLike.not_le_iff_exists.mp (mt le_bot_iff.mp hg)
  simp only [mem_bot] at hx1
  have hLC : L ≤ normalizer (D.moduleSubgroup : Set G) := by
    have horbit : Chapter3.Section02.localOrbit T L = L :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTL)
        (le_componentOrbit _ _)
    simpa only [horbit] using D.orbit_normalizes_module
  have htrans : ∀ y ∈ D.moduleSubgroup, y ≠ 1 →
      ∃ l ∈ normalizer (D.moduleSubgroup : Set G), (MulAut.conj l) x = y := by
    intro y hy hy1
    obtain ⟨l,hl,he⟩ := hnat.nonidentity_transitive hx.1.2 hx1 hy hy1
    exact ⟨l,hLC hl,he⟩
  obtain ⟨c,hc⟩ := exists_centralizer_conjugator_of_normalizer_transitive
    D.moduleSubgroup hx1 htrans hx.2
  exact ⟨c,hti.centralizer_le_normalizer hx.1 hx1 c.property,hc⟩

/-- The abelian normalizer span supplies exactly F.8.1(a). -/
theorem fundamental_intersecting_conjugates_commute
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hti : ChapterI.Section06To08.IsTISubgroup (setup T L D.moduleSubgroup H A).V₁)
    (hab : IsMulCommutative (conjugateSpanBy D.moduleSubgroup
      (setup T L D.moduleSubgroup H A).G₁))
    (g : G) (hg : (setup T L D.moduleSubgroup H A).V₁ ⊓
      ChapterG.Section02.Setup.conjugate D.moduleSubgroup g ≠ ⊥) :
    ⁅D.moduleSubgroup, ChapterG.Section02.Setup.conjugate D.moduleSubgroup g⁆ = ⊥ := by
  obtain ⟨c,hc,he⟩ := fundamental_intersecting_conjugate_transporter D hTL hnat hti g hg
  let U := conjugateSpanBy D.moduleSubgroup (setup T L D.moduleSubgroup H A).G₁
  let : IsMulCommutative U := hab
  have hgU : ChapterG.Section02.Setup.conjugate D.moduleSubgroup g ≤ U := by
    rw [← he]
    rintro y ⟨v,hv,rfl⟩
    exact subset_closure ⟨c,hc,v,hv,rfl⟩
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((le_conjugateSpanBy _ _).trans ((le_centralizer U).trans (centralizer_le hgU)))


/-- H escapes the unique maximal two-local over LT, forcing the generated two-core to vanish. -/
theorem fundamental_generated_core_eq_bot
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    pCore 2 ((setup T L D.moduleSubgroup H A).LT ⊔
      (setup T L D.moduleSubgroup H A).H : Subgroup G) = ⊥ := by
  have hu := D.lemma_3_2_3_uniqueness
    (Chapter1.Section02.nonsolvable_uniqueness_knownSimple D.simpleQTKE T D.maximal)
  have horbit : Chapter3.Section02.localOrbit T L = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTL)
      (le_componentOrbit _ _)
  have hjoin : Chapter3.Section02.localJoin T L = L ⊔ (T : Subgroup G) := by
    rw [Chapter3.Section02.localJoin,horbit]
  have hM : D.maximalLocal = normalizer (L : Set G) := by
    change normalizer (Chapter3.Section02.localOrbit T L : Set G) = _
    rw [horbit]
  apply twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup
    (L ⊔ (T : Subgroup G)) (H ⊔ A) (normalizer (L : Set G))
  · intro N hN hLN
    exact (hu.2.2 N hN (hjoin.symm ▸ hLN)).trans hM
  · intro hle
    exact hH.1.2 (le_sup_left.trans hle)

/-- Construct F.8.1 from the remaining normalizer geometry and G.2.1 inputs. -/
theorem fundamental_f8_of_normalizer_span
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hti : ∀ g ∈ normalizer (residual H : Set G),
      (setup T L D.moduleSubgroup H A).V₁ ⊓
          (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom =
          (setup T L D.moduleSubgroup H A).V₁)
    (hg2 : ChapterG.Section02.Setup.Hypothesis (setup T L D.moduleSubgroup H A))
    (hab : IsMulCommutative (conjugateSpanBy D.moduleSubgroup
      (setup T L D.moduleSubgroup H A).G₁))
    (hker : ((setup T L D.moduleSubgroup H A).quotientCentralizer hg2.H_le
      D.moduleSubgroup).normalCore ≤ pCore 2 (H ⊔ A : Subgroup G)) :
    (setup T L D.moduleSubgroup H A).Hypothesis := by
  have hglobal := fundamental_point_global_ti_of_residual_ti D hTL hpsl hodd hnat
    hH.1.1 hK hnf hti
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple D.simpleQTKE T D.maximal
  have horbit : Chapter3.Section02.localOrbit T L = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTL)
      (le_componentOrbit _ _)
  have hjoin : Chapter3.Section02.localJoin T L = L ⊔ (T : Subgroup G) := by
    rw [Chapter3.Section02.localJoin,horbit]
  exact {
    sylow := ⟨T,rfl⟩
    elementary := D.module_elementary
    residual := hg2.residual
    T_normalizes_L := hTL
    characteristic_L := D.faithful.1.2.2
    V_le_LT := D.module_le_sylow.trans le_sup_right
    reduced := by
      change IsPReduced 2 (D.moduleSubgroup.subgroupOf (L ⊔ (T : Subgroup G)))
      rw [← hjoin]
      exact D.module_reduced hu
    centralizer_eq := by
      change (T : Subgroup G) ⊓ centralizer (D.moduleSubgroup : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2
      rw [← hjoin]
      exact D.sylow_centralizer_module hu
    point_ne_bot := hg2.point_ne_bot
    point_le := hg2.point_le
    T_normalizes_point := hg2.T_normalizes_point
    conjugates_commute := fundamental_intersecting_conjugates_commute D hTL hnat hglobal hab
    quotient_nonzero := hg2.quotient_nonzero
    irreducible := hg2.irreducible
    H_le := hg2.H_le
    local_le := hg2.local_le
    characteristic_H := hg2.characteristic_two
    centralizer_core_le := hker
    generated_core := fundamental_generated_core_eq_bot D hTL hH }

end RankOneGeneric.LinearParity
end CFSG.Quasithin.Chapter6.Source

