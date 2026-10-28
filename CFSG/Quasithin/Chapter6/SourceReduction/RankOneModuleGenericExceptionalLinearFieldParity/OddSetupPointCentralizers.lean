module
public import Theory.GroupAction.CentralEightAutomizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupDegreeThreeSylow

/-!
# Common point centralizers in the degree-three residual geometry

For the original natural point Z₁ of order eight, T acts trivially. Its
full automizer has order dividing 21, while the literal quotient-action
kernel C_K has order prime to three. The original Cartan of order seven
therefore supplies the entire C_K point-stabilizer action. Point TI
under C_K and the free Cartan action identify C_{C_K}(z) with C_{C_K}(Z₁)
for every nonidentity z in Z₁.

The previously constructed full C_K Sylow is exactly that Cartan.
Intersecting it with the normalized pointwise centralizer shows the
centralizer has order prime to seven. If an N_G(K)-conjugate point meets
Z₁, both points have the same C_K-centralizer, and the conjugating element
normalizes this common subgroup. This supplies conjugation geometry
beyond the Frattini product; point equality still needs a proof.

The literal Chapter12 application is LinearFieldParityPointCentralizers.
Higher odd-degree point invariance, residual/global TI and full parity
remain with qt-d-1222-linear-field-parity. The independent Suzuki premise
is retained as solvability of the actual quotient-action kernel, with
qt-f112-linear-suzuki-containment retaining its source discharge.
Source: Aschbacher–Smith, 5.1.17, printed p.640 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G}
local instance pointCentralizerSevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The original point has a common seven-free kernel centralizer, preserved
by every residual-normalizer transporter producing an intersection. -/
theorem fundamental_degree_three_point_centralizers
    (h : Input KnownSimple.IsKnownSimple T L W 3)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup 3)
    (c : CartanPair T L H A B) :
    let N := normalizer (residual H : Set G)
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map N.subtype
    let Z := (setup T L D.moduleSubgroup H A).V₁
    C ⊓ normalizer (Z : Set G) = A ⊔ (C ⊓ centralizer (Z : Set G)) ∧
      (¬ 7 ∣ Nat.card (C ⊓ centralizer (Z : Set G) : Subgroup G)) ∧
      (∀ z ∈ Z, z ≠ 1 → C ⊓ centralizer ({z} : Set G) = C ⊓ centralizer (Z : Set G)) ∧
      ∀ g ∈ N, Z ⊓ Z.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
        C ⊓ centralizer (Z : Set G) = C ⊓ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G) ∧
          g ∈ normalizer ((C ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) := by
  let N := normalizer (residual H : Set G)
  let f := normalizerQuotientAction (residual H) (pCore 2 (residual H))
  let C := f.ker.map N.subtype
  let Z := (setup T L D.moduleSubgroup H A).V₁
  let := D.module_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le
    (show Z ≤ D.moduleSubgroup from inf_le_right)
  have hNZ : Nat.card Z = 8 := by
    exact fundamental_point_card D h.sylow_normalizes h.linear (by decide) hnat
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mp
    intro z hz t ht
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 t ht
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_maximal
  have hTN : (T : Subgroup G) ≤ N := hH.1.1.2.trans (le_normalizer_residual H)
  have horbit : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTN) (le_componentOrbit _ _)
  rw [horbit] at hmax
  have hsq : IsStronglyQuasithin N := (h.qtke.twoLocal_sqtk hmax.1).stronglyQuasithin
  have h3 : ¬ 3 ∣ Nat.card C := by
    rw [show Nat.card C = Nat.card f.ker from card_map_of_injective N.subtype_injective]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      (CubicEscape.quotientAction_kernel_three_prime (residual H) hsq (linear_residual_quotient hm))
  have hAC : A ≤ C := cartan_residual_action_trivial_of_odd h hH c (by decide) hK hnf hm
  have hAZ : A ≤ normalizer (Z : Set G) :=
    (c.left_le.trans (fundamental_point_normalizer D h.sylow_normalizes h.linear
      (by decide) hnat).ge).trans inf_le_right
  have hA : Nat.card A = 7 := by
    simpa using (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hfaith : Disjoint A (centralizer (Z : Set G)) :=
    fundamental_cartan_point_disjoint_centralizer D h.sylow_normalizes h.linear
      (by decide) (by decide) hnat c
  have hfree : ∀ a ∈ A, ∀ z ∈ Z, z ≠ 1 → a*z = z*a → a = 1 := by
    intro a ha z hz hz1 hac
    by_contra ha1
    have hne : zpowers a ≠ ⊥ := by
      intro he
      exact ha1 (mem_bot.mp (he ▸ mem_zpowers a))
    have hc : z ∈ centralizer (zpowers a : Set G) := by
      rintro b ⟨m,rfl⟩
      exact (show Commute a z from hac).zpow_left m |>.eq
    have hzC : z ∈ D.moduleSubgroup ⊓ centralizer (zpowers a : Set G) := ⟨hz.2,hc⟩
    rw [natural_cartan_subgroup_fixed_eq_bot c hnat (zpowers a) (zpowers_le.mpr ha) hne,
      mem_bot] at hzC
    exact hz1 hzC
  have hti : ∀ g ∈ C, Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
    intro g hg
    exact fundamental_point_ti_under_solvable_kernel h hH hK hnf hm hsolv D
      (by decide) hnat (mem_sup_left hg)
  have he (z : G) (hz : z ∈ Z) (hz1 : z ≠ 1) :
      C ⊓ centralizer ({z} : Set G) = C ⊓ centralizer (Z : Set G) :=
    central_eight_elementCentralizer_eq T Z C A hNZ hTZ h3 hAC hAZ hA hfaith hfree hti hz hz1
  let K := C ⊓ centralizer (Z : Set G)
  have hAK : A ≤ normalizer (K : Set G) :=
    (le_inf (hAC.trans C.le_normalizer)
      (hAZ.trans (normalizer_le_normalizer_centralizer Z))).trans inf_normalizer_le_normalizer_inf
  have hk7 : ¬ 7 ∣ Nat.card K := by
    -- K is normal in the point stabilizer. Its intersection with the full
    -- C-Sylow A is trivial, so its seven-part is trivial.
    obtain ⟨P,hP,_,_,_,_,_⟩ := fundamental_degree_three_full_sylow_point_action
      h hH hK hnf hm hsolv D hnat c
    let K' := K.subgroupOf C
    have hPK : (P : Subgroup C) ≤ normalizer (K' : Set C) := by
      intro x hx
      have hxA : (x : G) ∈ A := hP ▸ mem_map_of_mem C.subtype hx
      rw [mem_normalizer_iff]
      intro y
      change (y : G) ∈ K ↔ (x : G) * (y : G) * (x : G)⁻¹ ∈ K
      exact mem_normalizer_iff.mp (hAK hxA) y
    obtain ⟨R,hR⟩ := NormalSylowQuotientAction.intersection_sylow P K' hPK
    have hRbot : (R : Subgroup K') = ⊥ := by
      apply bot_unique
      intro x hx
      have hxP : (x : C) ∈ P := hR.le hx
      have hxA : (x.val : G) ∈ A := hP ▸ mem_map_of_mem C.subtype hxP
      apply mem_bot.mpr
      apply Subtype.ext
      apply Subtype.ext
      exact hfaith.le_bot ⟨hxA,x.property.2⟩
    have hfree := R.not_dvd_index
    rw [hRbot,index_bot] at hfree
    rwa [Nat.card_congr (subgroupOfEquivOfLe (show K ≤ C from inf_le_left)).toEquiv] at hfree
  refine ⟨central_eight_three_free_stabilizer_factor T Z C A hNZ hTZ h3 hAC hAZ hA hfaith,hk7,he,?_⟩
  intro g hg hx
  have hNC : N ≤ normalizer (C : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using f.ker.le_normalizer_map N.subtype
  exact ⟨centralizers_eq_of_intersecting_conjugates Z C he (hNC hg) hx,
    centralizer_normalizer_of_intersecting_conjugates Z C he (hNC hg) hx⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
