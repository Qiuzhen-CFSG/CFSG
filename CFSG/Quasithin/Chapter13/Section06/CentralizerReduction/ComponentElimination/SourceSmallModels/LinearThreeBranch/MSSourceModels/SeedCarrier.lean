module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.Basic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.SeedGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import Theory.Representation.PSL3Two.NaturalOrbits

/-!
# The literal seed carrier in the linear-three branch

The earlier Sylow and characteristic-two conclusions put the seed span W_K
inside T_v. Its commutator with K is a normal two-subgroup of K. The core of
KT_v centralizes the seed span, since it is normal and fixes the original seed.
Commutator idempotence therefore puts [W_K,K] in [Z(O₂(K)),K].
The actual marked A₅ line lies in this subgroup. In the natural cases,
transitivity on nonzero vectors upgrades the inclusion to equality. The
doubled-natural case is not asserted to follow from nonvanishing.

C.1.34(5) has an additional clause beyond its natural quotient: the omega
center of the Sylow subgroup is central in KT_v. In the present application
that Sylow subgroup is T_v itself. This clause contradicts the moving seed
condition in Y_z and excludes the order-sixteen alternative directly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.14 and
13.6.22, printed pp.929–932; C.1.34(5), printed pp.136–137.
-/

@[expose] public section
open Subgroup Representation Stellmacher
open scoped Pointwise
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.SeedCarrier
open ComponentSelection SourceContainment
variable {G : Type*} [Group G] {K L T : Subgroup G} {z v : G}

/-- With the actual invariance and containment conclusions, the source span
is the K-orbit span of the original seed. -/
theorem WK_eq_seedSpan (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Lv L v ≤ K) : WK K L T z v = conjugateSpanBy (zpowers z) K := by
  rw [WK, Kminus_eq_of_invariant K T v hn, sup_eq_left.mpr hL]

/-- The moving condition survives the literal star quotient. -/
theorem not_centralizes_seed (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    ¬ K ≤ centralizer ({z} : Set G) := by
  have hx := (invariant_component_consequences K L T z v hK hn).1.2
  exact fun hc => hx ((starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr hc)

/-- In particular the literal commutator carrier is nontrivial. -/
theorem UK_ne_bot (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) : UK K L T z v ≠ ⊥ := by
  intro he
  apply not_centralizes_seed hK hn
  have hc : K ≤ centralizer (WK K L T z v : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  exact hc.trans (centralizer_le (Set.singleton_subset_iff.mpr
    (le_conjugateSpanBy _ _ (mem_zpowers z))))

/-- R=T_v is already Sylow in KT_v; the S appearing in C.1.34 is therefore
literally T_v. Its central-omega clause would centralize the moving seed. -/
theorem not_central_sylow_omega (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S (K ⊔ Tv T v))
    (hTS : Tv T v ≤ S) :
    ¬ omegaCenterIn S ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (K ⊔ Tv T v) := by
  have he : S = Tv T v := (Chapter1.isSylowIn_iff.mp hK.1.2.2.1).2.2 S
    (Chapter1.isSylowIn_iff.mp hS).1 hTS (Chapter1.isSylowIn_iff.mp hS).2.1
  subst S
  intro hc
  obtain ⟨x, hx, he⟩ := hc hz
  apply not_centralizes_seed hK hn
  intro k hk
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg Subtype.val ((mem_center_iff.mp hx) ⟨k, (show K ≤ K ⊔ Tv T v from le_sup_left) hk⟩)
  change k * (x : G) = (x : G) * k at hh
  change (x : G) = z at he
  rwa [he] at hh

/-- Application to all the clauses of C.1.34(5), with its original carrier,
centralizer denominator and core-quotient actor. -/
theorem not_ms_caseFive (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S (K ⊔ Tv T v))
    (hTS : Tv T v ≤ S)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ¬ (Nonempty ((K ⧸ pCore 2 K) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      Nonempty ((msQ K (Tv T v) ⊓ centralizer (K : Set G) : Subgroup G) ≃*
        Multiplicative (ZMod 2)) ∧
      HasSectionModel K (msQ K (Tv T v))
        (msQ K (Tv T v) ⊓ centralizer (K : Set G))
        (linearThreeActor e) BinaryLinearThree.W ∧
      omegaCenterIn S ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (K ⊔ Tv T v) ∧
      MSPointStabilizer K (Tv T v) S) := by
  intro h
  exact not_central_sylow_omega hK hn hz hS hTS h.2.2.2.1

variable [Finite G]

/-- Only genuine earlier source conclusions, with no module marking or
asserted equality between the two candidate carriers. -/
structure EarlierData (K L T : Subgroup G) (z v : G) : Prop where
  component : K ∈ Yz L T z v
  tvSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)
  normalizeK : Tv T v ≤ normalizer (K : Set G)
  lv_le : Lv L v ≤ K
  seedOmega : z ∈ omegaOneCenterAmbient (Tv T v)
  characteristicTwo : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)

namespace EarlierData
variable (d : EarlierData K L T z v)
include d

theorem WK_le_Tv : WK K L T z v ≤ Tv T v := by
  have hw := (WK_le_Uv K L T z v d.component.1.1).trans
    (Uv_le_coreOmega T z v d.tvSylow d.seedOmega d.characteristicTwo)
  obtain ⟨P, hP⟩ := d.tvSylow
  intro w h
  have hc := ((mem_omegaOneCenterAmbient_iff _ _).mp (hw h)).1
  rw [← hP]
  exact pCoreIn_le_sylow (Gv v) P hc

omit [Finite G] in
theorem K_normalizes_WK : K ≤ normalizer (WK K L T z v : Set G) := by
  rw [WK_eq_seedSpan d.normalizeK d.lv_le]
  exact le_normalizer_conjugateSpanBy _ _

theorem WK_isPGroup : IsPGroup 2 (WK K L T z v) :=
  (Chapter1.isSylowIn_iff.mp d.tvSylow).1.to_le d.WK_le_Tv

theorem core_centralizes_WK : K.pCoreIn 2 ≤ centralizer (WK K L T z v : Set G) := by
  let H := K ⊔ Tv T v
  have hKH : K ≤ H := le_sup_left
  have hc : K.pCoreIn 2 ≤ H.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn K H 2 hKH d.component.1.2.1.subnormal
  have hct : H.pCoreIn 2 ≤ Tv T v := by
    obtain ⟨P, hP⟩ := d.component.1.2.2.1
    rw [← hP]
    exact pCoreIn_le_sylow H P
  have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 H).le_normalizer_map H.subtype
  have hz : H.pCoreIn 2 ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp d.seedOmega).2.2 x (hct hx))
  rw [WK_eq_seedSpan d.normalizeK d.lv_le]
  exact hc.trans (le_centralizer_conjugateSpanBy_of_normalizes _ _ K (hKH.trans hn) hz)

/-- The upper bound uses the actual normal two-subgroup [W_K,K] inside K
and coprime commutator idempotence. -/
theorem UK_le_sourceU (hp : IsPPerfect 2 K) : UK K L T z v ≤ sourceU K := by
  let W := WK K L T z v
  let U := UK K L T z v
  have hUK : U ≤ K := le_normalizer_iff_commutator_le_right.mp
    (d.WK_le_Tv.trans d.normalizeK)
  have hUW : U ≤ W := le_normalizer_iff_commutator_le_left.mp d.K_normalizes_WK
  have hn : (U.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_right W K)
  have hcore : U ≤ K.pCoreIn 2 :=
    isPGroup_le_pCoreAmbient_of_isSubnormalIn K U 2 hUK hn.isSubnormal
      (d.WK_isPGroup.to_le hUW)
  have hcenter : U ≤ ((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype := by
    intro u hu
    obtain ⟨q, hq, he⟩ := hcore hu
    refine ⟨q, ⟨⟨q, hq⟩, ?_, rfl⟩, he⟩
    apply mem_center_iff.mpr
    intro r
    apply Subtype.ext
    apply Subtype.ext
    change (r : G) * (q : G) = (q : G) * (r : G)
    change (q : G) = u at he
    rw [he]
    exact (d.core_centralizes_WK (mem_map_of_mem K.subtype r.property)
      u (hUW hu)).symm
  have hid : ⁅U, K⁆ = U :=
    commutator_isPPerfect_idempotent K W hp d.WK_isPGroup d.K_normalizes_WK
  exact hid.symm.le.trans (commutator_mono hcenter le_rfl)

end EarlierData

omit [Finite G] in
/-- A nonzero invariant subgroup of an actual natural three-space is the
whole carrier. Both the actor surjection and the faithful carrier map are
retained, so this does not identify K with the module. -/
theorem eq_of_natural_model {A U : Subgroup G}
    (m : ConjugationQuotientModel K U BinaryLinearThree.W)
    (ha : Function.Surjective m.actor) (hi : Function.Injective m.quotient)
    (hAU : A ≤ U) (hKA : K ≤ normalizer (A : Set G)) (hA : A ≠ ⊥) : A = U := by
  classical
  have hex : ∃ x : G, x ∈ A ∧ x ≠ 1 := by
    by_contra! hn
    exact hA (le_antisymm (fun x hx => mem_bot.mpr (hn x hx)) bot_le)
  obtain ⟨x, hx, hx1⟩ := hex
  let xU : U := ⟨x, hAU hx⟩
  have hfx : Multiplicative.toAdd (m.quotient xU) ≠ 0 := by
    intro he
    have he' : m.quotient xU = m.quotient 1 := he.trans (map_one m.quotient).symm
    exact hx1 (congrArg Subtype.val (hi he'))
  apply le_antisymm hAU
  intro y hy
  let yU : U := ⟨y, hy⟩
  by_cases hfy : Multiplicative.toAdd (m.quotient yU) = 0
  · have he' : m.quotient yU = m.quotient 1 := hfy.trans (map_one m.quotient).symm
    have he : y = 1 := congrArg Subtype.val (hi he')
    exact he ▸ A.one_mem
  · obtain ⟨g, hg⟩ := BinaryLinearThree.natural_transitive_nonzero
      (Multiplicative.toAdd (m.quotient xU)) (Multiplicative.toAdd (m.quotient yU)) hfx hfy
    obtain ⟨k, rfl⟩ := ha g
    have he : U.normalizerMonoidHom ⟨k, m.normalizes k.property⟩ xU = yU := by
      apply hi
      apply Multiplicative.toAdd.injective
      rw [m.equivariant]
      exact hg
    have hc := (mem_normalizer_iff.mp (hKA k.property) x).mp hx
    have he' : (k : G) * x * (k : G)⁻¹ = y := congrArg Subtype.val he
    exact he' ▸ hc

/-- The irreducible cases (1), (3), and (4) identify the literal seed
carrier once their genuine trivial-denominator section has been realized
on sourceU. Construction of that section is the MS-realization owner's job. -/
theorem UK_eq_sourceU_of_natural_section (d : EarlierData K L T z v)
    (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K (sourceU K) ⊥ (linearThreeActor e) BinaryLinearThree.W) :
    UK K L T z v = sourceU K := by
  obtain ⟨m, hm⟩ := natural_model_of_section e h
  have hi : Function.Injective m.quotient := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [m.kernel]
    have hc := section_centralizer_eq h (linearThreeActor_surjective e) bot_le
      (fun w hw => BinaryLinearThree.ParabolicFixedFree.natural_fixed_eq_zero w
        (fun g _ => hw g))
    simpa only [bot_subgroupOf] using hc
  apply eq_of_natural_model m (hm ▸ linearThreeActor_surjective e) hi
    (d.UK_le_sourceU hp) (normalizer_commutator_ge_right _ _) (UK_ne_bot d.component d.normalizeK)

/-- An actual application of the carrier identification to C.1.34(1).
The original checked quotient restriction and the core-quotient actor
are the same ones used by the MS realization. -/
theorem natural_ms_seed_realization (d : EarlierData K L T z v)
    (hp : IsPPerfect 2 K) (hv : v ^ 2 = 1)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K (msQ K (Tv T v)) ⊥
      (linearThreeActor e) BinaryLinearThree.W) :
    UK K L T z v = sourceU K ∧
    (∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      m.actor = linearThreeActor e) ∧
    ⁅sourceZ0 K v d.component.1.1, K⁆ = sourceU K := by
  obtain ⟨hU, hm, hz⟩ := natural_ms_section_realization v d.component.1.1 hv
    d.component.1.2.1.subnormal hp e h
  exact ⟨UK_eq_sourceU_of_natural_section d hp e (hU ▸ h), hm, hz⟩

/-- The source line is contained in sourceU even before the full seed
equality is established. This supplies the literal containment consumed by
the natural and doubled parabolic geometry, using the marked A₅ calculation
[V,L_v]=[⟨z⟩,L_v]. -/
theorem marked_line_le_sourceU {V : Subgroup G} (s : A5Module.Marking L V)
    (d : EarlierData K L T (A5Module.markedZ s) (A5Module.markedV s))
    (hp : IsPPerfect 2 K) : ⁅V, Lv L (A5Module.markedV s)⁆ ≤ sourceU K := by
  rw [SourceContainment.LinearThree.CentralAction.local_commutator_eq_seed s]
  apply le_trans _ (d.UK_le_sourceU hp)
  exact commutator_mono (le_conjugateSpanBy _ _) d.lv_le

omit [Finite G] in
/-- A seed in a central supplement of an invariant subgroup has all its
commutators in that invariant subgroup. -/
theorem commutator_seedSpan_le (A C : Subgroup G)
    (hA : A ≤ centralizer (K : Set G)) (hAC : A ≤ normalizer (C : Set G))
    (hKC : K ≤ normalizer (C : Set G)) (hz : z ∈ A ⊔ C) :
    ⁅conjugateSpanBy (zpowers z) K, K⁆ ≤ C := by
  have hKA : K ≤ normalizer (A : Set G) :=
    (le_centralizer_iff.mp hA).trans (Subgroup.centralizer_le_normalizer _)
  have hn : K ≤ normalizer ((A ⊔ C : Subgroup G) : Set G) := by
    intro k hk
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hKA hk),
      mem_normalizer_iff_map_conj_eq.mp (hKC hk)]
  apply (commutator_mono (conjugateSpanBy_le (zpowers_le.mpr hz) hn) le_rfl).trans
  apply commutator_le.mpr
  intro b hb k hk
  have hb' : b ∈ (A : Set G) * (C : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right A C hAC]
    exact hb
  obtain ⟨a, ha, c, hc, rfl⟩ := hb'
  have hak : Commute a k := (mem_centralizer_iff.mp (hA ha) k hk).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hak.commutator_eq, mul_one]
  exact (mem_normalizer_iff.mp (hAC ha) _).mp
    ((le_normalizer_iff_commutator_le_left.mp hKC) (commutator_mem_commutator hc hk))

/-- The exact carrier generated by the source line. The marked identity
V_v=⟨v⟩[V,L_v] and K≤C_G(v) show that its K-conjugates generate U_K.
This holds for both natural and doubled sourceU models. -/
theorem UK_eq_marked_line_span {V : Subgroup G} (s : A5Module.Marking L V)
    (d : EarlierData K L T (A5Module.markedZ s) (A5Module.markedV s)) :
    UK K L T (A5Module.markedZ s) (A5Module.markedV s) =
      conjugateSpanBy ⁅V, Lv L (A5Module.markedV s)⁆ K := by
  let l := ⁅V, Lv L (A5Module.markedV s)⁆
  let U := UK K L T (A5Module.markedZ s) (A5Module.markedV s)
  let C := conjugateSpanBy l K
  have hlU : l ≤ U := by
    dsimp [l]
    rw [SourceContainment.LinearThree.CentralAction.local_commutator_eq_seed s]
    exact commutator_mono (le_conjugateSpanBy _ _) d.lv_le
  have hUK : U ≤ K := le_normalizer_iff_commutator_le_right.mp
    (d.WK_le_Tv.trans d.normalizeK)
  have hCK : C ≤ K := conjugateSpanBy_le (hlU.trans hUK) K.le_normalizer
  have hZ : zpowers (A5Module.markedV s) ≤ centralizer (K : Set G) := by
    apply le_centralizer_iff.mpr
    rw [zpowers_eq_closure, centralizer_closure]
    exact d.component.1.1
  have hseed : A5Module.markedZ s ∈ zpowers (A5Module.markedV s) ⊔ C := by
    apply (sup_le_sup_left (le_conjugateSpanBy l K) (zpowers (A5Module.markedV s)))
    rw [← A5Module.Vv_eq_line_sup_commutator s]
    exact z_mem_Vv L (A5Module.markedZ s) (A5Module.markedV s)
  apply le_antisymm
  · rw [UK, WK_eq_seedSpan d.normalizeK d.lv_le]
    exact commutator_seedSpan_le _ C hZ
      ((hZ.trans (centralizer_le hCK)).trans (Subgroup.centralizer_le_normalizer _))
      (le_normalizer_conjugateSpanBy l K) hseed
  · exact conjugateSpanBy_le hlU (normalizer_commutator_ge_right _ _)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.SeedCarrier
