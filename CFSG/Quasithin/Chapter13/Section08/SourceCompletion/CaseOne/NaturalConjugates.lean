module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.Commutators
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalLabel
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
public import CFSG.Quasithin.Chapter13.Section07.ChosenConjugator
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPointOrbits
public import Theory.GroupTheory.ConjugateSpanLineKernel

/-!
# The nonorthogonal source conjugator in the nonabelian-span branch

The full-denominator endpoint and the length-three seed placement give a
commuting U_H-conjugate at a distinct point of V₃. The actual A₆ action
on V transports this commutation to every orthogonal point. If the whole
L-span lay in O₂(H), its commutators would lie in two distinct order-two
point lines and the span would be abelian. Thus a nonabelian span supplies
a nonorthogonal conjugate with nontrivial image in H/O₂(H).

The same marked point-stabilizer orbit transports nontrivial star action
to the earlier constructed conjugator whose square lies in O₂(LT).
The final theorem constructs this conjugator, its spanning nonorthogonal
point, and its nontrivial literal star image together. The inverse of the
source right-conjugation representative aligns every map with `conjBy`.

The ordinary identity H = G₁ and full denominators are explicit earlier
source/branch inputs, not conclusions asserted here. No abelianness of
U_L, chief-factor count, or strict denominator is assumed. The natural
nonabelian exclusion, Steinberg/permutation comparisons and final 13.8.33
assembly remain with `qt-d-138-a6-endgame-source`; the ordinary setup is
supplied by `qt-d-138-six-g2-source`.
Source: Aschbacher--Smith, Lemma 13.8.33, printed pp.966--967, using
13.7.3, 13.8.4 and 13.8.27.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.SixAndG2.Overgroup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The natural nonabelian branch cannot put the whole L-span in O₂(H). -/
theorem nonabelian_span_not_le_core
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hH : H = G₁) (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ¬ Source.UL L H V₃ ≤ Source.QH H := by
  intro hle
  apply hn
  apply conjugateSpan_commutative_of_line_kernel (Source.UH H V₃) L V₁ (Source.QH H)
    d.line_card
  · rw [← d.first_normalizer, ← hH]
    exact le_normalizer_conjugateSpanBy V₃ H
  · exact hF9.commutator_UH_QH_le_point
  · exact hle

/-- The conjugate realizing nontrivial star action is constructed from the
actual nonabelian span, rather than supplied as an extra premise. -/
theorem exists_nontrivial_conjugate_star
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hH : H = G₁) (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ∃ l : L, (Source.UH H V₃).conjBy (l : G) ≤ H ∧
      Source.starImage H ((Source.UH H V₃).conjBy (l : G)) ≠ ⊥ := by
  have hspanH : Source.UL L H V₃ ≤ H := by
    have hQ : (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ≤ (T : Subgroup G) := by
      change (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).LT.pCoreIn 2 ≤ _
      rw [← hF9.sylow_centralizer]
      exact inf_le_left
    exact (Section07.span_UH_L_le_core (localNaturalSetup d) hF9 (show IsMulCommutative (Source.UH H V₃) from inferInstance)).trans
      (hQ.trans hF9.T_le_H)
  have hlspan (l : L) : (Source.UH H V₃).conjBy (l : G) ≤ Source.UL L H V₃ := by
    rintro _ ⟨u, hu, rfl⟩
    exact subset_closure ⟨l, l.property, u, hu, rfl⟩
  by_contra! hh
  apply nonabelian_span_not_le_core d hF9 hH hn
  apply (closure_le _).mpr
  rintro x ⟨l, hl, u, hu, rfl⟩
  let lL : L := ⟨l, hl⟩
  have hU := (hlspan lL).trans hspanH
  have hz := hh lL hU
  let v : H := ⟨l * u * l⁻¹, hU (mem_map_of_mem _ hu)⟩
  have hv : QuotientGroup.mk' (pCore 2 H) v ∈
      Source.starImage H ((Source.UH H V₃).conjBy l) :=
    mem_map_of_mem _ (mem_map_of_mem _ hu)
  rw [hz, mem_bot] at hv
  exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff v).mp hv)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup BinaryPermutation
open CriticalGeometry TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- Lift the two natural point-stabilizer orbits to the original L and H,
retaining the original natural coordinates and conjugation convention. -/
theorem local_point_stabilizer_transitive
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (hH : H = G₁)
    (z : V₁) (hz : z ≠ 1) (u v : V)
    (hu : u ≠ 1) (hv : v ≠ 1)
    (huz : (u : G) ≠ (z : G)) (hvz : (v : G) ≠ (z : G))
    (hp : form (d.coordinate (inclusion (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z)).toAdd
        (d.coordinate u).toAdd =
      form (d.coordinate (inclusion (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z)).toAdd
        (d.coordinate v).toAdd) :
    ∃ a : L, (a : G) ∈ H ∧ (a : G) * (z : G) * (a : G)⁻¹ = z ∧
      (a : G) * (u : G) * (a : G)⁻¹ = v := by
  let zV : V := inclusion (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z
  have hzV : zV ≠ 1 := by
    intro he
    have heval : (z : G) = 1 := congrArg (fun x : V => (x : G)) he
    exact hz (Subtype.ext heval)
  have hcoord (w : V) (hw : w ≠ 1) : (d.coordinate w).toAdd ≠ 0 := by
    intro he
    exact hw (d.coordinate.injective (he.trans (map_one d.coordinate).symm))
  obtain ⟨b, hbz, hbu⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPointOrbits.stabilizer_transitive
      (d.coordinate zV).toAdd (d.coordinate u).toAdd (d.coordinate v).toAdd
      (hcoord zV hzV) (hcoord u hu) (hcoord v hv)
      (fun he => huz (congrArg Subtype.val (d.coordinate.injective he)))
      (fun he => hvz (congrArg Subtype.val (d.coordinate.injective he))) hp
  obtain ⟨q, hq⟩ := d.local_quotient.surjective b
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (centralCore L) q
  have haz : (a : G) * (z : G) * (a : G)⁻¹ = z := by
    have he := d.conjugation a zV
    rw [ha, hq] at he
    exact congrArg Subtype.val (d.coordinate.injective (he.trans hbz))
  have hau : (a : G) * (u : G) * (a : G)⁻¹ = v := by
    have he := d.conjugation a u
    rw [ha, hq] at he
    exact congrArg Subtype.val (d.coordinate.injective (he.trans hbu))
  have haH : (a : G) ∈ H := by
    rw [hH, d.first_normalizer,
      A6Endgame.PointNormalizer.normalizer_eq_point_centralizer V₁ d.line_card
        (z : G) z.property (fun he => hz (Subtype.ext he))]
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp haz)
  exact ⟨a, haH, haz, hau⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.SixAndG2.Overgroup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The original critical endpoint constructs a distinct orthogonal point
whose associated conjugate of U_H commutes with U_H. -/
theorem exists_seed_commuting_conjugate
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ∃ l : L, V₁.conjBy (l : G) ≤ V₃ ∧ V₁.conjBy (l : G) ≠ V₁ ∧
      ⁅Source.UH H V₃, (Source.UH H V₃).conjBy (l : G)⁆ = ⊥ := by
  obtain ⟨_, h, hA⟩ := nonabelian_seed_placement d hF9 c hDH hDg hcentral hn
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hPV : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hzA : (c.gb : G) * (z : G) * (c.gb : G)⁻¹ ∈ c.Aone V₁ :=
    mem_map_of_mem _ z.property
  have hm : (h : G)⁻¹ * ((c.gb : G) * (z : G) * (c.gb : G)⁻¹) * (h : G) ∈ V₃ := by
    obtain ⟨v, hv, he⟩ := hA hzA
    change (h : G) * v * (h : G)⁻¹ = (c.gb : G) * (z : G) * (c.gb : G)⁻¹ at he
    have he' : (h : G)⁻¹ * ((c.gb : G) * (z : G) * (c.gb : G)⁻¹) * (h : G) = v := by
      rw [← he]; group
    rwa [he']
  have hcenter : centralizer ({(z : G)} : Set G) ≤ H := by
    rw [hH, d.first_normalizer,
      A6Endgame.PointNormalizer.normalizer_eq_point_centralizer V₁ d.line_card z z.property hz1]
  let F : Bool → Subgroup G := fun i => if i then H else L
  obtain ⟨l, hl, k, hk, he⟩ := Subgroup.CosetGeometry.RankTwo.central_label_factorization
    F V z c.gb h hz1 hcenter
      (fun v hv hne => local_nonzero_transitive d (hPV z.property) hv hz1 hne) (d.seed_le hm)
  have hfixP (a : G) (ha : a ∈ H) : V₁.conjBy a = V₁ :=
    mem_normalizer_iff_map_conj_eq.mp ((hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) ha)
  have hfixU (a : G) (ha : a ∈ H) : (Source.UH H V₃).conjBy a = Source.UH H V₃ :=
    mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy V₃ H) ha)
  have hpoint : (c.Aone V₁).conjBy (h : G)⁻¹ = V₁.conjBy l := by
    change (V₁.conjBy (c.gb : G)).conjBy (h : G)⁻¹ = _
    rw [he, conjBy_mul, conjBy_mul, hfixP k hk, conjBy_inv]
  have hU : (c.Ugamma V₃).conjBy (h : G)⁻¹ = (Source.UH H V₃).conjBy l := by
    change ((Source.UH H V₃).conjBy (c.gb : G)).conjBy (h : G)⁻¹ = _
    rw [he, conjBy_mul, conjBy_mul, hfixU k hk, conjBy_inv]
  have hle : V₁.conjBy l ≤ V₃ := by
    have hh := map_mono (f := (MulAut.conj (h : G)⁻¹).toMonoidHom) hA
    change (c.Aone V₁).conjBy (h : G)⁻¹ ≤ (V₃.conjBy (h : G)).conjBy (h : G)⁻¹ at hh
    rwa [hpoint, conjBy_inv] at hh
  have hdis : V₁ ⊓ V₁.conjBy l = ⊥ := by
    have hh := congrArg (fun P : Subgroup G => P.map (MulAut.conj (h : G)⁻¹).toMonoidHom)
      (local_earlierGeometry d hF9 c).lines_disjoint
    rw [map_inf _ _ _ (MulAut.conj (h : G)⁻¹).injective, Subgroup.map_bot] at hh
    change V₁.conjBy (h : G)⁻¹ ⊓ (c.Aone V₁).conjBy (h : G)⁻¹ = ⊥ at hh
    rwa [hfixP _ (H.inv_mem h.property), hpoint] at hh
  have hne : V₁.conjBy l ≠ V₁ := by
    intro heq
    rw [heq, inf_idem] at hdis
    have hc := d.line_card
    rw [hdis, card_bot] at hc
    contradiction
  refine ⟨⟨l, hl⟩, hle, hne, ?_⟩
  have hh := congrArg (fun P : Subgroup G => P.map (MulAut.conj (h : G)⁻¹).toMonoidHom)
    (full_denominators_commutator d hF9 c hDH hDg).1
  rw [map_commutator, Subgroup.map_bot] at hh
  change ⁅(Source.UH H V₃).conjBy (h : G)⁻¹, (c.Ugamma V₃).conjBy (h : G)⁻¹⁆ = ⊥ at hh
  rwa [hfixU _ (H.inv_mem h.property), hU] at hh

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

private theorem conjugate_UH_eq_of_point_eq
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (hH : H = G₁)
    (g k : G) (hp : V₁.conjBy g = V₁.conjBy k) :
    (Source.UH H V₃).conjBy g = (Source.UH H V₃).conjBy k := by
  have hk : k⁻¹ * g ∈ H := by
    rw [hH, d.first_normalizer]
    exact mem_normalizer_iff_map_conj_eq.mpr (conjBy_inv_mul_cancel V₁ hp.symm)
  have he := mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V₃ H hk)
  have hh := congrArg (fun P : Subgroup G => P.conjBy k) he
  change ((Source.UH H V₃).conjBy (k⁻¹ * g)).conjBy k = (Source.UH H V₃).conjBy k at hh
  rwa [conjBy_conjBy, mul_inv_cancel_left] at hh

private theorem point_zpowers
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (z : V₁) (hz : z ≠ 1) :
    V₁ = zpowers (z : G) := by
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
  have hzW : z = w := hw z hz
  apply le_antisymm
  · intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ (zpowers (z : G)).one_mem
    · have he : (⟨x, hx⟩ : V₁) = z := (hw _ (fun h => hx1 (congrArg Subtype.val h))).trans hzW.symm
      rw [show x = (z : G) from congrArg Subtype.val he]
      exact mem_zpowers _
  · exact zpowers_le.mpr z.property

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup BinaryPermutation CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.SixAndG2.Overgroup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem seed_conjugates_commute
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hn : ¬ IsMulCommutative (Source.UL L H V₃))
    (l : L) (hseed : V₁.conjBy (l : G) ≤ V₃) :
    ⁅Source.UH H V₃, (Source.UH H V₃).conjBy (l : G)⁆ = ⊥ := by
  by_cases hp : V₁.conjBy (l : G) = V₁
  · have hlH : (l : G) ∈ H := by
      rw [hH, d.first_normalizer]
      exact mem_normalizer_iff_map_conj_eq.mpr hp
    have hfix := mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V₃ H hlH)
    change (Source.UH H V₃).conjBy (l : G) = Source.UH H V₃ at hfix
    rw [hfix]
    exact commutator_self_eq_bot_iff.mpr inferInstance
  obtain ⟨k, hkseed, hkne, hkcomm⟩ := exists_seed_commuting_conjugate d hF9 c hH hDH hDg hcentral hn
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
  let zV : V := inclusion (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z
  let act (a : L) : MulAut V := V.normalizerMonoidHom ⟨a, d.normalizes_V (mem_sup_left a.property)⟩
  let u : V := act l zV
  let v : V := act k zV
  have hzV : zV ≠ 1 := by
    intro he
    have heval : (z : G) = 1 := congrArg (fun x : V => (x : G)) he
    exact hz (Subtype.ext heval)
  have hu : u ≠ 1 := fun he => hzV ((act l).injective (he.trans (map_one (act l)).symm))
  have hv : v ≠ 1 := fun he => hzV ((act k).injective (he.trans (map_one (act k)).symm))
  have point_image (a : L) : V₁.conjBy (a : G) = zpowers (act a zV : G) := by
    rw [point_zpowers d z hz, conjBy, MonoidHom.map_zpowers]
    rfl
  have huz : (u : G) ≠ (z : G) := by
    intro he
    apply hp
    rw [point_image l, show (act l zV : G) = (z : G) from he, ← point_zpowers d z hz]
  have hvz : (v : G) ≠ (z : G) := by
    intro he
    apply hkne
    rw [point_image k, show (act k zV : G) = (z : G) from he, ← point_zpowers d z hz]
  have huSeed : (u : G) ∈ V₃ := hseed (mem_map_of_mem _ z.property)
  have hvSeed : (v : G) ∈ V₃ := hkseed (mem_map_of_mem _ z.property)
  have hform (w : V) (hw : (w : G) ∈ V₃) :
      form (d.coordinate zV).toAdd (d.coordinate w).toAdd = 0 := by
    have hi : (d.coordinate w).toAdd ∈ Section07.NaturalAction.image (localNaturalSetup d) V₃ :=
      ⟨w, hw, rfl⟩
    rw [Section07.NaturalAction.seed_perpendicular] at hi
    exact hi _ ⟨zV, z.property, rfl⟩
  obtain ⟨a, haH, _, hau⟩ := local_point_stabilizer_transitive d hH z hz u v hu hv huz hvz
    ((hform u huSeed).trans (hform v hvSeed).symm)
  have hpoint : V₁.conjBy ((a : G) * (l : G)) = V₁.conjBy (k : G) := by
    rw [point_zpowers d z hz, conjBy, conjBy, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    congr 1
    change ((a : G) * (l : G)) * (z : G) * ((a : G) * (l : G))⁻¹ =
      (k : G) * (z : G) * (k : G)⁻¹
    calc
      _ = (a : G) * ((l : G) * (z : G) * (l : G)⁻¹) * (a : G)⁻¹ := by group
      _ = _ := hau
  have hU := conjugate_UH_eq_of_point_eq d hH _ _ hpoint
  have hfix : (Source.UH H V₃).conjBy (a : G) = Source.UH H V₃ :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V₃ H haH)
  have hzmap : (⁅Source.UH H V₃, (Source.UH H V₃).conjBy (l : G)⁆).map
      (MulAut.conj (a : G)).toMonoidHom = ⊥ := by
    rw [map_commutator]
    change ⁅(Source.UH H V₃).conjBy (a : G),
      ((Source.UH H V₃).conjBy (l : G)).conjBy (a : G)⁆ = ⊥
    rw [hfix, ← conjBy_mul, hU]
    exact hkcomm
  have hh := congrArg (fun P : Subgroup G => P.map (MulAut.conj (a : G)⁻¹).toMonoidHom) hzmap
  change ((⁅Source.UH H V₃, (Source.UH H V₃).conjBy (l : G)⁆).conjBy (a : G)).conjBy (a : G)⁻¹ = _ at hh
  simpa only [conjBy_inv, Subgroup.map_bot] using hh

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- A nonabelian source span supplies a nonorthogonal conjugate with
nontrivial action in the literal H/O₂(H), after excluding the entire
orthogonal orbit by the original endpoint commutation. -/
theorem exists_nonorthogonal_conjugate_star
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ∃ l : L, ¬ V₁.conjBy (l : G) ≤ V₃ ∧
      (Source.UH H V₃).conjBy (l : G) ≤ H ∧
      Source.starImage H ((Source.UH H V₃).conjBy (l : G)) ≠ ⊥ := by
  obtain ⟨l, hlH, hlstar⟩ := exists_nontrivial_conjugate_star d hF9 hH hn
  refine ⟨l, ?_, hlH, hlstar⟩
  intro hp
  have hc := seed_conjugates_commute d hF9 c hH hDH hDg hcentral hn l hp
  let A := (Source.UH H V₃).conjBy (l : G)
  have hpre := f9_commutatorPreimage_eq _ hF9 A hlH
  have hle : A ≤ commutatorPreimage A (Source.UH H V₃) V₁ := by
    apply le_commutatorPreimage le_rfl
    rw [commutator_comm, hc]
    exact bot_le
  have hQ : A ≤ Source.QH H := (hle.trans hpre.le).trans inf_le_right
  apply hlstar
  apply bot_unique
  rintro _ ⟨x, hx, rfl⟩
  change QuotientGroup.mk' (pCore 2 H) x = 1
  apply (QuotientGroup.eq_one_iff x).mpr
  obtain ⟨y, hy, he⟩ := hQ hx
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup BinaryPermutation CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

private theorem source_point_pairing_zero_iff
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (z : V₁) (hz : z ≠ 1) (w : V) :
    form (d.coordinate (inclusion (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z)).toAdd
      (d.coordinate w).toAdd = 0 ↔ (w : G) ∈ V₃ := by
  let zV : V := inclusion (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z
  constructor
  · intro hp
    have hi : (d.coordinate w).toAdd ∈ Section07.NaturalAction.image (localNaturalSetup d) V₃ := by
      rw [Section07.NaturalAction.seed_perpendicular]
      intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      have hh : a.val = 1 ∨ a.val = z := by
        obtain ⟨q, _, hq⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
        by_cases h1 : a.val = 1
        · exact Or.inl h1
        · exact Or.inr (congrArg Subtype.val
            ((hq ⟨a.val, ha⟩ (fun he => h1 (congrArg Subtype.val he))).trans (hq z hz).symm))
      rcases hh with he | he
      · have he' : a = 1 := Subtype.ext he
        rw [he', map_one]
        change form 0 _ = 0
        simp only [map_zero, LinearMap.zero_apply]
      · have he' : a = zV := Subtype.ext he
        rw [he']
        exact hp
    obtain ⟨v, hv, he⟩ := hi
    have he' : v = w := d.coordinate.injective he
    exact he' ▸ hv
  · intro hw
    have hi : (d.coordinate w).toAdd ∈ Section07.NaturalAction.image (localNaturalSetup d) V₃ :=
      ⟨w, hw, rfl⟩
    rw [Section07.NaturalAction.seed_perpendicular] at hi
    exact hi _ ⟨zV, z.property, rfl⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup BinaryPermutation CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [Finite G] in
private theorem star_bot_iff_core (A : Subgroup G) (hAH : A ≤ H) :
    Source.starImage H A = ⊥ ↔ A ≤ Source.QH H := by
  constructor
  · intro he x hx
    let v : H := ⟨x, hAH hx⟩
    have hv : QuotientGroup.mk' (pCore 2 H) v ∈ Source.starImage H A := mem_map_of_mem _ hx
    rw [he, mem_bot] at hv
    exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff v).mp hv)
  · intro hQ
    apply bot_unique
    rintro _ ⟨x, hx, rfl⟩
    change QuotientGroup.mk' (pCore 2 H) x = 1
    apply (QuotientGroup.eq_one_iff x).mpr
    obtain ⟨y, hy, he⟩ := hQ hx
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy

private theorem source_conjugate_in_H
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (l : L) : (Source.UH H V₃).conjBy (l : G) ≤ H := by
  have hQ : (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ≤ (T : Subgroup G) := by
    change (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).LT.pCoreIn 2 ≤ _
    rw [← hF9.sylow_centralizer]
    exact inf_le_left
  have hs := Section07.span_UH_L_le_core (localNaturalSetup d) hF9 (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  apply le_trans ?_ (hs.trans (hQ.trans hF9.T_le_H))
  rintro _ ⟨u, hu, rfl⟩
  exact subset_closure ⟨l, l.property, u, hu, rfl⟩

/-- Nontrivial star action is constant on the nonorthogonal point orbit.
This allows the source's involutive conjugator to be chosen afterwards. -/
theorem nonorthogonal_star_transfer
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hH : H = G₁) (l k : L)
    (hlseed : ¬ V₁.conjBy (l : G) ≤ V₃) (hkseed : ¬ V₁.conjBy (k : G) ≤ V₃)
    (hlstar : Source.starImage H ((Source.UH H V₃).conjBy (l : G)) ≠ ⊥) :
    Source.starImage H ((Source.UH H V₃).conjBy (k : G)) ≠ ⊥ := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
  let zV : V := inclusion (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z
  let act (a : L) : MulAut V := V.normalizerMonoidHom ⟨a, d.normalizes_V (mem_sup_left a.property)⟩
  let u : V := act l zV
  let v : V := act k zV
  have hzV : zV ≠ 1 := by
    intro he
    have heval : (z : G) = 1 := congrArg (fun x : V => (x : G)) he
    exact hz (Subtype.ext heval)
  have hu : u ≠ 1 := fun he => hzV ((act l).injective (he.trans (map_one (act l)).symm))
  have hv : v ≠ 1 := fun he => hzV ((act k).injective (he.trans (map_one (act k)).symm))
  have point_image (a : L) : V₁.conjBy (a : G) = zpowers (act a zV : G) := by
    rw [point_zpowers d z hz, conjBy, MonoidHom.map_zpowers]
    rfl
  have hout (a : L) (ha : ¬ V₁.conjBy (a : G) ≤ V₃) : (act a zV : G) ∉ V₃ := by
    intro hm
    apply ha
    rw [point_image a]
    exact zpowers_le.mpr hm
  have huz : (u : G) ≠ (z : G) := by
    intro he
    exact hout l hlseed (he ▸ d.plane_le_seed (d.line_le_plane z.property))
  have hvz : (v : G) ≠ (z : G) := by
    intro he
    exact hout k hkseed (he ▸ d.plane_le_seed (d.line_le_plane z.property))
  have hnonzero (a : L) (ha : ¬ V₁.conjBy (a : G) ≤ V₃) :
      form (d.coordinate zV).toAdd (d.coordinate (act a zV)).toAdd ≠ 0 :=
    fun he => hout a ha ((source_point_pairing_zero_iff d z hz (act a zV)).mp he)
  have hp : form (d.coordinate zV).toAdd (d.coordinate u).toAdd =
      form (d.coordinate zV).toAdd (d.coordinate v).toAdd := by
    have unique_nonzero : ∀ (x y : ZMod 2), x ≠ 0 → y ≠ 0 → x = y := by decide
    exact unique_nonzero _ _ (hnonzero l hlseed) (hnonzero k hkseed)
  obtain ⟨a, haH, _, hau⟩ := local_point_stabilizer_transitive d hH z hz u v hu hv huz hvz hp
  have hpoint : V₁.conjBy ((a : G) * (l : G)) = V₁.conjBy (k : G) := by
    rw [point_zpowers d z hz, conjBy, conjBy, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    congr 1
    change ((a : G) * (l : G)) * (z : G) * ((a : G) * (l : G))⁻¹ =
      (k : G) * (z : G) * (k : G)⁻¹
    calc
      _ = (a : G) * ((l : G) * (z : G) * (l : G)⁻¹) * (a : G)⁻¹ := by group
      _ = _ := hau
  have hU := conjugate_UH_eq_of_point_eq d hH _ _ hpoint
  intro hkstar
  have hkQ := (star_bot_iff_core _ (source_conjugate_in_H d hF9 k)).mp hkstar
  have heQ : (Source.QH H).conjBy (a : G)⁻¹ = Source.QH H :=
    mem_normalizer_iff_map_conj_eq.mp (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
      (D := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H) (H.inv_mem haH))
  have hlQ := map_mono (f := (MulAut.conj (a : G)⁻¹).toMonoidHom) hkQ
  change ((Source.UH H V₃).conjBy (k : G)).conjBy (a : G)⁻¹ ≤
    (Source.QH H).conjBy (a : G)⁻¹ at hlQ
  rw [← hU, conjBy_mul, conjBy_inv, heQ] at hlQ
  exact hlstar ((star_bot_iff_core _ (source_conjugate_in_H d hF9 l)).mpr hlQ)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The actual nonabelian case supplies the source conjugator with square in
the local two-core and nontrivial star image. All conjugations here are left
conjugations; the previously constructed source involution is inverted. -/
theorem exists_nonorthogonal_involutive_star
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ∃ l : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left l)) ^ 2 = 1 ∧
      V ≤ V₃ ⊔ V₁.conjBy (l : G) ∧ ¬ V₁.conjBy (l : G) ≤ V₃ ∧
      (Source.UH H V₃).conjBy (l : G) ≤ H ∧
      Source.starImage H ((Source.UH H V₃).conjBy (l : G)) ≠ ⊥ := by
  obtain ⟨j, hj, _, hjstar⟩ := exists_nonorthogonal_conjugate_star d hF9 c hH hDH hDg hcentral hn
  obtain ⟨k, hksq, hkspan⟩ := Section07.exists_chosen_conjugator (localNaturalSetup d)
  have hspan : V ≤ V₃ ⊔ V₁.conjBy ((k⁻¹ : L) : G) := hkspan
  have hout : ¬ V₁.conjBy ((k⁻¹ : L) : G) ≤ V₃ := by
    intro he
    have hVV₃ : V ≤ V₃ := hspan.trans (sup_le le_rfl he)
    have hEq : V₃ = V := le_antisymm d.seed_le hVV₃
    have hindex := Comparison.local_seed_index d
    rw [hEq, relIndex_self] at hindex
    contradiction
  refine ⟨k⁻¹, ?_, hspan, hout, source_conjugate_in_H d hF9 (k⁻¹), ?_⟩
  · rw [map_inv, map_inv, inv_pow, hksq, inv_one]
  · exact nonorthogonal_star_transfer d hF9 hH j (k⁻¹) hj hout hjstar

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
