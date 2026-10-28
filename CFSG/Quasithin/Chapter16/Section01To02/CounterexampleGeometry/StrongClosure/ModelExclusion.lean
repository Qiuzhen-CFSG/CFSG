module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.IntersectionResidual.ModelFacts
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredCore
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import BenderSuzuki.Converse.PSL2
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki
public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.DihedralCore
public import CFSG.Quasithin.ClassicalModels
public import Mathlib.Algebra.CharP.CharAndCard
public import Theory.GroupTheory.PerfectSylowTwo
public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification

/-!
# Sylow model inputs for Lemma 16.2.10

This module supplies the concrete model facts consumed by the strong-closure
argument.  The Sylow subgroup is the actual intersection `T ∩ L`; all model
claims are transported through the displayed group isomorphisms.  No rank or
model conclusion is taken as a field of the component alternative.

For a covered Suzuki component, the quotient map gives a surjection from
the component Sylow onto the actual order-64 Suzuki root subgroup. This
retains the central kernel rather than identifying the cover with its quotient.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, Lemmas 16.2.5 and 16.2.10,
printed pp.1174–1176.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.ModelExclusion

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open BenderSuzuki.PFchapter1section1
open scoped MatrixGroups

universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {z : G} {L : Subgroup G}

/-- A four-group in a finite group can be moved into any prescribed Sylow
2-subgroup.  This is the only Sylow transport used below. -/
theorem twoRank_sylow {X : Type u} [Group X] [Finite X]
    (hX : TwoRankAtLeastTwo X) (P : Sylow 2 X) :
    TwoRankAtLeastTwo P := by
  rcases hX with ⟨E, hEcard, hEsq⟩
  have hEP : IsPGroup 2 E := IsPGroup.of_card (p := 2) (G := E) (n := 2) (by
    simp [hEcard])
  obtain ⟨S, hES⟩ := hEP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S P
  let fX : E →* X := (MulAut.conj g).toMonoidHom.comp E.subtype
  have hfX : Function.Injective fX := by
    intro a b hab
    apply Subtype.ext
    apply (MulAut.conj g).injective
    simpa [fX] using hab
  have hfP : ∀ e : E, fX e ∈ (P : Subgroup X) := by
    intro e
    rw [show (P : Subgroup X) = ((g • S : Sylow 2 X) : Subgroup X) from
      congrArg (fun Q : Sylow 2 X => (Q : Subgroup X)) hg.symm]
    rw [Sylow.coe_subgroup_smul]
    exact Set.mem_smul_set.mpr ⟨e, hES e.property, rfl⟩
  let f : E →* P := fX.codRestrict P hfP
  have hf : Function.Injective f := by
    intro a b hab
    exact hfX (by simpa [f] using congrArg Subtype.val hab)
  let EP : Subgroup P := (⊤ : Subgroup E).map f
  have hEPcard : Nat.card EP = 4 := by
    rw [Subgroup.card_map_of_injective hf]
    simpa using hEcard
  refine ⟨EP, hEPcard, ?_⟩
  rintro ⟨x, hx⟩
  rcases hx with ⟨e, _he, rfl⟩
  apply Subtype.ext
  change (f e) ^ 2 = (1 : P)
  rw [← map_pow]
  simpa using congrArg f (hEsq e)

private theorem exists_field_element_ne_zero_one {F : Type*} [Field F] [Finite F]
    (hcard : 2 < Nat.card F) : ∃ y : F, y ≠ 0 ∧ y ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  by_contra hn
  have hzeroone : ∀ x : F, x = 0 ∨ x = 1 := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      by_contra hx1
      exact hn ⟨x, hx, hx1⟩
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro x hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hzeroone x
  have hc := Finset.card_le_card hsub
  rw [Finset.card_univ] at hc
  have hc' : Nat.card F ≤ 2 := by simpa [Nat.card_eq_fintype_card] using hc
  omega

private theorem psl2_twoRank_even {F : Type*} [Field F] [Finite F]
    [CharP F 2] (hcard : 2 < Nat.card F) :
    TwoRankAtLeastTwo (BenderSuzuki.Converse.PSL2 F) := by
  obtain ⟨y, hy0, hy1⟩ := exists_field_element_ne_zero_one hcard
  exact BenderSuzuki.Converse.twoRank y hy0 hy1


private theorem field_odd_prime_power {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) : GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  let := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hcard : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  refine ⟨ringChar F, n, hp, ?_, n.pos, hcard⟩
  apply hp.odd_of_ne_two
  intro htwo
  rw [htwo] at hcard
  have heven : Even (Nat.card F) := by
    rw [hcard]
    exact (Nat.even_pow.mpr ⟨by decide, n.pos.ne'⟩)
  exact (Nat.not_even_iff_odd.mpr hodd) heven

private theorem psl2_sylow_twoRank_odd {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (_hcard : 2 < Nat.card F)
    (P : Sylow 2 (BenderSuzuki.Converse.PSL2 F)) :
    TwoRankAtLeastTwo P := by
  let hpp := field_odd_prime_power hodd
  rcases GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hpp P with
    ⟨m, hm, ⟨e⟩⟩
  obtain ⟨V, hVP, hV⟩ :=
    GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
      (P : Subgroup (BenderSuzuki.Converse.PSL2 F)) hm e
  refine ⟨V.subgroupOf (P : Subgroup _), ?_, ?_⟩
  · exact (Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv).trans hV.card_four
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    let xv : V := ⟨(x : BenderSuzuki.Converse.PSL2 F), x.property⟩
    have hxv := IsKleinFour.mul_self xv
    change ((x : BenderSuzuki.Converse.PSL2 F) ^ 2) = (1 : BenderSuzuki.Converse.PSL2 F)
    simpa [xv, pow_two] using congrArg Subtype.val hxv

/-- A linear odd model has an elementary four in every Sylow two-subgroup. -/
theorem linear_odd_sylow_rank {X : Type u} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hoddp : Odd p)
    (h : ClassicalGroup.IsPSL X 2 p) (P : Sylow 2 X) :
    TwoRankAtLeastTwo P := by
  obtain ⟨F, _, _, hFcard, ⟨e⟩⟩ := h
  have hoddF : Odd (Nat.card F) := by rw [hFcard]; exact hoddp
  have hcardF : 2 < Nat.card F := by
    rw [hFcard]
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      rcases hoddp with ⟨k, hk⟩
      omega
    have hp1 : 2 ≤ p := hp.two_le
    omega
  let Q : Sylow 2 (BenderSuzuki.Converse.PSL2 F) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ := psl2_sylow_twoRank_odd hoddF hcardF Q
  have ePQ : P ≃* Q := by
    let e0 : P ≃* (P.map e.toMonoidHom) :=
      (P : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective
    change P ≃* (P.map e.toMonoidHom)
    exact e0
  exact hQ.map_of_injective ePQ.symm.toMonoidHom ePQ.symm.injective

/-- A linear even model has an elementary four in every Sylow two-subgroup. -/
theorem linear_even_sylow_rank {X : Type u} [Group X] [Finite X]
    {n : ℕ} (hn : 2 ≤ n) (h : ClassicalGroup.IsPSL X 2 (2 ^ n))
    (P : Sylow 2 X) : TwoRankAtLeastTwo P := by
  obtain ⟨F, _, _, hFcard, ⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ n := by
    simpa only [Nat.card_eq_fintype_card] using hFcard
  let : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  have hq : 2 < Nat.card F := by
    rw [hFcard]
    have hp : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    norm_num at hp ⊢
    omega
  have hr : TwoRankAtLeastTwo (BenderSuzuki.Converse.PSL2 F) :=
    psl2_twoRank_even hq
  let Q : Sylow 2 (BenderSuzuki.Converse.PSL2 F) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ := twoRank_sylow hr Q
  let ePQ : P ≃* Q := by
    let e0 : P ≃* (P.map e.toMonoidHom) :=
      (P : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective
    change P ≃* (P.map e.toMonoidHom)
    exact e0
  exact hQ.map_of_injective ePQ.symm.toMonoidHom ePQ.symm.injective

private theorem suzuki_model_twoRank {m : ℕ} (hm : 1 ≤ m) :
    TwoRankAtLeastTwo (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  have h := BenderSuzuki.ZD.suzuki_identity_fixedSubgroup_twoRank m hm
  have htop :
      (1 : MulAut (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)).fixedSubgroup = ⊤ := by
    ext x
    simp [MulAut.mem_fixedSubgroup]
  rw [htop] at h
  let e : (⊤ : Subgroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m := Subgroup.topEquiv
  exact h.map_of_injective e.toMonoidHom e.injective

private theorem suzuki_sylow_twoRank {X : Type u} [Group X] [Finite X]
    {m : ℕ} (hm : 1 ≤ m)
    (h : Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (P : Sylow 2 X) : TwoRankAtLeastTwo P := by
  obtain ⟨e⟩ := h
  let Q : Sylow 2 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ := twoRank_sylow (suzuki_model_twoRank hm) Q
  have ePQ : P ≃* Q := by
    let e0 : P ≃* (P.map e.toMonoidHom) :=
      (P : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective
    change P ≃* (P.map e.toMonoidHom)
    exact e0
  exact hQ.map_of_injective ePQ.symm.toMonoidHom ePQ.symm.injective

theorem component_sylow_equiv
    (h : CentralComponentSetup T z L) :
    ∃ P : Sylow 2 L, Nonempty (P ≃* componentSylow T L) := by
  obtain ⟨P, hP⟩ := h.exists_component_sylow
  have hmap : (P : Subgroup L).map L.subtype = componentSylow T L := by
    rw [hP]
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.property⟩
    · rintro ⟨hxT, hxL⟩
      exact ⟨⟨x, hxL⟩, hxT, rfl⟩
  let e0 : P ≃* (P : Subgroup L).map L.subtype :=
    (P : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective
  exact ⟨P, ⟨e0.trans (MulEquiv.subgroupCongr hmap)⟩⟩

theorem component_sylow_twoRank_linear_even
    (h : CentralComponentSetup T z L) {n : ℕ} (hn : 2 ≤ n)
    (iso : ClassicalGroup.IsPSL L 2 (2 ^ n)) :
    TwoRankAtLeastTwo (componentSylow T L) := by
  obtain ⟨P, ⟨e⟩⟩ := component_sylow_equiv h
  exact (linear_even_sylow_rank hn iso P).map_of_injective e.toMonoidHom e.injective

theorem component_sylow_twoRank_linear_odd
    (h : CentralComponentSetup T z L) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (iso : ClassicalGroup.IsPSL L 2 p) :
    TwoRankAtLeastTwo (componentSylow T L) := by
  obtain ⟨P, ⟨e⟩⟩ := component_sylow_equiv h
  exact (linear_odd_sylow_rank hp hodd iso P).map_of_injective e.toMonoidHom e.injective

theorem component_sylow_twoRank_suzuki
    (h : CentralComponentSetup T z L) {m : ℕ} (hm : 1 ≤ m)
    (iso : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    TwoRankAtLeastTwo (componentSylow T L) := by
  obtain ⟨P, ⟨e⟩⟩ := component_sylow_equiv h
  exact (suzuki_sylow_twoRank hm iso P).map_of_injective e.toMonoidHom e.injective

open BenderSuzuki.MatrixGroups in
/-- The image Sylow is conjugate to the standard Suzuki root subgroup. The
map is surjective and retains the whole two-core as a possible kernel. -/
theorem covered_sylow_surjects_root
    (h : CentralComponentSetup T z L)
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup 1)) :
    ∃ f : componentSylow T L →* SuzukiRootSubgroup 1, Function.Surjective f := by
  obtain ⟨e⟩ := iso
  obtain ⟨P, ⟨eP⟩⟩ := component_sylow_equiv h
  let π : L →* SuzukiMatrixGroup 1 := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q : Sylow 2 (SuzukiMatrixGroup 1) := P.mapSurjective hπ
  let f : P →* Q := (π.comp (P : Subgroup L).subtype).codRestrict Q
    (fun x => ⟨x, x.property, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow 1 (by decide)
  let eQ : Q ≃* SuzukiRootSubgroup 1 :=
    (Q.equiv R).trans (MulEquiv.subgroupCongr hR)
  exact ⟨eQ.toMonoidHom.comp (f.comp eP.symm.toMonoidHom),
    eQ.surjective.comp (hf.comp eP.symm.surjective)⟩

omit [Finite G] in
/-- Conjugation inside T transports the actual intersections, including
their cardinalities and elementary subgroups. -/
theorem component_sylow_swap_equiv {u : G} (hu : u ∈ T) :
    Nonempty (componentSylow T L ≃* componentSylow T (conjugate L u)) := by
  have hT : conjugate (T : Subgroup G) u = T :=
    (mem_normalizer_iff_conjugate_eq _ _).mp (Subgroup.le_normalizer hu)
  have hA : conjugate (componentSylow T L) u =
      componentSylow T (conjugate L u) := by
    change ((T : Subgroup G) ⊓ L).map (MulAut.conj u⁻¹).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj u⁻¹).injective]
    change conjugate (T : Subgroup G) u ⊓ conjugate L u = _
    rw [hT]
    rfl
  exact ⟨((MulAut.conj u⁻¹).subgroupMap (componentSylow T L)).trans
    (MulEquiv.subgroupCongr hA)⟩

omit [Finite G] in
/-- A four in the first Sylow intersection gives a four in the second. -/
theorem swapped_sylow_twoRank {u : G} (hu : u ∈ T)
    (hA : TwoRankAtLeastTwo (componentSylow T L)) :
    TwoRankAtLeastTwo (componentSylow T (conjugate L u)) := by
  obtain ⟨e⟩ := component_sylow_swap_equiv (L := L) hu
  exact hA.map_of_injective e.toMonoidHom e.injective

private theorem nontrivial_of_twoRank {X : Type*} [Group X] [Finite X]
    (h : TwoRankAtLeastTwo X) : Nontrivial X := by
  obtain ⟨E, hE, _⟩ := h
  have hc := Nat.card_le_card_of_injective E.subtype E.subtype_injective
  exact Finite.one_lt_card_iff_nontrivial.mp (by omega)

/-- Every genuine component alternative gives a nontrivial Sylow intersection.
The covered case uses the nontrivial actual quotient root group. -/
theorem component_sylow_nontrivial
    (h : CentralComponentSetup T z L) (a : ComponentAlternative L) :
    Nontrivial (componentSylow T L) := by
  cases a with
  | linear_even n hn iso =>
    exact nontrivial_of_twoRank (component_sylow_twoRank_linear_even h hn iso)
  | linear_odd p hp ho iso =>
    exact nontrivial_of_twoRank (component_sylow_twoRank_linear_odd h hp ho iso)
  | suzuki m hm iso =>
    exact nontrivial_of_twoRank (component_sylow_twoRank_suzuki h hm iso)
  | covered_suzuki_eight _ iso =>
    obtain ⟨f, hf⟩ := covered_sylow_surjects_root h iso
    have hc := BenderSuzuki.MatrixGroups.suzukiRootSubgroup_card 1 (by decide)
    let : Nontrivial (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup 1) :=
      Finite.one_lt_card_iff_nontrivial.mp (by norm_num [hc])
    exact hf.nontrivial

private theorem perfect_sylow_eq_bot_of_central {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (P : Sylow 2 X) (hc : (P : Subgroup X) ≤ center X) :
    (P : Subgroup X) = ⊥ := by
  let : IsMulCommutative P := { is_comm := ⟨fun x y =>
    Subtype.ext (mem_center_iff.mp (hc y.property) x)⟩ }
  have hn : normalizer (P : Set X) ≤ centralizer (P : Set X) := by
    intro x _
    exact mem_centralizer_iff.mpr (fun y hy => (mem_center_iff.mp (hc hy) x).symm)
  let f := MonoidHom.transferSylow P hn
  have hb : Function.Bijective (f.domRestrict (P : Subgroup X)) :=
    (MonoidHom.transferSylow_domRestrict_eq_pow P hn).symm ▸
      (P.isPGroup'.powEquiv' P.not_dvd_index).bijective
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := hb.surjective y
    exact ⟨x, hx⟩
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective hf
  exact Subgroup.card_eq_one.mp (Nat.card_unique : Nat.card P = 1)

/-- The two Sylow intersections cannot be nested. A containment would make
the first central in the perfect component; Burnside transfer then makes it
trivial, contrary to its genuine model. -/
theorem sylow_noncontainment {u : G}
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u)
    (a : ComponentAlternative L) :
    ¬ componentSylow T L ≤ componentSylow T (conjugate L u) ∧
      ¬ componentSylow T (conjugate L u) ≤ componentSylow T L := by
  let := h.component.quasisimple
  let := component_sylow_nontrivial h a
  have hfirst : ¬ componentSylow T L ≤ componentSylow T (conjugate L u) := by
    intro hle
    obtain ⟨P, hP⟩ := h.exists_component_sylow
    have hc : conjugate L u ≤ centralizer (L : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [commutator_comm]
      exact o.commute h
    have hPc : (P : Subgroup L) ≤ center L := by
      intro x hx
      have hxT : (x : G) ∈ T := by
        change x ∈ (P : Subgroup L) at hx
        rwa [hP] at hx
      have hxC := hc (hle ⟨hxT, x.property⟩).2
      exact mem_center_iff.mpr fun y =>
        Subtype.ext (mem_centralizer_iff.mp hxC y y.property)
    have hb := perfect_sylow_eq_bot_of_central P hPc
    have hA : componentSylow T L = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hxP : (⟨x, hx.2⟩ : L) ∈ (P : Subgroup L) := by
        rw [hP]
        exact hx.1
      rw [hb] at hxP
      exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hxP))
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hA
  refine ⟨hfirst, ?_⟩
  intro hle
  obtain ⟨e⟩ := component_sylow_swap_equiv (L := L) o.mem_sylow
  have heq := eq_of_le_of_card_ge hle (Nat.card_congr e.toEquiv).le
  exact hfirst heq.symm.le

omit [Finite G] in
/-- The intersection of the Sylow subgroups lies in the embedded center of
the component, since the two distinct components commute. -/
theorem sylow_intersection_le_center {u : G}
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u) :
    componentSylow T L ⊓ componentSylow T (conjugate L u) ≤ (center L).map L.subtype := by
  have hc : conjugate L u ≤ centralizer (L : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [commutator_comm]
    exact o.commute h
  intro x hx
  refine ⟨⟨x, hx.1.2⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  exact Subtype.ext (mem_centralizer_iff.mp (hc hx.2.2) y y.property)

omit [Finite G] in
/-- A nontrivial intersection eliminates all three center-free alternatives
of 16.2.5, leaving the precise covered Sz(8) quotient. -/
theorem nontrivial_intersection_forces_cover {u : G}
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u)
    (a : ComponentAlternative L)
    (hne : componentSylow T L ⊓ componentSylow T (conjugate L u) ≠ ⊥) :
    pCore 2 L ≠ ⊥ ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) := by
  let := h.component.quasisimple
  have hcenter : center L ≠ ⊥ := by
    intro he
    apply hne
    apply le_bot_iff.mp
    simpa only [he, Subgroup.map_bot] using sylow_intersection_le_center h o
  cases a with
  | linear_even n hn iso => exact (hcenter (center_eq_bot_of_linear_even hn iso)).elim
  | suzuki m hm iso => exact (hcenter (center_eq_bot_of_suzuki (by omega) iso)).elim
  | linear_odd p _ ho iso => exact (hcenter (center_eq_bot_of_linear_odd ho iso)).elim
  | covered_suzuki_eight hc iso => exact ⟨hc, iso⟩

private theorem quotient_card_le_eight {X Y : Type*} [Group X] [Group Y]
    [Finite X] (A : Subgroup X) [IsCyclic A]
    (hi : A.index ≤ 2) (f : X →* Y) (hf : Function.Surjective f)
    (hpow : ∀ y : Y, y ^ 4 = 1) : Nat.card Y ≤ 8 := by
  let B := A.map f
  let : IsCyclic B := isCyclic_of_surjective (f.subgroupMap A) (f.subgroupMap_surjective A)
  have hc : Nat.card B ≤ 4 := by
    apply Nat.le_of_dvd (by decide)
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro b
    exact Subtype.ext (hpow b.val)
  have hidx : B.index ≤ 2 := (Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite : A.index ≠ 0))
    (A.index_map_dvd hf)).trans hi
  have hh := B.card_mul_index
  nlinarith

private theorem dihedral_has_cyclic_index_le_two (n : ℕ) [NeZero n] :
    ∃ A : Subgroup (DihedralGroup n), IsCyclic A ∧ A.index ≤ 2 := by
  let A := zpowers (DihedralGroup.r 1 : DihedralGroup n)
  refine ⟨A, inferInstance, ?_⟩
  have hh := A.card_mul_index
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at hh
  have hn := NeZero.pos n
  nlinarith

private theorem quaternion_has_cyclic_index_le_two (n : ℕ) [NeZero n] :
    ∃ A : Subgroup (QuaternionGroup n), IsCyclic A ∧ A.index ≤ 2 := by
  let A := zpowers (QuaternionGroup.a 1 : QuaternionGroup n)
  refine ⟨A, inferInstance, ?_⟩
  have hh := A.card_mul_index
  rw [Nat.card_zpowers, QuaternionGroup.orderOf_a_one,
    Nat.card_eq_fintype_card, QuaternionGroup.card] at hh
  have hn := NeZero.pos n
  nlinarith

private theorem semidihedral_has_cyclic_index_le_two (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : Subgroup (Semidihedral.StandardModel n hn), IsCyclic A ∧ A.index ≤ 2 := by
  let A := zpowers (Semidihedral.standardRotation n hn)
  refine ⟨A, inferInstance, ?_⟩
  have hh := A.card_mul_index
  rw [Nat.card_zpowers, Semidihedral.standardRotation_order, Semidihedral.standardModel_card] at hh
  have he : 2 ^ n = 2 ^ (n-1) * 2 := by
    conv_lhs => rw [show n = n-1+1 by omega, pow_succ]
  rw [he] at hh
  have hp : 0 < 2 ^ (n-1) := by positivity
  nlinarith

open BenderSuzuki.MatrixGroups in
private theorem no_root_quotient_of_cyclic_index_le_two
    {X : Type*} [Group X] [Finite X] (A : Subgroup X) [IsCyclic A]
    (hi : A.index ≤ 2) (f : X →* SuzukiRootSubgroup 1)
    (hf : Function.Surjective f) : False := by
  have hc := quotient_card_le_eight A hi f hf (suzukiRootSubgroup_pow_four 1 (by decide))
  rw [suzukiRootSubgroup_card 1 (by decide)] at hc
  norm_num at hc

/-- The covered component also has a four in its Sylow subgroup. Otherwise
the cyclic/quaternion theorem gives a cyclic subgroup of index at most two,
whose exponent-four quotient would have order at most eight, not 64. -/
theorem component_sylow_twoRank_covered
    (h : CentralComponentSetup T z L)
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    TwoRankAtLeastTwo (componentSylow T L) := by
  obtain ⟨f, hf⟩ := covered_sylow_surjects_root h iso
  by_contra hr
  have hp : IsPGroup 2 (componentSylow T L) := T.isPGroup'.to_le inf_le_left
  have hfour : ∀ E : Subgroup (componentSylow T L),
      IsElementaryAbelian 2 E → Nat.card E ≠ 4 := by
    intro E hE hc
    let : IsElementaryAbelian 2 E := hE
    exact hr ⟨E, hc, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E)⟩
  rcases hp.isCyclic_or_quaternion_of_no_elementary_four hfour with hc | ⟨n, _, ⟨e⟩⟩
  · let : IsCyclic (componentSylow T L) := hc
    exact no_root_quotient_of_cyclic_index_le_two ⊤ (by simp) f hf
  · obtain ⟨A, hA, hi⟩ := quaternion_has_cyclic_index_le_two (2 ^ (n - 2))
    let : IsCyclic A := hA
    exact no_root_quotient_of_cyclic_index_le_two A hi (f.comp e.symm.toMonoidHom)
      (hf.comp e.symm.surjective)

/-- The actual quotient Sylow excludes both Asc75 two-group models without
requiring a rank calculation for the cover or an involution-lifting theorem. -/
theorem covered_sylow_not_dihedral_or_semidihedral
    (h : CentralComponentSetup T z L)
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    ¬ Asc75.DihedralOrSemidihedral (componentSylow T L) := by
  obtain ⟨f, hf⟩ := covered_sylow_surjects_root h iso
  rintro (⟨n, _, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩)
  · obtain ⟨A, hA, hi⟩ := dihedral_has_cyclic_index_le_two (2 ^ n)
    let : IsCyclic A := hA
    exact no_root_quotient_of_cyclic_index_le_two A hi (f.comp e.symm.toMonoidHom)
      (hf.comp e.symm.surjective)
  · obtain ⟨A, hA, hi⟩ := semidihedral_has_cyclic_index_le_two n hn
    let : IsCyclic A := hA
    exact no_root_quotient_of_cyclic_index_le_two A hi (f.comp e.symm.toMonoidHom)
      (hf.comp e.symm.surjective)

/-- Every alternative of 16.2.5 gives the first elementary-four input of
Asc75. No rank or covering-structure premise is added. -/
theorem component_sylow_twoRank
    (h : CentralComponentSetup T z L) (a : ComponentAlternative L) :
    TwoRankAtLeastTwo (componentSylow T L) := by
  cases a with
  | linear_even n hn iso => exact component_sylow_twoRank_linear_even h hn iso
  | linear_odd p hp ho iso => exact component_sylow_twoRank_linear_odd h hp ho iso
  | suzuki m hm iso => exact component_sylow_twoRank_suzuki h hm iso
  | covered_suzuki_eight _ iso => exact component_sylow_twoRank_covered h iso

/-- The exceptional intersection in Asc75 is incompatible with the genuine
component list: a nontrivial intersection forces the covered Suzuki branch,
and its quotient Sylow is too large to be a quotient of either model. -/
theorem intersection_excludes_Asc75_model {u : G}
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u)
    (a : ComponentAlternative L)
    (hne : componentSylow T L ⊓ componentSylow T (conjugate L u) ≠ ⊥) :
    ¬ Asc75.DihedralOrSemidihedral (componentSylow T L) :=
  covered_sylow_not_dihedral_or_semidihedral h
    (nontrivial_intersection_forces_cover h o a hne).2

/-- All model inputs consumed by the source-hypothesis preparation for
16.2.10. Both Sylow groups are the actual intersections with T. -/
theorem source_model_inputs {u : G}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a : ComponentAlternative L) :
    TwoRankAtLeastTwo (componentSylow T L) ∧
    TwoRankAtLeastTwo (componentSylow T (conjugate L u)) ∧
    ¬ componentSylow T L ≤ componentSylow T (conjugate L u) ∧
    ¬ componentSylow T (conjugate L u) ≤ componentSylow T L ∧
    (componentSylow T L ⊓ componentSylow T (conjugate L u) ≠ ⊥ →
      ¬ Asc75.DihedralOrSemidihedral (componentSylow T L)) := by
  have hr := component_sylow_twoRank c.localSetup a
  have hn := sylow_noncontainment c.localSetup o a
  exact ⟨hr, swapped_sylow_twoRank o.mem_sylow hr, hn.1, hn.2,
    intersection_excludes_Asc75_model c.localSetup o a⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.ModelExclusion
end
