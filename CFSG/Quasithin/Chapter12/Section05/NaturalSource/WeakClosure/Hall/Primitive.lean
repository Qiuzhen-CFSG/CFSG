module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.Inputs
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.FixedSubgroup
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.Complete

/-!
# Prime exclusion for the actual exterior Hall subgroup

For every prime p > 3 dividing the abelian E.2.2 Hall subgroup C, the
characteristic subgroup Ω₁(C) for p is nontrivial and elementary abelian.
The actual Frattini factorization proves that it permutes with T. The
nontrivial point V₁ and 12.2.6 place its image in N_G(V). The two explicit
source obligations then put its full normalizer in M, contrary to the proved
full-Hall version of 4.4.13(1). Oddness leaves only the prime three.

This conditional deduction does not prove the two specialized source inputs.
The structural 12.2.2 input is supplied by qt-d-1222-source, with its eventual
specialization discharged by qt-d-1251-source.
Source: Aschbacher--Smith 12.2.11(a), printed pp.798--799.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterB

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Apply 12.2.6 with the literal nontrivial line V₁ in the role of U. -/
theorem exterior_overlap_normalizes
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {H : Subgroup G} (hHGi : H ≤ s.marking.Gi 1) :
    H ⊓ s.marking.M ≤ normalizer (V : Set G) := by
  have hpoint : s.marking.Vi 1 ≠ ⊥ := by
    intro he
    exact s.marking.z_ne_one (mem_bot.mp (he ▸ s.marking.z_mem_V₁))
  exact (le_inf inf_le_right (inf_le_left.trans hHGi)).trans
    (inf_normalizer_le_of_trivial_intersections
      ((structural L h).2.2 V D).2.2.1 hpoint (s.marking.subspace_le _))

/-- The actual E.2.2 Hall subgroup is a three-group once the two independent
specialized source obligations are proved. The escape is for the full Hall
subgroup, not only for the cyclic torus inside it. -/
theorem exterior_hall_three_of_controls
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    (control : ExteriorOddNormalizerControl s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H) :
    IsPGroup 3 d.witness.abelianGroup := by
  classical
  have hprime : (Nat.card d.witness.abelianGroup).primeFactors ⊆ ({3} : Finset ℕ) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ Nat.card d.witness.abelianGroup := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      intro he
      exact d.witness.odd.not_two_dvd_nat (he ▸ hpd)
    by_cases hp3 : p = 3
    · simp [hp3]
    have hpgt : 3 < p := by have := hpp.two_le; omega
    let : Fact p.Prime := ⟨hpp⟩
    let := d.witness.abelian
    let E := omega₁ d.witness.abelianGroup (p := p)
    let : E.Characteristic := omega₁_characteristic d.witness.abelianGroup
    let : IsElementaryAbelian p E :=
      IsElementaryAbelian.omega₁_of_isMulCommutative d.witness.abelianGroup
    let A₀ := E.map d.witness.abelianGroup.subtype
    let : IsElementaryAbelian p A₀ := IsElementaryAbelian.map _
    have hA₀ : A₀ ≠ ⊥ := omega₁_map_subtype_ne_bot d.witness.abelianGroup p hpd
    have hA₀C : A₀ ≤ d.witness.abelianGroup := map_subtype_le _
    have hperm₀ : (A₀ : Set H) * ((T.subtype hH.1.1.2) : Set H) =
        ((T.subtype hH.1.1.2) : Set H) * (A₀ : Set H) :=
      permutes_of_factorization d.frattini (hA₀C.trans d.normalizes)
        (inf_le_right.trans (normalizer_le_normalizer_characteristic_image
          d.witness.abelianGroup E))
    let A := A₀.map H.subtype
    have hA : A ≠ ⊥ := fun he =>
      hA₀ ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he)
    have hAe : IsElementaryAbelian p A := IsElementaryAbelian.map _
    have hCM : d.witness.abelianGroup ≤ s.marking.M.subgroupOf H := hmax ▸ d.hall_le
    have hAM : A ≤ s.marking.M := map_le_iff_le_comap.mpr
      (hA₀C.trans hCM)
    have hANV : A ≤ normalizer (V : Set G) :=
      (le_inf (map_subtype_le _) hAM).trans
        (exterior_overlap_normalizes s h structural hHGi)
    have hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) := by
      have he := congrArg (Set.image H.subtype) hperm₀
      change H.subtype '' ((A₀ : Set H) *
        ((T : Subgroup G).subgroupOf H : Set H)) =
        H.subtype '' (((T : Subgroup G).subgroupOf H : Set H) * (A₀ : Set H)) at he
      simpa only [Set.image_mul, ← Subgroup.coe_map, Sylow.coe_coe,
        map_subgroupOf_eq_of_le hH.1.1.2] using he
    have hAV : A ≤ centralizer (V : Set G) := action p hpp hpgt A hA hAe hAM hANV hperm
    have hNA : normalizer (A : Set G) ≤ s.marking.M :=
      control p hpp hpgt A hA hAe hAM hAV
    have hcore : pCore 2 H ≠ ⊥ := by
      intro he
      apply hH.1.1.1
      change (pCore 2 H).map H.subtype = ⊥
      rw [he, Subgroup.map_bot]
    have hgen := NormalizerEscape.source4413One_knownSimple G h.simpleQTKE
      H inferInstance inferInstance H.subtype H.subtype_injective hcore hlarge
      (T.subtype hH.1.1.2) hP d.witness.abelianGroup d.hall_le d.hall p hpp
      A₀ inferInstance hA₀C hperm₀
    have hN₀ : normalizer (A₀ : Set H) ≤ s.marking.M.subgroupOf H := by
      intro x hx
      exact hNA (A₀.le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx))
    have htop : (⊤ : Subgroup H) ≤ s.marking.M.subgroupOf H := by
      rw [← hgen]
      exact sup_le (le_of_eq hmax) hN₀
    exact (hH.1.2 (subgroupOf_eq_top.mp (top_unique htop))).elim
  rw [isPGroup_iff_card_dvd_pow]
  exact (Nat.exists_dvd_pow_iff (Nat.card_pos.ne') (by decide : (3 : ℕ) ≠ 0)).mpr
    (by
      intro q hq
      have hq3 : q = 3 := Finset.mem_singleton.mp (hprime hq)
      subst q
      norm_num)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
