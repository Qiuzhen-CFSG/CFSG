module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SevenReduction
public import Theory.SpecificGroups.Alternating.SevenFiveRadical

/-!
# The actual transposition geometry of the fixed A₇ component

The full group-model reduction identifies Lᵤ* as A₇. Its faithful permutation
extension carries the nontrivial radical to a two-subgroup normalized by
the marked stabilizer, whose order has a factor five. The intrinsic seven-point
calculation makes that radical a transposition subgroup. The original
Thompson-normalizer control then identifies the marked stabilizer with its
full centralizer in Lᵤ*. All conjugation equations retain the original maps.

The original two-core quotient also has trivial center: A.3.6 bounds its
order by one or three, and a cubic central element would lift to the forbidden
section centralizer. Thus the literal core-to-star map is injective.

This proves the group and geometric part of the surviving C.2.7(b) row.
Reconstruction of the original block module remains separate and is consumed
in OriginalInputs/LocalAlternatives/SevenBlock. Source: Aschbacher--Smith
C.2.7, pp.145--147, and 14.7.68(2), pp.1071--1072.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Nonquasisimple
structure SevenGeometry (d : Data T L V F W) (u : F.U) (Lu : Subgroup G) where
  component : starImage Lu (d.fixedCore u) Lu ≃* alternatingGroup (Fin 7)
  generator : StarQuotient Lu (d.fixedCore u)
  transposition : Equiv.Perm (Fin 7)
  order : orderOf generator = 2
  radical : starImage Lu (d.fixedCore u) (d.fixedCore u) = closure {generator}
  swap : transposition.IsSwap
  action : ∀ k k' : starImage Lu (d.fixedCore u) Lu,
    (k' : StarQuotient Lu (d.fixedCore u)) = generator * k * generator⁻¹ ↔
      (component k' : Equiv.Perm (Fin 7)) = transposition * component k * transposition⁻¹
  centralizer : starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u) =
    starImage Lu (d.fixedCore u) Lu ⊓ centralizer
      (starImage Lu (d.fixedCore u) (d.fixedCore u) : Set (StarQuotient Lu (d.fixedCore u)))
end Nonquasisimple

namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_coreToStar_injective_of_source
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Function.Injective (coreToStar (d.fixedCore_normalizes_component u h)) := by
  have input := d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
    d.point_mem_U_commutator_K
  have hc : center (Lu ⧸ pCore 2 Lu) = ⊥ := by
    apply card_eq_one.mp
    rcases ChapterC.C27Source.coreQuotient_center_card_from_source input with hc | hc
    · exact hc
    · obtain ⟨y,_,hy,hyc⟩ := d.fixedComponent_exists_orderThree_of_quotient_center u h
        (by rw [hc])
      exact (d.no_orderThree_sectionCentralizer h.normalizer y hy hyc).elim
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique (hc ▸ ChapterC.C27Source.coreToStar_ker_central_from_source input)

theorem fixedComponent_C27_core_alternatingSeven
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨e⟩ := d.fixedComponent_C27_star_alternatingSeven u h
  exact ⟨(MulEquiv.ofBijective (coreToStar (d.fixedCore_normalizes_component u h))
    ⟨d.fixedComponent_coreToStar_injective_of_source u h,coreToStar_surjective _⟩).trans e⟩

theorem fixedComponent_C27_seven_geometry
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Nonempty (Nonquasisimple.SevenGeometry d u Lu) := by
  obtain ⟨e⟩ := d.fixedComponent_C27_star_alternatingSeven u h
  have input := d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
    d.point_mem_U_commutator_K
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  obtain ⟨f,hf,hfe⟩ := ChapterC.C27Source.alternating_star_embedding input
    (by decide : 5 ≤ 7) (by decide : 7 ≠ 6) e
  let A := starImage Lu (d.fixedCore u) Lu
  let M := starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)
  let R := starImage Lu (d.fixedCore u) (d.fixedCore u)
  let Q := R.map f
  let N := M.map f
  have hR : IsPGroup 2 (d.fixedCore u) := by
    have hh := input.setup.radical.isPGroup.map (d.fixedCentralizer u).subtype
    rwa [map_subgroupOf_eq_of_le input.setup.radical_le] at hh
  have hQ : IsPGroup 2 Q := (hR.comap_subtype.map
    (QuotientGroup.mk' (starKernel Lu (d.fixedCore u)))).map f
  have hQne : Q ≠ ⊥ := by
    intro he
    exact ChapterC.C27Source.star_radical_ne_bot input
      ((R.map_eq_bot_iff_of_injective hf).mp he)
  have hN : N ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨m,hm,rfl⟩
    rw [show f m = (e ⟨m,starM_le _ _ _ hm⟩ : Equiv.Perm (Fin 7)) from
      hfe ⟨m,starM_le _ _ _ hm⟩]
    exact (e ⟨m,starM_le _ _ _ hm⟩).property
  have hMR : M ≤ normalizer (R : Set (StarQuotient Lu (d.fixedCore u))) :=
    d.fixedStarM_le_starRadicalNormalizer u h
  have hNQ : N ≤ normalizer (Q : Set _) :=
    (map_mono hMR).trans (R.le_normalizer_map f)
  have h5 : 5 ∣ Nat.card N := by
    rw [card_map_of_injective hf]
    exact (d.fixedStarM_hasA5TwoResidual_of_source u h).five_dvd_card
  obtain ⟨hcard,t,ht,hQt⟩ :=
    Theory.SpecificGroups.Alternating.SevenFiveRadical.generated_by_swap Q N hQ hQne hN hNQ h5
  have htQ : t ∈ Q := by
    rw [hQt]
    exact subset_closure (Set.mem_singleton t)
  obtain ⟨r,hr,hfr⟩ := htQ
  have hRcard : Nat.card R = 2 := by
    rw [←card_map_of_injective (K := R) hf]
    exact hcard
  have hRgen : R = closure {r} := by
    apply map_injective hf
    change Q = (closure {r}).map f
    rw [MonoidHom.map_closure,Set.image_singleton,hfr]
    exact hQt
  have hcentralizer : M = A ⊓ centralizer (R : Set (StarQuotient Lu (d.fixedCore u))) := by
    apply le_antisymm
    · exact le_inf (starM_le _ _ _) (hMR.trans (normalizer_le_centralizer_of_card_two R hRcard))
    · exact (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)).trans
        (ChapterC.C27Source.star_radical_normalizer_control input)
  refine ⟨⟨e,r,t,?_,hRgen,ht,?_,hcentralizer⟩⟩
  · rw [←orderOf_injective f hf r,hfr]
    exact ht.orderOf
  · intro k k'
    constructor
    · intro hh
      have he := congrArg f hh
      rw [map_mul,map_mul,map_inv,hfe k',hfe k,hfr] at he
      exact he
    · intro hh
      apply hf
      rw [map_mul,map_mul,map_inv,hfe k',hfe k,hfr]
      exact hh
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
