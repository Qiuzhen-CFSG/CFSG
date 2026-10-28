module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryNormalizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryQuotient
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceGeometry
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# The secondary residual and its proper full quotient image

The enlarged two-core O₂(K_Z T) lies in R₂ and therefore normalizes K₂.
Perfectness of K₂ recovers it as O²(K₂ O₂(K_Z T)). Component minimality
then shows K₂ O₂(K_Z) < K_Z. The actual projection K₂ → K_Z/O₂(K_Z)
is proper and has kernel the literal intersection with O₂(K_Z); no
identification of that intersection with O₂(K₂) is made.

The selected source component supplies these statements and all three
local-image geometry premises of the corrected sieve, including nontriviality
of the original radical action, without a SecondarySourceData witness.

This does not prove the separate printed inequality K₂ < O₂(K_Z)K₂.
Proper component containment and residual recovery alone do not imply it:
a proper perfect A₅ in A₆ already has O₂(A₆)=1. That checks only the weaker
inference, not the full original ambient configuration. Strict core enlargement,
actual MS construction, the original A₅ application and the final linear-four
contradiction remain with the nonblock assembly owner.
Source: Aschbacher--Smith, original 4.3.13--15, pp.617--618.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}
namespace RootCoordinates
variable (m : RootCoordinates d)
include m

/-- The actual enlarged core normalizes the original secondary residual. -/
theorem enlarged_core_normalizes_secondary (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (J : Subgroup G) (hJ : secondary c ⊔ S c ≤ J) :
    J.pCoreIn 2 ≤ normalizer (secondary c : Set G) :=
  ((m.enlarged_core_le_radical_source hn D J hJ).trans (R₂ c).le_normalizer).trans
    ((m.radical_normalizer_source hn D).trans inf_le_right)

/-- Recover K₂ as the two-residual after adjoining the actual enlarged core. -/
theorem secondary_enlarged_core_residual (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (J : Subgroup G) (hJ : secondary c ⊔ S c ≤ J) :
    (pResidual 2 (secondary c ⊔ J.pCoreIn 2 : Subgroup G)).map
      (secondary c ⊔ J.pCoreIn 2).subtype = secondary c := by
  let E := secondary c ⊔ J.pCoreIn 2
  let A := (secondary c).subgroupOf E
  let P := (J.pCoreIn 2).subgroupOf E
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (secondary c).le_normalizer (m.enlarged_core_normalizes_secondary hn D J hJ))
  let : Group.IsPerfect (secondary c) := EndgameSieve.secondary_perfect c
  let e := subgroupOfEquivOfLe (show secondary c ≤ E from le_sup_left)
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hs : A ⊔ P = ⊤ := by
    rw [←subgroupOf_sup (show secondary c ≤ E from le_sup_left)
      (show J.pCoreIn 2 ≤ E from le_sup_right),subgroupOf_self]
  rw [(residuals_of_perfect_normal_sup_twoGroup A P
    (isPGroup_pCoreIn 2 J).comap_subtype hs).1,
    map_subgroupOf_eq_of_le (show secondary c ≤ E from le_sup_left)]

/-- A containing normal component remains proper after adjoining its two-core. -/
theorem secondary_sup_component_core_lt (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hgen : L ⊔ secondary c = K c)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype) :
    secondary c ⊔ (B.map (rootNormalizer c).subtype).pCoreIn 2 <
      B.map (rootNormalizer c).subtype := by
  let M := B.map (rootNormalizer c).subtype
  have hN : rootNormalizer c ≤ normalizer (M : Set G) := by
    let := hBn
    have hh := B.le_normalizer_map (rootNormalizer c).subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hcore : M.pCoreIn 2 ≤ normalizer (secondary c : Set G) := by
    apply le_trans (pCoreIn_mono_of_normalizes (show M ≤ M ⊔ (T : Subgroup G) from le_sup_left)
      ((sup_le (map_subtype_le _) (root_normalized c D)).trans hN))
    exact m.enlarged_core_normalizes_secondary hn D (M ⊔ (T : Subgroup G))
      (sup_le (hsec.trans le_sup_left) (inf_le_left.trans le_sup_right))
  have hproper := secondary_lt_component_of_generation D hgen B hBn hsec
  refine lt_of_le_of_ne (sup_le hsec (pCoreIn_le 2 M)) ?_
  intro he
  have hMN : M ≤ normalizer (secondary c : Set G) :=
    he.ge.trans (sup_le (secondary c).le_normalizer hcore)
  let A := (secondary c).subgroupOf (rootNormalizer c)
  have hSN : secondary c ≤ rootNormalizer c := hsec.trans (map_subtype_le _)
  have hAB : A ≤ B := by
    intro x hx
    obtain ⟨b,hb,he⟩ := hsec hx
    exact (Subtype.ext he : b = x) ▸ hb
  have hlt : A < B := by
    refine lt_of_le_of_ne hAB ?_
    intro he
    have hh := congrArg (map (rootNormalizer c).subtype) he
    rw [map_subgroupOf_eq_of_le hSN] at hh
    exact hproper.ne hh
  have hne : A ≠ ⊥ := by
    intro he
    apply secondary_ne_bot_of_generation hgen
    have hh := congrArg (map (rootNormalizer c).subtype) he
    simpa only [A,map_subgroupOf_eq_of_le hSN,Subgroup.map_bot] using hh
  let : Group.IsPerfect (secondary c) := EndgameSieve.secondary_perfect c
  let e := subgroupOfEquivOfLe hSN
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  apply hB.not_le_normalizer_of_perfect_lt hlt hne
  intro b hb
  apply mem_normalizer_iff.mpr
  intro x
  exact mem_normalizer_iff.mp (hMN (mem_map_of_mem _ hb)) (x : G)
end RootCoordinates

namespace RootCoordinates
variable (m : RootCoordinates d)
include m

omit m [Finite G] in
/-- The full projection kernel is the actual core intersection, not all O₂(K₂). -/
theorem secondary_component_projection_kernel
    (B : Subgroup (rootNormalizer c))
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype) :
    (EndgameSieve.SourceImages.secondaryProjection c B hsec).ker =
      ((B.map (rootNormalizer c).subtype).pCoreIn 2).subgroupOf (secondary c) := by
  ext x
  change QuotientGroup.mk' (pCore 2 B)
    (EndgameSieve.SourceImages.secondaryToComponent c B hsec x) = 1 ↔ _
  apply (QuotientGroup.eq_one_iff _).trans
  rw [←map_pCoreIn_of_injective 2 B (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
  change _ ↔ (rootNormalizer c).subtype (B.subtype
    (EndgameSieve.SourceImages.secondaryToComponent c B hsec x)) ∈
      ((pCore 2 B).map B.subtype).map (rootNormalizer c).subtype
  rw [mem_map_iff_mem (rootNormalizer c).subtype_injective,
    mem_map_iff_mem B.subtype_injective]

/-- The original secondary image is proper in the full component quotient. -/
theorem secondary_component_projection_proper (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hgen : L ⊔ secondary c = K c)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype) :
    (EndgameSieve.SourceImages.secondaryProjection c B hsec).range < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  have hsur := MonoidHom.range_eq_top.mp he
  apply (m.secondary_sup_component_core_lt hn D hgen B hB hBn hsec).not_ge
  rintro _ ⟨b,hb,rfl⟩
  let b' : B := ⟨b,hb⟩
  obtain ⟨x,hx⟩ := hsur (QuotientGroup.mk' (pCore 2 B) b')
  let u := EndgameSieve.SourceImages.secondaryToComponent c B hsec x
  have hx' : QuotientGroup.mk' (pCore 2 B) u = QuotientGroup.mk' (pCore 2 B) b' := hx
  have hk : u⁻¹*b' ∈ pCore 2 B := QuotientGroup.eq.mp hx'
  have hk' : ((u⁻¹*b' : B) : rootNormalizer c) ∈ B.pCoreIn 2 :=
    mem_map_of_mem _ hk
  have hk'' := mem_map_of_mem (rootNormalizer c).subtype hk'
  rw [map_pCoreIn_of_injective 2 B (rootNormalizer c).subtype
    (rootNormalizer c).subtype_injective] at hk''
  have hm := mul_mem_sup x.property hk''
  change (x : G) * ((x : G)⁻¹ * (b : G)) ∈
    secondary c ⊔ (B.map (rootNormalizer c).subtype).pCoreIn 2 at hm
  simpa only [mul_inv_cancel_left,Subgroup.subtype_apply] using hm

end RootCoordinates

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree

/-- The selected original component has a proper full secondary projection with
its exact kernel. No SecondarySourceData or strict core enlargement is assumed. -/
theorem MSData.sourceComponent_projection_geometry (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    let B := d.sourceComponent hn D h hL hSL
    let hsec := (d.sourceComponent_spec hn D h hL hSL).2.2.1.le
    let f := EndgameSieve.SourceImages.secondaryProjection c B hsec
    f.range < ⊤ ∧
      f.ker = ((B.map (rootNormalizer c).subtype).pCoreIn 2).subgroupOf (secondary c) ∧
      (pResidual 2 (secondary c ⊔
        (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 : Subgroup G)).map
        (secondary c ⊔ (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2).subtype =
          secondary c := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨hB,hBn,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  refine ⟨m.secondary_component_projection_proper hn D (m.original_sup_secondary hn D hL.ge)
    _ hB hBn hsec.le,RootCoordinates.secondary_component_projection_kernel _ _,?_⟩
  exact m.secondary_enlarged_core_residual hn D _
    (sup_le (hsec.le.trans le_sup_left) (inf_le_left.trans le_sup_right))


/-- The selected component supplies the actual nontrivial radical action and all
three local-image premises of the sieve before a secondary record is assembled. -/
theorem MSData.sourceComponent_local_image (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (Y : Subgroup G) :
    let B := d.sourceComponent hn D h hL hSL
    letI := (d.sourceComponent_spec hn D h hL hSL).2.1
    let a := normalQuotientAction B (pCore 2 B)
    let r := ((R₂ c).subgroupOf (rootNormalizer c)).map a
    let k := ((secondary c).subgroupOf (rootNormalizer c)).map a
    let y := (Y.subgroupOf (rootNormalizer c)).map a
    r ≠ ⊥ ∧ ClassicalGroup.IsPSL (k ⧸ pCore 2 k) 2 (2^n) ∧
      (MulAut.innerSubgroup (B ⧸ pCore 2 B) ⊔ r ⊔ y) ⊓ normalizer (r : Set _) ≤
        normalizer (k : Set _) ∧
      ¬ MulAut.innerSubgroup (B ⧸ pCore 2 B) ≤ normalizer (r : Set _) := by
  let B := d.sourceComponent hn D h hL hSL
  obtain ⟨hB,hBn,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  let : B.Normal := hBn
  let : IsQuasisimple (B ⧸ pCore 2 B) := d.sourceComponent_quasisimple hn D h hL hSL
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  have hbound := m.enlarged_core_le_radical_source hn D
    (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G))
    (sup_le (hsec.le.trans le_sup_left) (inf_le_left.trans le_sup_right))
  have hnorm := m.radical_normalizer_source hn D
  obtain ⟨_,hmodel,_,hrad⟩ := d.secondary_structure_of_marked_parabolic hn D
    hL hSL B hB hBn hsec.le hbound (hnorm.trans inf_le_right)
  exact ⟨hrad,EndgameSieve.SourceImages.local_image_geometry c B hsec.le hB.perfect D
    hmodel Y hbound (radical_le_root_normalizer D) hnorm hrad⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
