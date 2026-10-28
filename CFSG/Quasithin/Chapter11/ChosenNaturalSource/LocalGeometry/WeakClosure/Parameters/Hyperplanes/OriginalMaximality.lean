module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.ComplementMaximality
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalCubic
public import Theory.GroupTheory.SubgroupCoverTransport

/-!
# Maximality in the original component and the remaining orbit supplement

The maximal stabilizer of the field complement pulls back along the actual
component quotient to N_L(U). The same quotient and original binary
hyperplane are retained throughout. A subgroup whose intersection with the
component is maximal is maximal in LT once it supplements L there. Applying
this observation to N_LT(U) reduces the last E.6.14 premise to preservation
of the L-orbit of U by T.

The orthogonal maximality calculation is proved here; the supplement is
still explicit and is owned by qt-d-1222-natural-weak-parameters. The cubic
actor, fixed intersection and non-two index are supplied by the checked
OriginalCubic consumer. The earlier source premises retain their existing
producers and final discharge by qt-d-1222-natural-weak-closure-source.

Source: Aschbacher--Smith 11.2.2, printed p.767, and E.6.14.
-/

open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.ComplementMaximality
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalMaximality
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

theorem original_component_stabilizer_isCoatom
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hn : S.field.degree = 2)
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2)
    (hint : U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥) :
    IsCoatom ((normalizer (U : Set G)).subgroupOf L) := by
  obtain ⟨f,_,_,Q,_,hQR,him,_,hgreat,_⟩ :=
    OriginalComplement.exists_original_field_complement D S m hUV hU hC hint
  have he : (normalizer (U : Set G)).subgroupOf L =
      (quadraticStabilizer (naturalForm Q hQR)).comap (Coordinates.sp4 m).quotientMap := by
    ext l
    exact (OriginalComplement.original_field_stabilizer_iff D S m f hUV Q him hgreat l).symm.trans
      (stabilizer_iff_naturalForm Q hQR _)
  rw [he]
  exact Subgroup.isCoatom_comap_of_surjective (Coordinates.sp4 m).quotientMap_surjective
    (field_stabilizer_isCoatom (by rw [S.field.card_eq,hn]; norm_num) Q hQR)

theorem escaping_component_stabilizer_isCoatom (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    IsCoatom ((normalizer (U : Set G)).subgroupOf L) := by
  obtain ⟨⟨m⟩,hn,hC,hi,_⟩ := escaping_hyperplane_sp4_four D S c hE hunique hUV hU hescape
  exact original_component_stabilizer_isCoatom D S m hn hUV hU hC hi
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalMaximality

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalMaximality
open Subgroup
open CFSG.Quasithin.ChapterE.Section06
open scoped Pointwise
variable {G : Type*} [Group G]

private theorem maximal_stabilizer_of_component_supplement
    (L K U : Subgroup G) (hLK : L ≤ K) (hKL : K ≤ normalizer (L : Set G))
    (hmax : IsCoatom ((normalizer (U : Set G)).subgroupOf L))
    (hgen : localNormalizer K U ⊔ L = K) : localNormalizer K U ⋖ K := by
  let N := localNormalizer K U
  have hNK : N ≤ K := inf_le_left
  have hNL : N ≤ normalizer (L : Set G) := hNK.trans hKL
  have hproper : N ≠ K := by
    intro he
    apply hmax.ne_top
    apply top_unique
    intro l _
    exact (show l.val ∈ N from he.symm ▸ hLK l.property).2
  apply covBy_iff_lt_and_eq_or_eq.mpr
  refine ⟨lt_of_le_of_ne hNK hproper,?_⟩
  intro X hNX hXK
  have hin : (normalizer (U : Set G)).subgroupOf L ≤ X.subgroupOf L := by
    intro l hl
    exact hNX ⟨hLK l.property,hl⟩
  by_cases he : (normalizer (U : Set G)).subgroupOf L = X.subgroupOf L
  · left
    apply le_antisymm _ hNX
    intro x hx
    have hxgen : x ∈ N ⊔ L := hgen.symm ▸ hXK hx
    rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right N L hNL] at hxgen
    obtain ⟨n,hn,l,hl,hprod⟩ := hxgen
    have hlX : l ∈ X := by
      have hh := X.mul_mem (X.inv_mem (hNX hn)) hx
      rwa [←hprod,inv_mul_cancel_left] at hh
    have hlN : l ∈ normalizer (U : Set G) := by
      exact (show (⟨l,hl⟩ : L) ∈ (normalizer (U : Set G)).subgroupOf L from
        he.symm ▸ hlX)
    rw [←hprod]
    exact N.mul_mem hn ⟨hLK hl,hlN⟩
  · right
    have ht := hmax.2 _ (lt_of_le_of_ne hin he)
    have hLX : L ≤ X := by
      intro l hl
      exact (show (⟨l,hl⟩ : L) ∈ X.subgroupOf L from ht.symm ▸ mem_top _)
    apply le_antisymm hXK
    rw [←hgen]
    exact sup_le hNX hLX
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalMaximality

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalMaximality
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

theorem escaping_hyperplane_maximal_of_supplement (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G))
    (hgen : localNormalizer (L ⊔ (T : Subgroup G)) U ⊔ L = L ⊔ (T : Subgroup G)) :
    localNormalizer (L ⊔ (T : Subgroup G)) U ⋖ L ⊔ (T : Subgroup G) :=
  maximal_stabilizer_of_component_supplement L (L ⊔ (T : Subgroup G)) U le_sup_left
    (sup_le L.le_normalizer D.sylow_normalizes_component)
    (escaping_component_stabilizer_isCoatom D S c hE hunique hUV hU hescape) hgen

/-- E.6.14 now only needs preservation of the component orbit by T.
All orthogonal stabilizer maximality inside the component is proved. -/
theorem centralizer_le_of_stabilizer_supplement (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hgen : localNormalizer (L ⊔ (T : Subgroup G)) U ⊔ L = L ⊔ (T : Subgroup G)) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  exact hescape (OriginalCubic.centralizer_le_of_natural_maximal_stabilizer
    D S c hE hunique hUV hU
    (escaping_hyperplane_maximal_of_supplement D S c hE hunique hUV hU hescape hgen))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalMaximality
