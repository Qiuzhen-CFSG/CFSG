module
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalEmbedding
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerLocalMathieu
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimpleDispatch

/-!
# Producing the M22 marking from original point-local data

The original point Sylow restricts to I and maps through the literal quotient
I/Z(I). The native M22 theorem then constructs an automorphism placing the
actual E16:A5 image in the natural actor. Composing that automorphism with
the supplied central-quotient equivalence produces the marking consumed by
the existing quasisimple dispatcher, and hence the original point alternative.

The elementary core of order sixteen is the actual A.3.14(6) row shape. The
marking and local Sylow membership are proved here from the source point
geometry; the earlier embedding classification still supplies that row shape.

Source: Aschbacher–Smith A.3.14(6) and 10.2.9, printed pp.750–751.
-/

public section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Sporadic.Mathieu.M22ChapterH
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The M22 row obtains its actual marking from the original full point Sylow. -/
theorem source_a5_point_m22_quasisimple_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (eI : I ⧸ center I ≃* M22)
    (hE : IsElementaryAbelian 2 (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))))
    (h16 : Nat.card (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 16) :
    SourceA5PointQuasisimpleMarking.{u,0} L I := by
  obtain ⟨S,_,_,hl,_,_,⟨eB⟩,_⟩ := source_a5_point_center_quotient_local_embedding D e hn hvL hv0 hs hLI hIX hI
  obtain ⟨f,hf⟩ := source_a5_m22_local_image_exists_marking eI
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I))) hl hE h16 eB
  exact .mathieu22 f hf

/-- The same proved placement feeds the original point-component alternative. -/
theorem source_a5_point_m22_local_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (eI : I ⧸ center I ≃* M22)
    (hE : IsElementaryAbelian 2 (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))))
    (h16 : Nat.card (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 16) :
    SourceA5PointComponentAlternative D e t I :=
  source_a5_point_alternative_of_quasisimple_marking D e t I hLI.le hv hNI hcross
    (source_a5_point_m22_quasisimple_marking D e hn (hcross hv) hv0 hs hLI hIX hI eI hE h16)

end CFSG.Quasithin.Chapter10

