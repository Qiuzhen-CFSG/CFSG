module
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimpleRows
public import CFSG.Quasithin.Chapter10.SourceA5PointTriality
public import CFSG.Quasithin.Chapter10.SourceA5PointRudvalis
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerMarkedMathieu

/-!
# Dispatching the actual quasisimple point-component markings

The finite marking interface retains the actual central quotient and local
subgroup images. Linear and M23 rows require only the central-quotient model;
G2, triality, symplectic and M22 retain their proved literal subgroup markings.
The small-core and Rudvalis rows contradict the original moved-module bound.
All remaining rows give the existing common-centralizer or moving-torus
alternative, for the original conjugate moved subgroup.

The final input contract has precisely the actual enlarged-component hypotheses
from the source point inspection. Producing that marked embedding data from
A.3.12/A.3.14 remains an independent source theorem; this module proves its
consumer, not an unmarked catalogue classification.

Source: Aschbacher–Smith 10.2.9, pp.750–751, together with A.3.12/A.3.14.
-/

public section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Sporadic.Mathieu.M22ChapterH
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Theory.SpecificGroups.SymplecticFour
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Actual marked rows, including the impossible small-core and sporadic rows.
Producing this data is the independent source embedding problem. -/
inductive SourceA5PointQuasisimpleMarking (L I : Subgroup G) : Prop
  | smallCore (hsmall : Nat.card (center (pCore 2
      ((L.subgroupOf I).map (QuotientGroup.mk' (center I))))) < 16)
  | rudvalis (S : Sylow 2 I)
      (hlocal : L.subgroupOf I ∈ ChapterA.Section03.localCComponents S)
      (eI : (I ⧸ center I) ≃* Rudvalis.Model)
      (hcore : Nat.card (pCore 2
        ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 2048)
  | linear (eI : (I ⧸ center I) ≃* Matrix.PSL3Four.PSL)
  | mathieu22 (eI : (I ⧸ center I) ≃* M22)
      (hmark : Quintet.naturalActor.map M22Quintet.Q.subtype ≤
        (((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map
          eI.toMonoidHom).map m22ToPairStabilizer)
  | mathieu23 (eI : (I ⧸ center I) ≃* Sporadic.Mathieu.M23)
  | g2 {F : Type v} [Field F] [Finite F] [CharP F 2]
      (hF : Nat.card F = 4) (eI : (I ⧸ center I) ≃* Atlas.G2.Model F)
      (hmark : (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
          Atlas.G2.LieParabolicSetup.local₁ ∨
        (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
          Atlas.G2.LieParabolicSetup.local₂)
  | triality (n : ℕ) (hn : 0 < n) (hq : 2 ^ n = 4)
      (eI : (I ⧸ center I) ≃* Triality.Standard.BinaryCarrier n hn)
      (hmark : (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
          Triality.Standard.Parabolics.localFactor (Triality.Standard.binaryParameters n hn) .arms ∨
        (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
          Triality.Standard.Parabolics.localFactor (Triality.Standard.binaryParameters n hn) .central)
  | symplectic {F : Type v} [Field F] [Finite F] [CharP F 2]
      (hF : Nat.card F = 4) (eI : (I ⧸ center I) ≃* Sp F)
      (hmark : (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) = pointLocal ∨
        (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
          planeLocal)

/-- The marked M22 calculation feeds the original point-centralizer alternative. -/
theorem source_a5_point_m22_marked_alternative
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : G)
    (I : Subgroup G) [Group.IsPerfect I]
    (eI : (I ⧸ center I) ≃* M22)
    (hmark : Quintet.naturalActor.map M22Quintet.Q.subtype ≤
      (((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map
        eI.toMonoidHom).map m22ToPairStabilizer)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G)) : SourceA5PointComponentAlternative D e t I := by
  let := source_original_full_moved_elementary D
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  have hUC : U ≤ centralizer ({v} : Set G) := by
    intro u hu y hy
    have he : y = v := Set.mem_singleton_iff.mp hy
    rw [he]
    exact U.le_centralizer hu v hv
  exact .common (source_a5_m22_marked_component_centralized eI hmark
    (hUC.trans hNI) hcross)

/-- The completed marked rows feed the original source alternative. -/
theorem source_a5_point_alternative_of_quasisimple_marking
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : G)
    (I : Subgroup G) [Group.IsPerfect I] (hLI : L ≤ I)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hmark : SourceA5PointQuasisimpleMarking.{u,v} L I) :
    SourceA5PointComponentAlternative D e t I := by
  cases hmark with
  | smallCore hsmall =>
      have h := source_a5_marked_core_center_card D e hLI (MulEquiv.refl _)
      omega
  | rudvalis S hlocal eI hcore =>
      exact (source_a5_not_rudvalis_containing_quotient D e hLI S hlocal eI hcore).elim
  | linear eI => exact source_a5_point_linear_alternative D e t I hLI eI hv hNI hcross
  | mathieu22 eI hmark =>
      exact source_a5_point_m22_marked_alternative D e t I eI hmark hv hNI hcross
  | mathieu23 eI => exact source_a5_point_m23_alternative D e t I hLI eI hv hNI hcross
  | g2 hF eI hmark => exact source_a5_point_g2_alternative D e t I hLI hF eI hmark hv hNI hcross
  | triality n hn hq eI hmark =>
      exact source_a5_point_triality_alternative D e t I hLI n hn hq eI hmark hv hNI hcross
  | symplectic hF eI hmark =>
      exact source_a5_point_symplectic_alternative D e t I hLI hF eI hmark

/-- The remaining source input supplies marked rows for the actual enlarged
quasisimple component, with precisely the hypotheses of the point inspection. -/
@[expose] def SourceA5PointQuasisimpleMarkingInput
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (v : G) : Prop :=
  ∀ I : Subgroup G, L < I → I ≤ centralizer ({v} : Set G) →
    (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent →
    centralizer ({v} : Set G) ≤ normalizer (I : Set G) →
    ¬ I ≤ D.maximalLocal → componentOrbit L I = I → IsQuasisimple I →
    SourceA5PointQuasisimpleMarking.{u,v} L I

/-- Once the actual source embeddings are produced, every quasisimple case
of the original point-centralizer inspection is discharged. -/
theorem source_a5_point_quasisimple_alternative_of_source_markings
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : G)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hmarks : SourceA5PointQuasisimpleMarkingInput.{u,v} D v)
    (I : Subgroup G) (hLI : L < I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hout : ¬ I ≤ D.maximalLocal) (hgen : componentOrbit L I = I)
    (hquasi : IsQuasisimple I) : SourceA5PointComponentAlternative D e t I := by
  let := hquasi
  exact source_a5_point_alternative_of_quasisimple_marking D e t I hLI.le
    hv hNI hcross (hmarks I hLI hIX hI hNI hout hgen hquasi)

end CFSG.Quasithin.Chapter10
