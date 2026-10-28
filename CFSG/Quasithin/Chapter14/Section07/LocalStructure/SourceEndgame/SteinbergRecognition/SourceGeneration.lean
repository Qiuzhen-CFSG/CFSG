module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration.Algebra
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SpecialGroup

/-!
# The generation and fixed-kernel branch of genuine 14.7.72

For one genuine critical choice, the original module action gives
[U,Q]=VU₀. The two spans in 14.7.13 then identify Φ(S)=S'=R≤Z(S).
Irreducibility on U/(VU₀) and the 14.7.71 centralizer step give
[R,L₁]=V; normal generation gives [R,L]≤V. The existing centralization
and rank-two exclusion now give U₀=V₁ and R=V.

`Earlier` lists the precise remaining earlier-source premises, without any
14.7.72 generation assertion. The same critical path is used throughout.
The full 14.7.72 assembly, including construction of these earlier inputs,
Steinberg recognition and S=O₂(L), remains with qt-14-07-endgame-steinberg.
The actual centralizer inference of 14.7.71 is imported as a proved theorem,
not assumed. The final consumer combines this branch with the original
Steinberg coordinates to identify the center and supply the Ru1 constructor.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.13, 14.7.65–72, printed pp.1046,1070–1076.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Earlier local setup, the original 14.7.65 module calculation and
66–70 for ONE critical path. The interval irreducibility is that of the
original natural section U/(VU₀), used explicitly in the source proof.
`point_commutator` is proved in the opening paragraph of 14.7.70.
The 14.7.13 fields retain their own original commutator spans. -/
structure Earlier (c : CriticalPath (L := L) F) : Prop where
  critical : ChiefFactors.Earlier d c
  thirteen : EarlierThirteen c
  upper_mark : ((F.Ri L 1).subgroupOf F.H).map d.qH =
    (Matrix.SpecialLinearGroup.upperUnipotent SL2FourNatural.F).map
      (alternatingActor d.naturalQuotient)
  upper_fixed : SL2CentralExtension.upperFixed
    ((d.descendedAction critical.sectionCentralizer).comp
      (alternatingActor d.naturalQuotient)) = d.conjugationSection.imageSpace (V ⊔ d.U₀)
  point_commutator : F.Vi 1 ≤ ⁅F.U, c.Uα⁆
  irreducible : SectionIrreducible d
  span_le_Q : S F L ≤ Q T L
  fixed_bound : Nat.card d.U₀ ≤ 4
  sylow_normalizes : (T : Subgroup G) ≤ normalizer (L : Set G)
  seed_fixed : V ⊓ centralizer (F.Li L 1 : Set G) = F.Vi 1
  centralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
    d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H

/-- The generation conclusions, on the published original S and R.
The center equality is supplied separately after Steinberg recognition;
central containment here suffices for that independent branch. -/
structure Conclusion : Prop where
  original_commutator : ⁅F.U, Q T L⁆ = V ⊔ d.U₀
  span_central : R d ≤ (center (S F L)).map (S F L).subtype
  span_intersection : R d ⊓ F.U = V ⊔ d.U₀
  residual_commutator : ⁅R d, F.Li L 1⁆ = V
  actor_commutator : ⁅R d, L⁆ ≤ V
  span_join : R d = V ⊔ d.U₀
  fixed_kernel : d.U₀ = F.Vi 1
  fixed_span : R d = V
  seed_central : V ≤ (center (S F L)).map (S F L).subtype
  frattini_eq : (frattini (S F L)).map (S F L).subtype = V
  derived_eq : ⁅S F L, S F L⁆ = V
  core_commutator : ⁅S F L, Q T L⁆ = V
  seed_central_in_Q : V ≤ (center (Q T L)).map (Q T L).subtype

/-- Complete the conditional generation branch. Every generation,
centralization, intersection and collapse premise is discharged here from
the earlier-source fields, through the original action and quotient maps. -/
theorem generation (c : CriticalPath (L := L) F) (e : Earlier d c) : Conclusion d := by
  have hE := commutator_U_Q d c e.critical.images e.critical.sectionCentralizer
    e.upper_mark e.upper_fixed e.span_le_Q e.critical.conjugate e.point_commutator
  have hc := central_and_derived d c e.critical e.thirteen hE e.point_commutator
  have hi := fixed_span_intersection d hc.1 hc.2.2 e.irreducible
  have hL₁ := fixed_span_commutator_point d c e.critical e.span_le_Q hc.1 hi
  have hL := fixed_span_commutator_L d hL₁
  have hj := R_eq_join_of_commutator_le d hL
  have hp := fixed_kernel_and_span d e.critical.separation hL e.fixed_bound
    (U_le_S.trans e.span_le_Q) e.sylow_normalizes ChiefFactors.L₁_le_K
    e.seed_fixed e.centralizer68
  exact {
    original_commutator := hE
    span_central := hc.1
    span_intersection := hi
    residual_commutator := hL₁
    actor_commutator := hL
    span_join := hj
    fixed_kernel := hp.1
    fixed_span := hp.2
    seed_central := hp.2.symm.le.trans hc.1
    frattini_eq := hc.2.1.trans hp.2
    derived_eq := hc.2.2.trans hp.2
    core_commutator := (commutator_S_Q d e.span_le_Q hE).trans hp.2
    seed_central_in_Q := hp.2.symm.le.trans
      (R_le_center_Q d hj e.fixed_bound (U_le_S.trans e.span_le_Q)) }

/-- Actual recognition consumer: the original Steinberg coordinates turn
central containment into equality, giving all three special-group layers. -/
theorem special_equalities (c : CriticalPath (L := L) F) (e : Earlier d c)
    (s : SteinbergCoordinates d) :
    (center (S F L)).map (S F L).subtype = V ∧
      (frattini (S F L)).map (S F L).subtype = V ∧ ⁅S F L, S F L⁆ = V := by
  have h := generation d c e
  exact ⟨center_eq_of_steinberg d s h.seed_central h.derived_eq, h.frattini_eq, h.derived_eq⟩

/-- Application to the published Ru1 constructor. The independent source
recognition/core branch and later 14.7.74 supply the displayed three inputs;
all generation and fixed-kernel inputs are discharged by `generation`. -/
theorem ruOne (c : CriticalPath (L := L) F) (e : Earlier d c)
    (s : SteinbergCoordinates d) (hcore : S F L = L.pCoreIn 2)
    (hTL : (T : Subgroup G) ≤ L) : Nonempty (ChapterJ.RuOne L V) := by
  have h := generation d c e
  exact ruOne_of_recognized_source d e.critical.separation hTL hcore
    h.seed_central h.frattini_eq h.derived_eq s

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration
