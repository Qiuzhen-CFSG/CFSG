module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryCensus.Source

/-!
# The literal single-alternating-five census consumer

Construct the original refinement setup from the distinguished involution,
its secondary centralizer and the marked ordinary component. The equality
M_u=T_u supplies the two-group intersection. The finite Sylow, rank and
residual-module geometry is retained for its independent source producers.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open Stellmacher
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
variable (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
variable (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
variable (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
variable (hsingle : d.L0 = d.block)
variable (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
variable (u : G) (hu2 : orderOf u = 2)
variable (huR : u ∈ (center (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))).map
  (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subtype)
variable (hout : ¬ d.H ⊓ centralizer ({u} : Set G) ≤ M)
variable (hMu : M ⊓ centralizer ({u} : Set G) = (T : Subgroup G) ⊓ centralizer ({u} : Set G))
variable (hi : ((T : Subgroup G) ⊓ centralizer ({u} : Set G)).relIndex (T : Subgroup G) = 2)
variable (P : Sylow 2 (centralizer ({u} : Set G)))
variable (hP : (P : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype =
  (T : Subgroup G) ⊓ centralizer ({u} : Set G))
variable (z : G) (hz : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype)
variable (hz2 : orderOf z = 2)


include hG hM hTM hu hST hsingle hA hu2 huR hout hMu hi hP hz hz2 in
/-- The literal single-alternating source consumer: construct the original
refinement setup and apply the complete three-row screen to its component. -/
theorem MinimalBlockSetup.single_alternating_secondary_three_rows_of_marks
    (K : Subgroup (centralizer ({u}:Set G)))
    (hK : IsComponent (centralizer ({u}:Set G)) K)
    (hcard : Nat.card P ≤ 128)
    (hrank : primeRank 2 (centralizer ({u}:Set G)) ≤ 4)
    (ho : pPrimeCore 2 (centralizer ({u}:Set G))=⊥)
    (L R : Subgroup (centralizer ({u}:Set G))) (hL : IsPPerfect 2 L)
    (eA : L ≃* alternatingGroup (Fin 4))
    (a : L) (ha : a ∈ pCore 2 L) (hza : z=(a:G)*u)
    (hEP : (pCore 2 L).map L.subtype ≤ (P : Subgroup (centralizer ({u}:Set G))))
    (hRL : R ≤ normalizer (L : Set (centralizer ({u}:Set G))))
    (hri : R.relIndex (P : Subgroup (centralizer ({u}:Set G))) ≤ 2)
    (x : centralizer ({u}:Set G)) (hx : x ∈ P)
    (hnc : ¬ ((pCore 2 L).map L.subtype).map (MulAut.conj x).toMonoidHom ≤
      centralizer (((pCore 2 L).map L.subtype : Subgroup (centralizer ({u}:Set G))) : Set (centralizer ({u}:Set G)))) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) ∨
      Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 17)) := by
  let c := d.single_alternating_secondary_refinement_setup_of_marks hG T hM hTM hu hST
    hsingle hA u hu2 huR hout hMu hi P hP z hz hz2 K hK
  have htwo : IsPGroup 2 (centralizer ({u}:Set G) ⊓ M : Subgroup G) := by
    rw [inf_comm,hMu,←hP]
    exact P.isPGroup'.map (centralizer ({u}:Set G)).subtype
  exact SmallBlocks.AlternatingSecondaryCensus.secondary_component_three_rows hG u hu2 P M z K c
    hK hcard hrank htwo ho L R hL eA a ha hza hEP hRL hri x hx hnc

end CFSG.Quasithin.Chapter2
