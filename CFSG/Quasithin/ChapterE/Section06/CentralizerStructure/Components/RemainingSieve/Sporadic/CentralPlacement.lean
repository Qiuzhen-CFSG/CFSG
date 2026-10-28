module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.SourceAction
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.RelativeCoordinates
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport

/-!
# E.6.7 placement through central component coordinates

For an invariant characteristic-two local in the original component quotient,
relative component-orbit coordinates send each two-perfect subnormal block
into a finite power of that local with central kernel. An intrinsic obstruction
to chi-zero blocks in those coordinates therefore places the full local lift
in M by the genuine E.6.7 decomposition. The native M₂₄ octad and sextet
calculations discharge this obstruction in the adjacent source consumer.
The whole component two-kernel, original Q and relative subnormality remain.

Source: Aschbacher–Smith E.6.7–8, printed pp.246–248.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
universe u v
variable {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

omit [Finite A] in
theorem seedLift_le_M_of_central_coordinates
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (e : (L ⧸ pCore 2 L) ≃* A) (hZ : center A = ⊥) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (P : Subgroup A)
    (hinv : ∀ a : MulAut A, ((S : Subgroup L).map (modelMap e)).map a.toMonoidHom =
      (S : Subgroup L).map (modelMap e) → P.map a.toMonoidHom = P)
    (hP : HasCharacteristicTwo P)
    (hobs : ∀ {B : Type u} [Group B], ChapterC.IsChiZeroBlock B →
      ∀ {n : ℕ} (q : B →* (Fin n → P)), q.ker ≤ center B →
        q.range.IsSubnormal → False) : seedLift e P ≤ M := by
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQ : Q ≤ centralizer (U : Set G) := inf_le_right.trans (centralizer_le hU.1)
  have htwo : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have hn := seedLift_stable e S hS P hinv
  have hp := seedLift_characteristicTwo e P hP
  have hjoin : HasCharacteristicTwo (seedLift e P ⊔ Q : Subgroup G) := by
    apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
    exact hL.2.relative_local_adjoin_centralizer hL.1 (seedLift_le e P) hQ htwo hn
      ((inf_centralizer_pCoreIn_le_iff 2 _).mpr hp)
  let f := seedProjection e P
  have hf : Function.Surjective f := seedProjection_surjective e P
  have hfc : f.ker ≤ center (seedLift e P) := by
    exact seedProjection_ker_central hL e P
  have hfz (x : seedLift e P) (hx : inclusion (seedLift_le e P) x ∈ center L) : f x = 1 := by
    exact seedProjection_kills_center e hZ P x hx
  obtain ⟨d⟩ := h67 U hU _ le_sup_right
    (sup_le ((seedLift_le e P).trans hL.1) hQ) hjoin
  apply le_sup_left.trans (OtherTypes.le_of_blockDecomposition d ?_)
  intro D hD hs hb
  let C := D.subgroupOf (seedLift e P ⊔ Q)
  let c := subgroupOfEquivOfLe hD
  have hb' := hb.of_mulEquiv c.symm
  have hj : C.subtype.range.IsSubnormal := by rwa [C.range_subtype]
  obtain ⟨n, q, hqc, hqs⟩ := hL.2.relative_subnormal_central_coordinates hL.1
    (seedLift_le e P) hQ htwo hn f hf hfc hfz hb'.chi.short.twoPerfect
    C.subtype C.subtype_injective hj
  exact hobs hb' q hqc hqs
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
