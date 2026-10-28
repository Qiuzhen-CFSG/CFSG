module

public import CFSG.Quasithin.ChapterI.Section03.OrdinaryBalance
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.BadCentralizers

/-!
# The Bender ordinary-balance application of S₂ and GLS 5.17

The ordinary orbit theorem supplies exactly OrdinaryBalance13 from the
universal earlier S₂ and two-layer inputs. The existing bad-centralizer
application retains H = C_G(v), the original t = u and component pullback,
and maps its resulting ambient component through the original subtype.
Thus the empty-delta local-control conclusion needs no general B₂ assertion.

Source: Aschbacher--Smith 2.2.2, printed pp.519--520, using I.3.1 and
GLS II 5.17/5.22. The S₂ and 5.17 producers remain explicit obligations;
this module proves their actual Bender application, not those earlier inputs.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.BenderFusion
open Subgroup Theory.GroupTheory
universe u

/-- The adequate ordinary balance projection for any retained K-group class. -/
theorem BadCentralizers.ordinaryBalance13_of_sylowFixer_and_twoLayer
    (C : GroupClass.{u})
    (sourceS2 : ChapterI.OrdinaryBalance.SimpleSylowFixerSolvability.{u})
    (source517 : ChapterI.OrdinaryBalance.TwoLayerCentralizerBalance.{u}) :
    BadCentralizers.OrdinaryBalance13 C := by
  intro H _ _ _ ho t ht D hD
  exact ChapterI.OrdinaryBalance.ordinary_orbit_of_source_inputs sourceS2 source517 ho t ht D hD

/-- Actual Bender consumer: the existing literal centralizer/component maps
are reused, with precisely the two earlier-source balance inputs exposed. -/
theorem source_local_control_with_centralizers_of_s2_layer_balance
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅)
    (source115 : BadCentralizers.ComponentSource115 G)
    (sourceS2 : ChapterI.OrdinaryBalance.SimpleSylowFixerSolvability.{u})
    (source517 : ChapterI.OrdinaryBalance.TwoLayerCentralizerBalance.{u}) :
    ∃ w : LocalControlWitness T M,
      ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M :=
  source_local_control_with_centralizers_of_delta_empty hG T M hM hTM hunique hdelta
    source115 (BadCentralizers.ordinaryBalance13_of_sylowFixer_and_twoLayer
      CFSG.KnownSimple.IsKnownSimple sourceS2 source517)

end CFSG.Quasithin.Chapter2.BenderFusion
