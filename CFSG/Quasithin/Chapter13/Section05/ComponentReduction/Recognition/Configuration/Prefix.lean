module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.SimpleImage
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.SourceDefs

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}

/-- The proved prefix: the literal simple socle, Sylow subgroups, condition (i),
and the nontrivial Y-inclusions in condition (ii). -/
structure Prefix (s : Selected D K) (h : D.Hypothesis)
    [(componentCentralizer s h).Normal] (Y : Subgroup G) : Prop where
  tx_sylow_normalizer : Chapter1.IsSylowIn 2 (TX D K) (D.H ⊓ normalizer (K : Set G))
  tx_sylow_X : Chapter1.IsSylowIn 2 (TX D K) (X D K)
  khat_simple : IsSimpleGroup (Khat s h)
  khat_fitting : generalizedFitting (Xhat s h) = Khat s h
  marked_sylow : ∃ S : Sylow 2 (Xhat s h), (S : Subgroup (Xhat s h)) = That s h
  actor_card : Nat.card (Vhat s h) = 2
  actor_le_sylow : Vhat s h ≤ That s h
  actor_central : Vhat s h ≤ centralizer (That s h : Set (Xhat s h))
  Y_ne_bot : markedImage s h Y ≠ ⊥
  Y_le_local : markedImage s h Y ≤ L1hat s h

/-- Apply the earlier 13.5.19 conclusions to the original selected component.
No parity, normalization, Sylow, simple-image or Fitting equality is assumed. -/
theorem source_prefix (s : Selected D K) (h : D.Hypothesis)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (Y : Subgroup G) (hYL : Y ≤ D.L₁)
    (himage : starImage D.H (D.H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage D.H Y : Set (Hstar D.H)))
    (hcore : D.V ≤ (D.H ⊓ normalizer (Y : Set G)).pCoreIn 2) :
    letI := componentCentralizer_normal s h (selected_star_local_normalization s h hG hH)
    Prefix s h Y := by
  let hn := selected_star_local_normalization s h hG hH
  let := componentCentralizer_normal s h hn
  have hv := (selected_actor_normalization s h hindex hU).1
  have ht := TX_sylow_X s h hG hH
  have hc := Vhat_central s h hv hindex hU
  have hy := Yhat_ne_bot s h Y hYL himage hcore
  exact ⟨TX_sylow_normalizer s h hG hH, ht,
    Khat_simple s h, Khat_generalizedFitting s h hn,
    marked_TX_sylow s h ht, Vhat_card_two s h hv hindex hU, hc.1, hc.2, hy.1, hy.2⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
end
