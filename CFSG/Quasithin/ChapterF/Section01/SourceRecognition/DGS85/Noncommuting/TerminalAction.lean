module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EpsilonTwoCenters
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.ElementaryAbelianAction

/-!
# Constructing the terminal radius section

At the terminal edge in the epsilon-two path, the exact Chapter 7 center
identities give `[V_t,Q_t] = Z_t`. The quotient conjugation action therefore
factors through the original `L_t/Q_t` and realizes the literal section
`V_t/Z_t`. This constructs the action used by corrected (5.12); the rank-one
model selection, faithfulness and residual fixed-space condition remain
separate hypotheses for recognition.

Source: DGS, *Groups and Graphs* (1985), (7.4)(d) and (7.5), pp.128--131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Subgroup.CosetGeometry.RankTwo
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G]

private theorem graph_Z_normalized
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (v : Vertex (family P)) :
    stabilizer (family P) v ≤ normalizer (Z (family P) v : Set G) := by
  let := finite_endpoints h
  exact (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _)

/-- The original vertex core is normal in the chosen local actor. -/
theorem graph_local_core_normal
    {P : Fin 2 → Subgroup G} {E : Subgroup G}
    (t : Vertex (family P))
    (c : LocalRankOneData (stabilizer (family P) t) E) :
    ((Q (family P) t).subgroupOf c.Pstar).Normal := by
  have hcoreEq : (Q (family P) t).subgroupOf c.Pstar = pCore 2 c.Pstar := by
    rw [show Q (family P) t = c.Pstar.pCoreIn 2 from c.same_core.symm]
    exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
  rw [hcoreEq]
  infer_instance

private theorem exists_section_of_commutator_le
    (H A E Q : Subgroup G) (hAH : A ≤ H) (hEA : E ≤ A)
    (hNA : H ≤ normalizer (A : Set G)) (hNE : H ≤ normalizer (E : Set G))
    [IsElementaryAbelian 2 A] [(Q.subgroupOf H).Normal]
    (hcomm : ⁅A,Q⁆ ≤ E) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      ∃ σ : Representation (ZMod 2) (H ⧸ Q.subgroupOf H) W,
        Nonempty (BinaryConjugationSection H A E
          (σ.comp (QuotientGroup.mk' (Q.subgroupOf H)))) := by
  let W := Additive (A ⧸ E.subgroupOf A)
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action H A E hNA hNE inferInstance
  have hkill : Q.subgroupOf H ≤ α.ker :=
    quotient_conjugation_action_kills_commutator_layer H A E Q inferInstance hNA hcomm α hα
  let β := QuotientGroup.lift (Q.subgroupOf H) α hkill
  let : MulDistribMulAction (H ⧸ Q.subgroupOf H) (A ⧸ E.subgroupOf A) :=
    MulDistribMulAction.compHom _ β
  let σ : Representation (ZMod 2) (H ⧸ Q.subgroupOf H) W :=
    Representation.ofElementaryAbelianAction
  let q := QuotientGroup.mk' (E.subgroupOf A)
  let c : A →* Multiplicative W := {
    toFun := fun a => Multiplicative.ofAdd (Additive.ofMul (q a))
    map_one' := q.map_one
    map_mul' := q.map_mul }
  refine ⟨W,inferInstance,inferInstance,σ,⟨{
    section_le := hAH
    kernel_le := hEA
    normalized := hNA
    coordinates := c
    onto := fun w => QuotientGroup.mk'_surjective (E.subgroupOf A) w.toAdd.toMul
    kernel_eq := ?_
    equivariant := ?_ }⟩⟩
  · ext a
    exact QuotientGroup.eq_one_iff a
  · intro h a
    change q _ = α h (q a)
    exact (hα h a).symm

/-- The terminal edge carries an actual module action through the literal
local quotient. The commutator needed to construct the section is supplied by
the proved two-ended identity (7.4)(d), not by a module assumption. -/
theorem graph_epsilonTwo_terminal_section_exists
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u t y : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u) (hwt : (graph (family P)).Adj w t)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hb : 2 < b (family P)) (hty : (graph (family P)).Adj t y) :
    let c := d t y hty
    letI : ((Q (family P) t).subgroupOf c.Pstar).Normal := graph_local_core_normal t c
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      ∃ σ : Representation (ZMod 2)
        ((d t y hty).Pstar ⧸ (Q (family P) t).subgroupOf (d t y hty).Pstar) W,
        Nonempty (BinaryConjugationSection (d t y hty).Pstar
          (V (family P) t 1) (Z (family P) t)
          (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf (d t y hty).Pstar)))) := by
  let c := d t y hty
  have hcenter := graph_epsilonTwo_critical_centers h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hwt hdu hdt hepsilon hnat₀ hnat₁
  let _ : ((Q (family P) t).subgroupOf c.Pstar).Normal := graph_local_core_normal t c
  let := graph_V_elementary_of_twice_radius_lt h hS t (i := 1) (by omega)
  exact exists_section_of_commutator_le c.Pstar (V (family P) t 1) (Z (family P) t)
    (Q (family P) t)
    ((graph_V_le_Q_of_short h hS t (by omega : 1 < b (family P))).trans
      (source_core_le_star c))
    (Z_le_V _ _ _)
    (c.Pstar_le.trans (graph_stabilizer_normalizes_V h t 1))
    (c.Pstar_le.trans (graph_Z_normalized h t)) hcenter.2.2.2.le

/-- The neighboring critical center survives in the terminal section. Otherwise
its short-distance core containment would contradict noncommutation. -/
theorem graph_terminal_section_nontrivial
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    {v w t : Vertex (family P)}
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hwt : (graph (family P)).Adj w t)
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    {H : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W}
    (s : BinaryConjugationSection H (V (family P) t 1) (Z (family P) t) ρ) :
    Nontrivial W := by
  classical
  by_contra hn
  have : Subsingleton W := not_nontrivial_iff_subsingleton.mp hn
  have hVZ : V (family P) t 1 ≤ Z (family P) t := by
    intro z hz
    exact (s.coordinates_eq_one_iff ⟨z,hz⟩).mp (Subsingleton.elim _ _)
  have hwt' : Z (family P) w ≤ V (family P) t 1 :=
    le_iSup_of_le w (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl hwt.symm)) le_rfl)
  have ht : Z (family P) t ≤ Q (family P) v :=
    graph_Z_le_Q_of_short h hS (by rw [SimpleGraph.dist_comm]; omega)
  apply hne
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((hwt'.trans hVZ).trans (ht.trans (graph_Q_centralizes_Z h v)))

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
