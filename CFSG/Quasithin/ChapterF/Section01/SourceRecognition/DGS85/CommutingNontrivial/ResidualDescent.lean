module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualOmegaEquality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommutatorGeometry
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# Descent of the full Chapter 8 residual module

Put E = O²(L_alpha') and D = E Q_lambda. The original Sylow supplements
E, and fixes the neighboring center Z_lambda setwise. Thus Z_lambda
generates V_alpha' already under D. The two-core of D lies in the marked
residual edge intersection, whose quotient image is the omega-center.
Its displacement on Z_lambda lies in C_V_alpha'(E). Normality propagates
this bound over the whole neighboring span.

The original residual coordinates consequently carry an actual action of
D/O₂(D). The action is constructed by quotient descent and agrees with
original conjugation on representatives. `ResidualOmegaApplication`
identifies D with the printed E T₀ and applies this to the full reduced
F1.11 residual quotient. No natural-module alternative is assumed or
excluded here.

Source: DGS, Groups and Graphs (1985), proof of 8.3, p.136.
-/

@[expose] public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G]

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem source_central_residual_join_geometry (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hz : Z (family P) v = omegaCenterIn (d.localGroup v))
    (R : Sylow 2 (d.localGroup w))
    (hR : (R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype =
      (stabilizer (family P) w ⊓ stabilizer (family P) v).pCoreIn 2) :
    let F := family P
    let E := (pResidual 2 (d.localGroup v)).map (d.localGroup v).subtype
    let D := E ⊔ Q F w
    D ≤ d.localGroup v ∧ d.localGroup v ≤ normalizer (D : Set G) ∧
      D.pCoreIn 2 ≤ ((R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype) ⊓ D ∧
      conjugateSpanBy (Z F w) D = V F v 1 := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨S,hS⟩ := source_edge_core_local_sylow h hB d hvw
  let T := (S : Subgroup L).map L.subtype
  have hST : T = (R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype := by
    dsimp only [T]
    rw [hS,hR,inf_comm (stabilizer F v)]
  have hQT : Q F w ≤ T := by
    dsimp only [T]
    rw [hS]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hvw.symm
  have hTL : T ≤ L := map_subtype_le _
  have hQL : Q F w ≤ L := hQT.trans hTL
  have hTw : T ≤ stabilizer F w := by
    dsimp only [T]
    rw [hS]
    exact (pCoreIn_le 2 _).trans inf_le_right
  have hnQ : T ≤ normalizer (Q F w : Set G) := hTw.trans (stabilizer_normalizes_Q F w)
  have hnE : L ≤ normalizer (E : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pResidual 2 L).le_normalizer_map L.subtype
  have hsupp : E ⊔ T = L := by
    have hh := congrArg (map L.subtype) (pResidual_sup_sylow_eq_top S)
    simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] using hh
  have hDL : D ≤ L := sup_le (map_subtype_le _) hQL
  have hnD : L ≤ normalizer (D : Set G) := by
    rw [←hsupp]
    exact sup_le (le_sup_left.trans D.le_normalizer)
      ((le_inf (hTL.trans hnE) hnQ).trans (normalizer_inf_normalizer_le_normalizer_sup E (Q F w)))
  have hKT : D.pCoreIn 2 ≤ T :=
    (pCoreIn_mono_of_normalizes hDL hnD).trans (pCoreIn_le_sylow L S)
  refine ⟨hDL,hnD,le_inf ?_ (pCoreIn_le 2 D),?_⟩
  · exact hST ▸ hKT
  have hspan := CommutingThreeProfile.V_eq_center_sup_neighbor_conjugates F L (d.local_le v) hvw
    (fun z hz => d.transitive v ⟨w,hvw⟩ ⟨z,hz⟩)
  have hzle : Z F v ≤ Z F w := hz.symm ▸ local_omega_le_neighbor_Z h d hvw
  rw [sup_eq_right.mpr (hzle.trans (le_conjugateSpanBy _ _))] at hspan
  have hspanE : conjugateSpanBy (Z F w) L = conjugateSpanBy (Z F w) E := by
    rw [←hsupp]
    exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
      (hTw.trans (stabilizer_normalizes_Z F w)) (hTL.trans hnE)
  change conjugateSpanBy (Z F w) (E ⊔ Q F w) = _
  rw [conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((Q_le_stabilizer F w).trans (stabilizer_normalizes_Z F w)) (hQL.trans hnE),
    ←hspanE,←hspan]

/-- The literal core of O²(L_alpha') Q_lambda acts trivially on the full
residual quotient V_alpha'/C_V_alpha'(O²(L_alpha')). This is the descent
premise following the quotient omega identity in 8.3. -/
theorem source_counterexample_residual_core_displacement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (hescape : ¬ Q (family P) w.val ≤ Q (family P) a')
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆) :
    let F := family P
    let E := (pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype
    ⁅(E ⊔ Q F w.val).pCoreIn 2,V F a' 1⁆ ≤
      V F a' 1 ⊓ centralizer (E : Set G) := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup a'
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w.val
  let C := V F a' 1 ⊓ centralizer (E : Set G)
  have hz := critical_end_center_of_commuting F h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    L (d.sylow_or_center a')
  obtain ⟨hDL,hnD,hK,hspan⟩ := source_central_residual_join_geometry h hB d w.property hz R hR
  have hY := source_counterexample_residual_edge_eq_omega h hB d hc hab hd hb hcomm models w hm hescape R hR hbad
  have hKY : D.pCoreIn 2 ≤ quotientSylowOmegaPreimage (d.localGroup w.val) R := hY ▸ hK
  have hmove := source_omega_displacement_residual_fixed h hB d hc hab hd hb hcomm models w hm hescape R hR
  have hseed : ⁅Z F w.val,D.pCoreIn 2⁆ ≤ C := by
    rw [commutator_comm]
    exact ((commutator_mono hKY le_rfl).trans hmove).trans
      (inf_le_inf_right _ (Z_neighbor_le_V F w.property))
  have hnE : L ≤ normalizer (E : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pResidual 2 L).le_normalizer_map L.subtype
  have hnC : L ≤ normalizer (C : Set G) :=
    (le_inf ((d.local_le a').trans (stabilizer_normalizes_V F a' 1))
      (hnE.trans (normalizer_le_normalizer_centralizer E))).trans inf_normalizer_le_normalizer_inf
  have hZD : Z F w.val ≤ D := by
    intro x hx
    exact (show Q F w.val ≤ D from le_sup_right)
      ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w.val).1 hx)).1
  have hnK : D ≤ normalizer (D.pCoreIn 2 : Set G) :=
    D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
  change ⁅D.pCoreIn 2,V F a' 1⁆ ≤ C
  rw [commutator_comm,←hspan,commutator_conjugateSpanBy_of_normalized_right _ D _ hZD hnK]
  exact conjugateSpanBy_le hseed (hDL.trans hnC)

/-- The full original residual module descends to the printed residual-join
core quotient. The original vector coordinates and conjugation action are
retained; no natural-module conclusion is assumed. -/
theorem source_counterexample_residual_quotient_action (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (hescape : ¬ Q (family P) w.val ≤ Q (family P) a')
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (d.localGroup a') W)
    (c : BinaryConjugationSection (d.localGroup a') (V (family P) a' 1)
      (V (family P) a' 1 ⊓ centralizer
        ((pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype : Set G)) ρ) :
    let L := d.localGroup a'
    let E := (pResidual 2 L).map L.subtype
    let D := E ⊔ Q (family P) w.val
    ∃ (hDL : D ≤ L) (σ : Representation (ZMod 2) (D ⧸ pCore 2 D) W),
      (∀ g : D, σ (QuotientGroup.mk' (pCore 2 D) g) = ρ (inclusion hDL g)) ∧
      ∃ cD : BinaryConjugationSection D (V (family P) a' 1)
        (V (family P) a' 1 ⊓ centralizer (E : Set G))
        (σ.comp (QuotientGroup.mk' (pCore 2 D))), cD.coordinates = c.coordinates := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup a'
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w.val
  have hz := critical_end_center_of_commuting F h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    L (d.sylow_or_center a')
  obtain ⟨hDL,_,_,hspan⟩ := source_central_residual_join_geometry h hB d w.property hz R hR
  have hdisp := source_counterexample_residual_core_displacement h hB d hc hab hd hb hcomm models w hm hescape R hR hbad
  let η : Representation (ZMod 2) D W := ρ.comp (inclusion hDL)
  let q := QuotientGroup.mk' (pCore 2 D)
  have hk : q.ker ≤ η.ker := by
    rw [QuotientGroup.ker_mk']
    intro g hg
    apply LinearMap.ext
    intro v
    obtain ⟨z,hz⟩ := c.onto (Multiplicative.ofAdd v)
    have hv : v ∈ c.imageSpace (V F a' 1) :=
      (c.mem_imageSpace_iff _ _).mpr ⟨z,z.property,congrArg Multiplicative.toAdd hz⟩
    exact c.fixed_on_imageSpace_of_commutator_le (D.pCoreIn 2) (V F a' 1)
      hdisp (inclusion hDL g) (mem_map_of_mem D.subtype hg) v hv
  have hkU : q.ker ≤ η.asGroupHom.ker := fun g hg => Units.ext (hk hg)
  let σ : Representation (ZMod 2) (D ⧸ pCore 2 D) W :=
    (Units.coeHom _).comp (q.liftOfSurjective (QuotientGroup.mk'_surjective _) ⟨η.asGroupHom,hkU⟩)
  have hσ (g : D) : σ (q g) = η g := by
    change Units.coeHom (Module.End (ZMod 2) W)
      ((q.liftOfSurjective (QuotientGroup.mk'_surjective _) ⟨η.asGroupHom,hkU⟩) (q g)) = _
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    exact Representation.asGroupHom_apply _ _
  refine ⟨hDL,σ,hσ,?_,?_⟩
  · refine {
      section_le := ?_
      kernel_le := c.kernel_le
      normalized := hDL.trans c.normalized
      coordinates := c.coordinates
      onto := c.onto
      kernel_eq := c.kernel_eq
      equivariant := ?_ }
    · rw [←hspan]
      apply conjugateSpanBy_le _ D.le_normalizer
      intro x hx
      exact (show Q F w.val ≤ D from le_sup_right)
        ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w.val).1 hx)).1
    · intro g z
      change _ = σ (q g) (c.coordinates z).toAdd
      rw [hσ]
      exact c.equivariant (inclusion hDL g) z
  · rfl

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
