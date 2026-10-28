module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SylowCenters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.MovingActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs

/-!
# Displacement of the Chapter 8 actor in the actual edge

An elementary subgroup of one endpoint core lies in every edge Sylow.
Inside the other local group its quotient image lies in a Sylow omega-center,
so its commutator with the edge Sylow lies in the original neighboring core.
The equality O₂(L)=Q is proved through the actual inclusion into the full
stabilizer. No faithfulness hypothesis on a representation is needed.

The moving actor is elementary by the minimal critical distance. Applying
the displacement result to the existing local-generation argument proves
relative normality of H, containment in every neighboring center, and the
transferred 6.5 centralizer obstruction. `LocalGeneration` discharges the
generation premise, and `ReducedNormality` gives the literal reduced-source
application. Later distance, field and natural-module conclusions are separate.

Source: DGS, *Groups and Graphs* (1985), 5.9(b), 8.1(g,i), pp.110,133.
The supplied actual rank-one models are precisely the earlier 6.1 input.
-/

@[expose] public noncomputable section
open Subgroup Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- An elementary subgroup of the first core is central modulo the second
core under every Sylow of their literal full edge stabilizer. -/
theorem source_elementary_edge_displacement
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup w ⧸ pCore 2 (d.localGroup w)))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAQ : A ≤ Q (family P) v)
    (T : Sylow 2 ↥(stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G)) :
    ⁅(T : Subgroup ↥(stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G)).map
      (stabilizer (family P) v ⊓ stabilizer (family P) w).subtype, A⁆ ≤ Q (family P) w := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup w
  let E := stabilizer F v ⊓ stabilizer F w
  let T₀ := (T : Subgroup E).map E.subtype
  have hp : IsPGroup 2 T₀ := T.isPGroup'.map _
  have hTL : T₀ ≤ L := pGroup_le_localGroup F d w T₀ hp ((map_subtype_le _).trans inf_le_right)
  have hAT : A ≤ T₀ := hAQ.trans (Q_le_edge_sylow F (fun x => (source_Z_Q_U h x).2) hvw T)
  let : Finite L := Finite.of_injective (inclusion (d.local_le w)) (inclusion_injective _)
  obtain ⟨R, hR⟩ := (hp.comap_subtype (K := L)).exists_le_sylow
  have hTR : T₀ ≤ (R : Subgroup L).map L.subtype := by
    intro t ht
    exact ⟨⟨t, hTL ht⟩, hR ht, rfl⟩
  let q := QuotientGroup.mk' (pCore 2 L)
  have hk : q.ker.map L.subtype = Q F w := by
    rw [QuotientGroup.ker_mk']
    exact localGroup_core_eq F d w
  have hh := elementary_actor_displacement_le_kernel L q (QuotientGroup.mk'_surjective _)
    M R A (hAT.trans hTL) (hAT.trans hTR)
  exact (commutator_mono hTR le_rfl).trans (hk ▸ hh)

/-- The literal actor of 8.0 satisfies the displacement used in 8.1(i).
Only the actual earlier 6.1 rank-one quotient marking is supplied. -/
theorem source_moving_actor_displacement
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (M : IsRankOneModel (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)))
    (T : Sylow 2 ↥(stabilizer (family P) a' ⊓ stabilizer (family P) w.val : Subgroup G)) :
    ⁅(T : Subgroup ↥(stabilizer (family P) a' ⊓ stabilizer (family P) w.val : Subgroup G)).map
      (stabilizer (family P) a' ⊓ stabilizer (family P) w.val).subtype,
      V (family P) beta 1 ⊓ Q (family P) a'⁆ ≤ Q (family P) w.val := by
  obtain ⟨_, hb3, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 (V (family P) beta 1) :=
    CommutingThreeProfile.V_elementary (family P) h.generate
      (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) beta
  let : IsElementaryAbelian 2 ↥(V (family P) beta 1 ⊓ Q (family P) a' : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  exact source_elementary_edge_displacement h d w.property M _ inf_le_right T

/-- After proving local generation, the source displacement is no additional
premise: the exact rank-one models give normality of H and its containment
in every neighboring center, as used in 8.2--8.7. -/
theorem source_critical_normality_of_generation
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ w : (graph (family P)).neighborSet a',
      IsRankOneModel (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)))
    (hgen : ∀ w : (graph (family P)).neighborSet a',
      ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥ →
      ∃ T : Sylow 2 ↥(stabilizer (family P) a' ⊓ stabilizer (family P) w.val : Subgroup G),
        V (family P) beta 1 ⊔
          (T : Subgroup ↥(stabilizer (family P) a' ⊓ stabilizer (family P) w.val : Subgroup G)).map
            (stabilizer (family P) a' ⊓ stabilizer (family P) w.val).subtype = d.localGroup a') :
    let H := ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆
    (H.subgroupOf (d.localGroup a')).Normal ∧
      (∀ w : (graph (family P)).neighborSet a', H ≤ Z (family P) w.val) ∧
      ∀ w : (graph (family P)).neighborSet a',
        ¬ ∃ T : Sylow 2 ↥(d.localGroup a' ⊓ centralizer (H : Set G) : Subgroup G),
          (T : Subgroup ↥(d.localGroup a' ⊓ centralizer (H : Set G) : Subgroup G)).map
            (d.localGroup a' ⊓ centralizer (H : Set G)).subtype = Q (family P) w.val := by
  let := finite_endpoints h
  dsimp only
  obtain ⟨_, hb3, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
  have hQL := pGroup_le_localGroup (family P) d a' (Q (family P) a')
    (isPGroup_pCoreIn 2 _) (Q_le_stabilizer _ _)
  obtain ⟨hn, hcens, _, hobs⟩ := radius_one_commutator_normality (family P) h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2)
    d.kernel_sylow beta a' hd.le hb3 (d.localGroup a') hQL (d.transitive a') (by
      intro w hw
      obtain ⟨T, hT⟩ := hgen w hw
      exact ⟨T, hT, source_moving_actor_displacement h d hc hab hd hb hcomm w (models w) T⟩)
  refine ⟨hn, hcens, fun w => hobs w ?_ (d.core_span_obstruction a' w.val w.property)⟩
  exact pGroup_le_localGroup (family P) d a' _ (isPGroup_pCoreIn 2 _)
    (((source_Z_Q_U h w.val).2).trans
      ((ballKernel_one_le_edge (family P) w.property.symm).trans inf_le_right))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
