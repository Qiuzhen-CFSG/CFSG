module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryResidualRoot
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeFullSpan

/-!
# A proper unitary core product and the marked quotient omega

For an incident edge with a larger unitary quotient, the image of the
neighboring two-core is preserved by the full Sylow normalizer. The
unitary root calculation puts that image in the omega-center or makes it
the whole Sylow. The latter alternative says that the two original vertex
cores generate the full edge two-core. Thus a proper core product gives
the required omega placement for the entire neighboring core, and in
particular for the literal radius-three intersection.

Relative normality and actual local transitivity carry a single marked
commutator bound to the whole neighboring span. `UnitaryCoreDistance`
uses these results with the proved 8.3 bound and closes the residual-section
contradiction for this case and every terminal model.

Source: DGS, *Groups and Graphs* (1985), 8.3--8.4(3), pp.135--138;
the unitary normalizer dichotomy is the full-torus root calculation in
`UnitaryResidualRoot`. No claim of involution generation of an intersection
is needed.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A proper adjacent-core product in a large unitary local quotient puts
the entire opposite core over the marked Sylow omega-center. -/
theorem source_unitary_neighbor_core_le_omega
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (R : Sylow 2 (d.localGroup v))
    (hR : (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (d.localGroup v ⧸ pCore 2 (d.localGroup v)) 3 (2^n) ∨
      IsSU (d.localGroup v ⧸ pCore 2 (d.localGroup v)) 3 (2^n))
    (hproper : ¬ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 ≤
      Q (family P) v ⊔ Q (family P) w) :
    Q (family P) w ≤ quotientSylowOmegaPreimage (d.localGroup v) R := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 L)
  let S := R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let A := (Q F w).subgroupOf L
  have hQR : Q F w ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hvw.symm
  have hQL : Q F w ≤ L := hQR.trans (map_subtype_le _)
  have hAR : A ≤ R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hQR hx
    exact (Subtype.ext he : y=x) ▸ hy
  have hNA : normalizer (R : Set L) ≤ normalizer (A : Set L) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    have hgw : (g : G) ∈ stabilizer F w := by
      have hg' : g ∈ (stabilizer F w).subgroupOf L :=
        (source_edge_local_normalizer h d hvw M R hR).2.symm ▸ hg
      exact hg'
    exact le_normalizer_iff.mp (stabilizer_normalizes_Q F w) g hgw x hx
  have hNq : normalizer (S : Set (L ⧸ pCore 2 L)) ≤
      normalizer (A.map q : Set (L ⧸ pCore 2 L)) := by
    change normalizer ((R : Subgroup L).map q : Set (L ⧸ pCore 2 L)) ≤ _
    rw [←R.normalizer_map_surjective q (QuotientGroup.mk'_surjective _)]
    exact (map_mono hNA).trans (A.le_normalizer_map q)
  have hAO : A.map q ≤ omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L)) := by
    rcases unitary_sylow_invariant_dichotomy hn hu S (A.map q) (map_mono hAR) hNq with ho | he
    · exact ho
    · exfalso
      apply hproper
      rw [←hR]
      rintro _ ⟨r,hr,rfl⟩
      have hqr : q r ∈ A.map q := he ▸ mem_map_of_mem q hr
      obtain ⟨x,hx,hxr⟩ := hqr
      have hk : x⁻¹*r ∈ pCore 2 L := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q (x⁻¹*r) = 1
        rw [map_mul,map_inv,hxr,inv_mul_cancel]
      have hkQ : (x : G)⁻¹*(r : G) ∈ Q F v := by
        rw [←localGroup_core_eq F d v]
        exact mem_map_of_mem L.subtype hk
      have hh := (Q F v ⊔ Q F w).mul_mem
        ((show Q F w ≤ Q F v ⊔ Q F w from le_sup_right) hx)
        ((show Q F v ≤ Q F v ⊔ Q F w from le_sup_left) hkQ)
      simpa only [subtype_apply,mul_inv_cancel_left] using hh
  intro x hx
  exact ⟨⟨x,hQL hx⟩,hAO (mem_map_of_mem q hx),rfl⟩

/-- One marked omega bound controls the full radius-one span when the
entire terminal core has the marked omega placement. -/
theorem source_core_full_span_bound
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a' : Vertex (family P)} (hb : 1 < b (family P))
    (w : (graph (family P)).neighborSet a')
    (R : Sylow 2 (d.localGroup w.val))
    (hQ : Q (family P) a' ≤ quotientSylowOmegaPreimage (d.localGroup w.val) R)
    (H : Subgroup G) (hn : d.localGroup a' ≤ normalizer (H : Set G))
    (hbound : ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤ H) :
    ⁅Q (family P) a',V (family P) a' 1⁆ ≤ H := by
  let := finite_endpoints h
  let F := family P
  have hVL : V F a' 1 ≤ d.localGroup a' :=
    (V_le_Q_of_dist_add_lt_b F h.generate (fun v => (source_Z_Q_U h v).1)
      a' a' 1 (by simpa using hb) (d.kernel_sylow a')).trans
        ((pCoreIn_le_sylow (stabilizer F a') default).trans (d.sylow_le a' default))
  have hall (v : (graph F).neighborSet a') : ⁅Q F a',Z F v.val⁆ ≤ H := by
    obtain ⟨g,hg,hgv⟩ := d.transitive a' w v
    have hga : g • a' = a' := d.local_le a' hg
    have hc := map_mono (f := (MulAut.conj g).toMonoidHom)
      ((commutator_mono hQ le_rfl).trans hbound)
    have hH : H.map (MulAut.conj g).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (hn hg)
    rwa [map_commutator,←Q_translate,hga,←Z_translate,hgv,hH] at hc
  have hZ : ⁅Z F a',Q F a'⁆ ≤ H := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr (Z_centralizes_Q F a' (source_Z_Q_U h a').1)]
    exact bot_le
  rw [V_one_eq_sup_neighbors,commutator_comm]
  apply commutator_sup_le_of_relative_normal (d.localGroup a') _ _ (Q F a') H hn
    ((Z_le_V F a' 1).trans hVL)
    (iSup_le fun v => (Z_neighbor_le_V F v.property).trans hVL) hZ
  exact commutator_iSup_le_of_relative_normal (d.localGroup a') (Q F a') H _ hn
    (fun v => (Z_neighbor_le_V F v.property).trans hVL)
    (fun v => by rw [commutator_comm]; exact hall v)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
