module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusSectionGeneration

/-!
# Fixed-space generation at the terminal edge

Transport the natural seed and its edge-Sylow commutator along an actual
oriented edge. The transported seed generates the terminal radius-one
span, and is fixed modulo its center. Hence corrected (5.12) applies to
the same V_t/Z_t section and the literal L_t/Q_t quotient action, with
fixed-space generation proved rather than assumed.

Source: DGS, *Groups and Graphs* (1985), (7.5), pp.130--131, and the
published fixed-space-generation correction to (5.12).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem graph_epsilonTwo_radius_section_generated_of_type
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v u y t : Vertex (family P)} (hvu : (graph (family P)).Adj v u)
    (hyt : (graph (family P)).Adj y t) (htype : v.type = y.type)
    (c₀ : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) u))
    (c₁ : LocalRankOneData (stabilizer (family P) u)
      (stabilizer (family P) u ⊓ stabilizer (family P) v))
    (c : LocalRankOneData (stabilizer (family P) t)
      (stabilizer (family P) t ⊓ stabilizer (family P) y))
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer (family P) v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer (family P) u))
    (hdich : Stellmacher.IsSylowSubgroupIn (Q (family P) u)
      (c₁.Pstar ⊓ centralizer (Z (family P) u : Set G)) ∨
      Z (family P) u = Stellmacher.omegaOneCenterAmbient c₁.Pstar)
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat : HasNaturalCenter c₀.Pstar (Z (family P) v) (Q (family P) v))
    [((Q (family P) t).subgroupOf c.Pstar).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (c.Pstar ⧸ (Q (family P) t).subgroupOf c.Pstar) W)
    (s : BinaryConjugationSection c.Pstar (V (family P) t 1) (Z (family P) t)
      (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar)))) :
    GeneratedByFixedSpace σ
      ((((stabilizer (family P) t ⊓ stabilizer (family P) y).pCoreIn 2).subgroupOf c.Pstar).map
        (QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar))) := by
  let := finite_endpoints h
  have hcenter := graph_epsilonTwo_center_trivial_of_localData h hB hvu c₀ c₁ ho₀ ho₁ hdich hepsilon
  have hcomm := graph_natural_edge_commutator h hB hvu c₀ ho₀ hcenter hnat
    ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2) le_rfl
    (local_edgeCore_not_le_vertexCore c₀ ho₀ (source_edge_core_sylow h hB hvu))
  rw [←hepsilon] at hcomm
  have hZZ : Z (family P) u ≤ Z (family P) v :=
    hepsilon.le.trans (graph_edgeSeed_le_Z h hB hvu c₀ ho₀)
  obtain ⟨g,hgv⟩ := (same_orbit_iff (family P) v y).mpr htype
  have hgu : (graph (family P)).Adj y (g • u) := by
    have he := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hvu
    change (graph (family P)).Adj (g • v) (g • u) at he
    rwa [hgv] at he
  obtain ⟨r,hr,hrt⟩ := locally_transitive (family P) hgu hyt
  let f := r*g
  have hfv : f • v = y := by rw [show f = r*g from rfl,mul_smul,hgv]; exact hr
  have hfu : f • u = t := by rw [show f = r*g from rfl,mul_smul]; exact hrt
  have hZZ' : Z (family P) t ≤ Z (family P) y := by
    have he := map_mono (f := (MulAut.conj f).toMonoidHom) hZZ
    rwa [←Z_translate,←Z_translate,hfv,hfu] at he
  have hcomm' : ⁅(stabilizer (family P) t ⊓ stabilizer (family P) y).pCoreIn 2,
      Z (family P) y⁆ ≤ Z (family P) t := by
    have he := congrArg (Subgroup.map (MulAut.conj f).toMonoidHom) hcomm
    rw [map_commutator,←Z_translate,←Z_translate,
      ←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj f).injective,
      map_inf _ _ _ (MulAut.conj f).injective,
      ←stabilizer_translate,←stabilizer_translate,hfv,hfu] at he
    simpa only [commutator_comm,inf_comm] using he.le
  exact section_generated_by_fixed_seed c.Pstar (V (family P) t 1) (Z (family P) t)
    (Z (family P) y) _ σ _ s (graph_radius_one_eq_center_span h hyt c hZZ') hcomm'

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
