module
public import Theory.SpecificGroups.Suzuki.SylowNeighborOrbits
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearNeighborOrbits
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration

/-!
# Middle-core conjugation in the nonbinary Suzuki branch of DGS 12.3(a)

The earlier common-Sylow identity says that the neighboring core and the
vertex core generate a Sylow in the actual starred endpoint. Under the
original Suzuki quotient marking, the neighboring core therefore maps
onto that quotient Sylow. Its regular root orbit lifts to transitivity on
the remaining graph neighbors, since the full neighbor stabilizer pulls
back from the same Sylow normalizer.

Combine this with the linear full-edge complement construction: conjugate
the chosen odd complement by the middle core to fix any prescribed
remaining neighbor at the Suzuki endpoint. The conjugate fixes the two
original vertices, normalizes V_x intersect Q_y, has the same order, and
retains its conjugation formula under the original completion inclusion.
Both orbit callbacks in ComplementSelection are discharged in this branch.

The common-Sylow identity is the genuine earlier Chapter 8 / 12.1(c)
input, not a new conclusion assumption. The original linear and Suzuki
markings are kept independently; no field-parameter compatibility or
quotient-supplement conclusion is inferred from this construction. Those
and the later index and profile conclusions remain with Chapter 12.
The private base-stabilizer identification is intentionally reused from
CoreGeneration within this same source family.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
12.1(c,e) and the non-dihedral complement conjugation in 12.3(a),
printed pp.178--179. This module treats Suzuki parameter n > 0.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The earlier common-Sylow identity makes the opposite vertex core
transitive on the remaining neighbors at the marked Suzuki vertex. -/
theorem suzuki_neighbor_core_transitive
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hcommon : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {y z : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hyx : y ≠ base (reducedFamily L S) (!i))
    (hzx : z ≠ base (reducedFamily L S) (!i)) :
    ∃ t ∈ Q (reducedFamily L S) (base (reducedFamily L S) (!i)), t • y = z := by
  let F := reducedFamily L S
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (L := L) (S := S) i))
    (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext t
    change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff t
  let R : Sylow 2 (SuzukiMatrixGroup n) := T.mapSurjective (f := f) hf
  have hRT : (R : Subgroup (SuzukiMatrixGroup n)).comap f = (T : Subgroup A) := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  let D := (Q F (base F (!i))).subgroupOf A
  have hDA : Q F (base F (!i)) ≤ A :=
    (le_sup_left.trans hcommon.ge).trans (map_subtype_le _)
  have hTsup : (T : Subgroup A) = D ⊔ pCore 2 A := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hDA]
    change _ = _ ⊔ A.pCoreIn 2
    rw [star_core h i]
    exact hcommon
  have hDmap : D.map f = (R : Subgroup (SuzukiMatrixGroup n)) := by
    change D.map f = (T : Subgroup A).map f
    rw [hTsup, Subgroup.map_sup]
    have hh : (pCore 2 A).map f = ⊥ := by
      rw [← hk]
      apply bot_unique
      rintro a ⟨t, ht, rfl⟩
      exact ht
    rw [hh, sup_bot_eq]
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨T₀, hT₀⟩ := base_star_sylow_normalizer h i
  have hTfix : (T : Subgroup A).map A.subtype ≤ stabilizer F (base F (!i)) := by
    rw [hcommon]
    exact sup_le (Q_le_stabilizer F _) (((source_Z_Q_U (reduced_triple h) (base F i)).2.trans
      (ballKernel_one_le_edge F hadj)).trans inf_le_right)
  have heT : T = T₀ := sylow_le_normalizer_eq T₀ T (by
    rw [← hT₀]
    exact fun t ht => hTfix (mem_map_of_mem A.subtype ht))
  obtain ⟨p, hp, htrans⟩ := suzuki_sylow_remaining_orbit hn R
  have hstab : (MulAction.stabilizer (SuzukiMatrixGroup n) p).comap f =
      MulAction.stabilizer A (base F (!i)) := by
    rw [← hp]
    change (normalizer ((R : Subgroup (SuzukiMatrixGroup n)) : Set (SuzukiMatrixGroup n))).comap f = _
    rw [comap_normalizer_eq_of_surjective _ hf, hRT, Sylow.coe_coe, heT, ← hT₀]
    rfl
  obtain ⟨a, ha, hay⟩ := star_locally_transitive h i hadj hy
  obtain ⟨c, hc, hcz⟩ := star_locally_transitive h i hadj hz
  obtain ⟨t, ht, he⟩ := Theory.GroupAction.MatchedPointOrbit.transitive_away_from_base f D
    (base F (!i)) p hstab (by rw [hDmap]; exact htrans) (⟨a, ha⟩ : A) (⟨c, hc⟩ : A)
    (by simpa only [Subgroup.mk_smul, hay] using hyx)
    (by simpa only [Subgroup.mk_smul, hcz] using hzx)
  refine ⟨t, ht, ?_⟩
  change (t : G₀ L S) • (a • base F (!i)) = c • base F (!i) at he
  rwa [hay, hcz] at he

end ReducedLayer

open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Construct both complements used in the nonbinary Suzuki branch of
12.3(a), discharging both orbit premises and retaining the original maps. -/
theorem source_linear_suzuki_complements
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hcommon : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {x z : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hxne : base (reducedFamily L S) i ≠ x)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hzne : z ≠ base (reducedFamily L S) (!i)) :
    let F := reducedFamily L S
    let E := stabilizer F x ⊓ stabilizer F (base F (!i))
    let W := V F x 1 ⊓ Q F (base F i)
    ∃ K : Subgroup E,
      (pCore 2 E).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map E.subtype ≤ stabilizer F (base F i) ∧
      ∃ q ∈ Q F (base F (!i)),
        (K.map E.subtype).map (MulAut.conj q).toMonoidHom ≤
          stabilizer F x ⊓ stabilizer F (base F i) ⊓ stabilizer F z ∧
        (K.map E.subtype).map (MulAut.conj q).toMonoidHom ≤ normalizer (W : Set (G₀ L S)) ∧
        Nat.card ((K.map E.subtype).map (MulAut.conj q).toMonoidHom) = Nat.card K ∧
        ((K.map E.subtype).map (MulAut.conj q).toMonoidHom).map (G₀ L S).subtype =
          ((K.map E.subtype).map (G₀ L S).subtype).map (MulAut.conj (q : G)).toMonoidHom := by
  let F := reducedFamily L S
  let E := stabilizer F x ⊓ stabilizer F (base F (!i))
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨K, hK, hodd, hKy, _, _⟩ := source_linear_edge_complement h (!i) eLin hx hadj hxne
  have hcard : Nat.card (K.map E.subtype) = Nat.card K :=
    (Nat.card_congr (K.equivMapOfInjective E.subtype E.subtype_injective).toEquiv).symm
  obtain ⟨q, hq, hfix, hnorm, hc, hmap⟩ := source_middle_core_conjugate_complement h hx hadj hz hzne
    (K.map E.subtype) ((map_subtype_le K).trans inf_le_left)
    ((map_subtype_le K).trans inf_le_right) hKy (hcard.symm ▸ hodd)
    (fun w hw hwm => suzuki_neighbor_core_transitive h i hn eSuz T hcommon hz hw hzne hwm)
  exact ⟨K, hK, hodd, hKy, q, hq, hfix, hnorm, hc.trans hcard, hmap⟩

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
