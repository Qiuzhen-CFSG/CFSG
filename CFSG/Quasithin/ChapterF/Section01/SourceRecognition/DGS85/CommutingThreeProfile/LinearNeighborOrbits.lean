module
public import Theory.GroupAction.MatchedPointOrbit
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear.MatrixBorel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.ComplementSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration

/-!
# The linear neighbor orbit and the first complement in DGS 12.3(a)

The original linear quotient marking identifies the actual starred
Sylow normalizer with a projective-point stabilizer. Unipotents act
transitively away from that point, so the Sylow acts transitively on the
other graph neighbors. Its image lies in the normal Sylow of the full
edge. Conjugating by a starred actor gives the assertion for any incident
edge, with the actual embedded core and original graph action.

Apply this orbit theorem to construct the full-edge odd complement fixing
a second neighbor. It normalizes the literal V_x intersect Q_y, both in
the reduced completion and after the original completion inclusion. This
discharges the first orbit premise of ComplementSelection. The later
opposite-core orbit, complement quotient image, first intersection index,
and the rest of 12.3--12.9 and 13.1 remain separate proof obligations.

The intentional implementation import of CoreGeneration reuses its
private base-neighbor/Sylow-normalizer identification inside this same
Chapter 12 family, without widening the existing public interface.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
12.1(e) and the first complement choice in 12.3(a), printed pp.178--179;
Aschbacher--Smith F.1.9 for the literal original starred quotient.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
open BenderSuzuki.Converse
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
variable {k : Type*} [Field k] [CharP k 2]

private theorem unip_transitive (a b : P1 k) (ha : a ≠ pInf k) (hb : b ≠ pInf k) :
    ∃ u ∈ Unip k, u • a = b := by
  have hzero : pInf k ≠ pZero k := by
    intro he
    apply weyl_notMem_Borel (F := k)
    change weyl k • pInf k = pInf k
    exact weyl_smul_pInf.trans he.symm
  have hreach (c : P1 k) (hc : c ≠ pInf k) : ∃ u ∈ Unip k, u • pZero k = c := by
    obtain ⟨g, hgi, hgc⟩ := MulAction.is_two_pretransitive_iff.mp
      (inferInstance : MulAction.IsMultiplyPretransitive (SL2 k) (P1 k) 2)
      hzero hc.symm
    have hg : g ∈ (Unip k : Set (SL2 k)) * (Torus k : Set (SL2 k)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        (Torus_le_Borel.trans (CFSG.Quasithin.ChapterF.Source.Linear.unip_normalizer.ge)),
        Unip_sup_Torus]
      exact hgi
    obtain ⟨u, hu, t, ht, rfl⟩ := hg
    refine ⟨u, hu, ?_⟩
    rwa [mul_smul, (show t • pZero k = pZero k from ht.2)] at hgc
  obtain ⟨u, hu, hua⟩ := hreach a ha
  obtain ⟨v, hv, hvb⟩ := hreach b hb
  refine ⟨v * u⁻¹, (Unip k).mul_mem hv ((Unip k).inv_mem hu), ?_⟩
  rw [← hua, mul_smul, inv_smul_smul, hvb]


variable [Finite k]

private theorem sylow_affine_transitive (T : Sylow 2 (SL2 k)) :
    ∃ p : P1 k, normalizer (T : Set (SL2 k)) = MulAction.stabilizer (SL2 k) p ∧
      ∀ a b : P1 k, a ≠ p → b ≠ p → ∃ t ∈ (T : Subgroup (SL2 k)), t • a = b := by
  let P := Matrix.SpecialLinearGroup.upperUnipotentSylow k 2
  have hP : (P : Subgroup (SL2 k)) = Unip k :=
    CFSG.Quasithin.ChapterF.Source.Linear.unip_eq_upper.symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 k) P T
  have hmap : (P : Subgroup (SL2 k)).map (MulAut.conj g).toMonoidHom = T := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g • pInf k, ?_, ?_⟩
  · have he := Subgroup.map_equiv_normalizer_eq (P : Subgroup (SL2 k)) (MulAut.conj g)
    rw [hmap, hP, CFSG.Quasithin.ChapterF.Source.Linear.unip_normalizer] at he
    simp only [Sylow.coe_coe] at he
    rw [← he, Borel, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  · intro a b ha hb
    have ha' : g⁻¹ • a ≠ pInf k := by
      intro he
      exact ha (by rw [← he, smul_inv_smul])
    have hb' : g⁻¹ • b ≠ pInf k := by
      intro he
      exact hb (by rw [← he, smul_inv_smul])
    obtain ⟨u, hu, he⟩ := unip_transitive (g⁻¹ • a) (g⁻¹ • b) ha' hb'
    refine ⟨g * u * g⁻¹, ?_, ?_⟩
    · rw [← hmap]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hP ▸ hu)
    · rw [mul_smul, mul_smul, he, smul_inv_smul]


open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem linear_base_edge_core_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    {y z : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hyx : y ≠ base (reducedFamily L S) (!i))
    (hzx : z ≠ base (reducedFamily L S) (!i)) :
    ∃ t ∈ (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) :
        Subgroup (G₀ L S)).pCoreIn 2, t • y = z := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F (base F (!i)) ⊓ stabilizer F (base F i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (L := L) (S := S) i))
    (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F (base F i) from inf_le_right))
    (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  obtain ⟨T, hT⟩ := base_star_sylow_normalizer h i
  let R : Sylow 2 (SL2 k) := T.mapSurjective (f := f) hf
  have hRT : (R : Subgroup (SL2 k)).comap f = (T : Subgroup A) := by
    apply comap_map_eq_self
    have hk : f.ker = pCore 2 A := by
      ext t
      change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
      rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff t
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  obtain ⟨p, hp, htrans⟩ := sylow_affine_transitive R
  have hstab : (MulAction.stabilizer (SL2 k) p).comap f = MulAction.stabilizer A (base F (!i)) := by
    rw [← hp]
    change (normalizer ((R : Subgroup (SL2 k)) : Set (SL2 k))).comap f = _
    rw [comap_normalizer_eq_of_surjective _ hf, hRT, Sylow.coe_coe, ← hT]
    rfl
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a, ha, hay⟩ := star_locally_transitive h i hadj hy
  obtain ⟨c, hc, hcz⟩ := star_locally_transitive h i hadj hz
  obtain ⟨t, ht, he⟩ := Theory.GroupAction.MatchedPointOrbit.transitive_away_from_base f (T : Subgroup A)
    (base F (!i)) p hstab htrans (⟨a, ha⟩ : A) (⟨c, hc⟩ : A)
    (by simpa only [Subgroup.mk_smul, hay] using hyx)
    (by simpa only [Subgroup.mk_smul, hcz] using hzx)
  have hTE : (T : Subgroup A).map A.subtype ≤ E := by
    rintro u ⟨t, ht, rfl⟩
    refine ⟨?_, star_le_stabilizer i t.property⟩
    have hh := (T : Subgroup A).le_normalizer ht
    rwa [Sylow.coe_coe, ← hT] at hh
  have hcore := pGroup_le_core_of_core_sylow E ((T : Subgroup A).map A.subtype) hTE
    (T.isPGroup'.map _) (source_edge_core_sylow (reduced_triple h)
      (reduced_borel_core_sylow h) hadj.symm)
  refine ⟨t, hcore (mem_map_of_mem A.subtype ht), ?_⟩
  change (t : G₀ L S) • (a • base F (!i)) = c • base F (!i) at he
  rwa [hay, hcz] at he

end ReducedLayer

open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual full-edge two-core is transitive on the other neighbors of
a linear marked endpoint, including the binary field. -/
theorem linear_incident_core_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    {x y z : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hyx : y ≠ x) (hzx : z ≠ x) :
    ∃ t ∈ (stabilizer (reducedFamily L S) x ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) :
        Subgroup (G₀ L S)).pCoreIn 2, t • y = z := by
  let F := reducedFamily L S
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a, ha, hax⟩ := star_locally_transitive h i hadj hx
  have ham : a • base F i = base F i := star_le_stabilizer i ha
  have haim : a⁻¹ • base F i = base F i := (stabilizer F (base F i)).inv_mem ham
  have hback {v : Vertex F} (hv : (graph F).Adj (base F i) v) :
      (graph F).Adj (base F i) (a⁻¹ • v) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F a⁻¹).map_adj_iff.mpr hv
    change (graph F).Adj (a⁻¹ • base F i) (a⁻¹ • v) at hh
    rwa [haim] at hh
  have hne {v : Vertex F} (hv : v ≠ x) : a⁻¹ • v ≠ base F (!i) := by
    intro he
    apply hv
    calc
      v = a • (a⁻¹ • v) := (smul_inv_smul _ _).symm
      _ = x := by rw [he, hax]
  obtain ⟨t, ht, he⟩ := linear_base_edge_core_transitive h i e (hback hy) (hback hz) (hne hyx) (hne hzx)
  let E := stabilizer F (base F (!i)) ⊓ stabilizer F (base F i)
  have hE : E.map (MulAut.conj a).toMonoidHom = stabilizer F x ⊓ stabilizer F (base F i) := by
    rw [map_inf _ _ _ (MulAut.conj a).injective]
    rw [← stabilizer_translate, ← stabilizer_translate, hax, ham]
  have hcore : (E.pCoreIn 2).map (MulAut.conj a).toMonoidHom =
      (stabilizer F x ⊓ stabilizer F (base F i) : Subgroup (G₀ L S)).pCoreIn 2 := by
    rw [← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 (MulAut.conj a).toMonoidHom (MulAut.conj a).injective, hE]
  refine ⟨a * t * a⁻¹, ?_, ?_⟩
  · rw [← hcore]
    exact mem_map_of_mem (MulAut.conj a).toMonoidHom ht
  · rw [mul_smul, mul_smul, he, smul_inv_smul]

/-- The first complement in 12.3(a), with the linear orbit premise discharged. -/
theorem source_linear_edge_complement
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    {x y : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) i))
    (hy : (graph (reducedFamily L S)).Adj y (base (reducedFamily L S) i)) (hyx : y ≠ x) :
    let F := reducedFamily L S
    let E := stabilizer F x ⊓ stabilizer F (base F i)
    ∃ K : Subgroup E,
      (pCore 2 E).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map E.subtype ≤ stabilizer F y ∧
      K.map E.subtype ≤ normalizer (V F x 1 ⊓ Q F y : Set (G₀ L S)) ∧
      (K.map E.subtype).map (G₀ L S).subtype ≤
        normalizer ((V F x 1 ⊓ Q F y).map (G₀ L S).subtype : Set G) := by
  obtain ⟨K, hK, hodd, hfix, hnorm⟩ := source_edge_complement_fixing_neighbor h hx hy hyx
    (fun z hz hzx => linear_incident_core_transitive h i e hx.symm hy.symm hz hyx hzx)
  exact ⟨K, hK, hodd, hfix, hnorm,
    (map_mono (f := (G₀ L S).subtype) hnorm).trans
      ((V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) y).le_normalizer_map (G₀ L S).subtype)⟩

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
