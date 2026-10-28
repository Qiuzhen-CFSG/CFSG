module
public import Theory.GroupTheory.CoprimeComplementRestriction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionIndexSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration

/-!
# The complement supplement in the marked linear quotient

The starred endpoint is normal in its full vertex stabilizer. Restrict an
odd full-edge complement to this endpoint using coprime factorization;
the restricted subgroup supplements the starred Sylow in its normalizer.
Projecting through the literal original/starred quotient marking preserves
that supplement. Every two-subgroup in this normalizer lies in the Sylow,
so the intersection-image containment is discharged as well.

The source application now obtains the second linear index and field
coordinates from an actual full-edge complement fixing x. It no longer
assumes a quotient-image supplement or a selected quotient Sylow. Earlier
containment in the starred endpoint and nonzero movement remain explicit.

Source: DGS85, Groups and Graphs, (12.3)(a), printed p.179. The private
base normalizer calculation is reused from CoreGeneration in this family.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem star_normalized_by_vertex (h : HypothesisF11 L S) (i : Bool) :
    stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ≤
      normalizer (star L S i : Set (G₀ L S)) := by
  intro t ht
  apply le_normalizer_comap (G₀ L S).subtype
  apply (normal_subgroupOf_iff_le_normalizer (starredParabolic_le _)).mp
    (h.starredParabolic_normal (if i then 1 else 0))
  apply P₀_le h (if i then 1 else 0)
  rw [stabilizer, Subgroup.CosetGeometry.stabilizer_base] at ht
  cases i <;> exact ht

private theorem star_neighbor_normalizer (h : HypothesisF11 L S) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y) :
    ∃ T : Sylow 2 (star L S i), (stabilizer (reducedFamily L S) y).subgroupOf
      (star L S i) = normalizer (T : Set (star L S i)) := by
  let F := reducedFamily L S
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (L := L) (S := S) i))
    (inclusion_injective _)
  obtain ⟨T₀, hT₀⟩ := base_star_sylow_normalizer h i
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a, ha, hay⟩ := star_locally_transitive h i hadj hy
  let aA : A := ⟨a, ha⟩
  let T := T₀.mapSurjective (f := (MulAut.conj aA).toMonoidHom) (MulAut.conj aA).surjective
  refine ⟨T, ?_⟩
  have he : (stabilizer F y).subgroupOf A =
      ((stabilizer F (base F (!i))).subgroupOf A).map (MulAut.conj aA).toMonoidHom := by
    change MulAction.stabilizer A y = (MulAction.stabilizer A (base F (!i))).map _
    have hayA : aA • base F (!i) = y := hay
    rw [← hayA]
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj aA _
  rw [he, hT₀]
  exact map_equiv_normalizer_eq (T₀ : Subgroup A) (MulAut.conj aA)

/-- The full-edge complement restricts to a supplement in the original/starred quotient. -/
theorem source_quotient_edge_complement_supplement
    {M : Type*} [Group M]
    (h : HypothesisF11 L S) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* M)
    (K : Subgroup (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) :
      Subgroup (G₀ L S))).IsComplement' K)
    (hodd : Odd (Nat.card K)) :
    let F := reducedFamily L S
    let A := star L S i
    let E := stabilizer F y ⊓ stabilizer F (base F i)
    let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 A))
    ∃ T : Sylow 2 M,
      (normalizer (T : Set M)).comap q = (stabilizer F y).subgroupOf A ∧
      (T : Subgroup M) ⊔ ((K.map E.subtype).subgroupOf A).map q =
        normalizer (T : Set M) := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F y ⊓ stabilizer F (base F i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (L := L) (S := S) i))
    (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F y from inf_le_left))
    (inclusion_injective _)
  let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    ext a
    change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) a)) = 1 ↔ a ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff a
  obtain ⟨R, hR⟩ := star_neighbor_normalizer h i hy
  have hER : E.subgroupOf A = normalizer (R : Set A) := by
    rw [← hR]
    ext a
    exact and_iff_left (star_le_stabilizer i a.property)
  have hcop : Nat.Coprime (Nat.card (pCore 2 E)) (Nat.card K) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := E)).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr hodd).pow_left n
  have hsup := sylow_normalizer_sup_restricted_complement 2 A E
    (inf_le_right.trans (star_normalized_by_vertex h i)) R hER (pCore 2 E) K
    pCore_isPGroup hK hcop
  let T : Sylow 2 M := R.mapSurjective (f := q) hq
  have hRT : (T : Subgroup M).comap q = (R : Subgroup A) := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal R
  have hn : (normalizer (T : Set M)).comap q = normalizer (R : Set A) := by
    rw [← Sylow.coe_coe, comap_normalizer_eq_of_surjective _ hq, hRT, Sylow.coe_coe]
  refine ⟨T, hn.trans hR.symm, ?_⟩
  have hm := congrArg (Subgroup.map q) hsup
  rw [Subgroup.map_sup, ← hn, map_comap_eq_self_of_surjective hq _] at hm
  exact hm

/-- The full-edge complement restricts to a supplement in the original/starred quotient. -/
theorem source_marked_edge_complement_supplement
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (K : Subgroup (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) :
      Subgroup (G₀ L S))).IsComplement' K)
    (hodd : Odd (Nat.card K)) :
    let F := reducedFamily L S
    let A := star L S i
    let E := stabilizer F y ⊓ stabilizer F (base F i)
    let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 A))
    ∃ T : Sylow 2 SL(2,k),
      (normalizer (T : Set SL(2,k))).comap q = (stabilizer F y).subgroupOf A ∧
      (T : Subgroup SL(2,k)) ⊔ ((K.map E.subtype).subgroupOf A).map q =
        normalizer (T : Set SL(2,k)) := by
  exact source_quotient_edge_complement_supplement h i hy e K hK hodd

/-- The actual full-edge complement forces the linear index and marked field coordinates. -/
theorem source_linear_index_of_edge_complement
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    {x y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (hW : V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) y ≤ star L S i)
    (hmove : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) y,
      Z (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≠ ⊥)
    (K : Subgroup (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) :
      Subgroup (G₀ L S))).IsComplement' K)
    (hodd : Odd (Nat.card K))
    (hKx : K.map (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤
        stabilizer (reducedFamily L S) x) :
    let F := reducedFamily L S
    let W := V F x 1 ⊓ Q F y
    (Q F (base F i)).relIndex W = Nat.card k ∧
      ((parabolic L S (if i then 1 else 0)).pCoreIn 2).relIndex
        (W.map (G₀ L S).subtype) = Nat.card k ∧
      ∃ T : Sylow 2 SL(2,k), ∃ f : W →* Multiplicative k, Function.Surjective f ∧
        f.ker = (Q F (base F i)).subgroupOf W ∧
        ∀ w, ((Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T) (f w) : SL(2,k)) =
          e ((originalQuotient h i).symm
            (QuotientGroup.mk' (pCore 2 (star L S i)) ⟨w, hW w.property⟩)) := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F y ⊓ stabilizer F (base F i)
  let W := V F x 1 ⊓ Q F y
  let C := (K.map E.subtype).subgroupOf A
  let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  obtain ⟨T, hn, hsup⟩ := source_marked_edge_complement_supplement h i hy e K hK hodd
  have hPN : (W.subgroupOf A).map q ≤ normalizer (T : Set SL(2,k)) := by
    apply map_le_iff_le_comap.mpr
    rw [hn]
    intro a ha
    exact Q_le_stabilizer F y ha.2
  have hp : IsPGroup 2 ((W.subgroupOf A).map q) :=
    ((isPGroup_pCoreIn 2 (stabilizer F y)).to_inf_right.comap_subtype).map q
  have hPT : (W.subgroupOf A).map q ≤ T := by
    rw [← inf_eq_left.mpr hPN, hp.inf_normalizer_sylow T]
    exact inf_le_right
  have hC : C.map A.subtype ≤ K.map E.subtype := by
    rintro a ⟨c, hc, rfl⟩
    exact hc
  obtain ⟨hi, ho, f, hf, hk, hm⟩ := source_linear_intersection_index h i e hW hmove T C hPT
    (hC.trans hKx) (hC.trans ((map_subtype_le K).trans inf_le_left)) hsup
  exact ⟨hi, ho, T, f, hf, hk, hm⟩

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
