module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MarkedComplementIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.FullEdgeComplements
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearIntersectionTransitivity
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearIntersectionIndex
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearIntersectionTransitivity

/-!
# The full edge complement forces a linear root orbit

Let D lie in the incoming core at a linear vertex, escape that vertex's
core, and be normalized by an odd complement C to the full edge core.
Restrict C to the starred endpoint and use the original quotient marking.
Its image supplements the Sylow in its full normalizer. Since the Sylow
is abelian, the nonzero image of D is normalizer-invariant and hence the
whole linear root group. The already proved common-Sylow orbit then lifts
to D: the remaining vertex-core factor fixes every neighbor.

One edge conjugation carries this argument to any vertex of the same
orbit, including the complement, relative index and literal action.
The source six-path application in SuzukiSixPathRegular derives the
normalization and escape premises for its actual threefold intersection.
The common-Sylow marking remains the earlier source input; no local
transitivity or full quotient-image hypothesis is assumed here.
Implementation imports reuse the existing private root invariance and
core-product arguments without changing their public boundaries.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.3)(a) and the complement-action step of (12.8), pp.179,185.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- An escaping two-subgroup normalized by the full edge complement acts transitively on all other linear neighbors. -/
theorem linear_complement_invariant_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (D C : Subgroup (G₀ L S))
    (hD : D ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hesc : ¬ D ≤ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hC : C ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S))).IsComplement'
      (C.subgroupOf (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        stabilizer (reducedFamily L S) (base (reducedFamily L S) i))))
    (hodd : Odd (Nat.card C)) (hnorm : C ≤ normalizer (D : Set (G₀ L S))) :
    let F := reducedFamily L S
    (Q F (base F i)).relIndex D = Nat.card k ∧
      ∀ u v, (graph F).Adj (base F i) u → (graph F).Adj (base F i) v →
        u ≠ base F (!i) → v ≠ base F (!i) → ∃ d ∈ D, d • u = v := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F (base F (!i)) ⊓ stabilizer F (base F i)
  let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hDA : D ≤ A := hD.trans ((le_sup_left.trans hT.ge).trans (map_subtype_le _))
  have hk : q.ker = (Q F (base F i)).subgroupOf A := by
    have he : q.ker = pCore 2 A := by
      ext t
      change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
      rw [map_eq_one_iff _ e.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff t
    rw [he,←star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hc : Nat.card (C.subgroupOf E) = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv
  obtain ⟨R,hR,hcover⟩ := source_marked_edge_complement_supplement h i hadj e
    (C.subgroupOf E) hK (hc.symm ▸ hodd)
  rw [map_subgroupOf_eq_of_le hC] at hcover
  have hPN : (D.subgroupOf A).map q ≤ normalizer (R : Set SL(2,k)) := by
    apply map_le_iff_le_comap.mpr
    rw [hR]
    intro a ha
    exact Q_le_stabilizer F _ (hD ha)
  have hp : IsPGroup 2 ((D.subgroupOf A).map q) :=
    (((isPGroup_pCoreIn 2 (stabilizer F (base F (!i)))).to_le hD).comap_subtype).map q
  have hPT : (D.subgroupOf A).map q ≤ R := by
    rw [←inf_eq_left.mpr hPN,hp.inf_normalizer_sylow R]
    exact inf_le_right
  have hn : C.subgroupOf A ≤ normalizer (D.subgroupOf A : Set A) := by
    intro c hc
    exact le_normalizer_comap A.subtype (hnorm hc)
  have hne : (D.subgroupOf A).map q ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff (D.subgroupOf A)).mp he
    rw [hk] at hh
    exact hesc (fun d hd => hh (show (⟨d,hDA hd⟩ : A) ∈ D.subgroupOf A from hd))
  have him := Matrix.SpecialLinearGroup.subgroup_eq_sylow_of_normalizer_invariant R
    ((D.subgroupOf A).map q) hPT hne
    (image_normalized_of_sylow_supplement q R _ (C.subgroupOf A) hPT hn hcover)
  have hi : (Q F (base F i)).relIndex D = Nat.card k := by
    rw [←relIndex_subgroupOf hDA,←hk,relIndex_ker,him]
    exact Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 R).symm.toEquiv
  refine ⟨hi,?_⟩
  intro u v hu hv hun hvn
  obtain ⟨t,ht,he⟩ := linear_common_sylow_transitive h i e T hT hu hv hun hvn
  rw [←linear_full_index_sup_core h i e T hT D hD hi] at ht
  have hnQ : D ≤ normalizer (Q F (base F i) : Set (G₀ L S)) :=
    (hDA.trans (star_le_stabilizer i)).trans ((stabilizer F (base F i)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F (base F i)))))
  have ht' : t ∈ (D : Set (G₀ L S)) * (Q F (base F i) : Set (G₀ L S)) := by
    rw [←coe_mul_of_left_le_normalizer_right D (Q F (base F i)) hnQ]
    exact ht
  obtain ⟨d,hd,r,hr,rfl⟩ := ht'
  refine ⟨d,hd,?_⟩
  have hru : r • u = u :=
    (((source_Z_Q_U (reduced_triple h) (base F i)).2.trans (ballKernel_one_le_edge F hu)).trans inf_le_right) hr
  simpa only [mul_smul,hru] using he

/-- Transfer the complement action and the root orbit through one literal edge conjugation. -/
theorem linear_complement_invariant_transitive_at
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {a x : Vertex (reducedFamily L S)} (ha : a.type = i)
    (hax : (graph (reducedFamily L S)).Adj a x)
    (D C : Subgroup (G₀ L S)) (hD : D ≤ Q (reducedFamily L S) x)
    (hesc : ¬ D ≤ Q (reducedFamily L S) a)
    (hC : C ≤ stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)
    (hK : (pCore 2 (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a :
      Subgroup (G₀ L S))).IsComplement'
        (C.subgroupOf (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)))
    (hodd : Odd (Nat.card C)) (hnorm : C ≤ normalizer (D : Set (G₀ L S))) :
    (Q (reducedFamily L S) a).relIndex D = Nat.card k ∧
      ∀ u v, (graph (reducedFamily L S)).Adj a u → (graph (reducedFamily L S)).Adj a v →
        u ≠ x → v ≠ x → ∃ d ∈ D, d • u = v := by
  let F := reducedFamily L S
  obtain ⟨g,hga,hgx⟩ := incident_common_translate F hax.2
  have hx : x.type = !i := Bool.eq_not_iff.mpr (ha ▸ hax.1.symm)
  rw [ha] at hga
  rw [hx] at hgx
  have hga' : g⁻¹ • a = base F i := by rw [←hga,inv_smul_smul]
  have hgx' : g⁻¹ • x = base F (!i) := by rw [←hgx,inv_smul_smul]
  let c := (MulAut.conj g⁻¹).toMonoidHom
  let D' := D.map c
  let C' := C.map c
  have hD' : D' ≤ Q F (base F (!i)) := by
    have hh := map_mono (f := c) hD
    change D' ≤ (Q F x).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Q_translate F,hgx'] at hh
  have hesc' : ¬ D' ≤ Q F (base F i) := by
    intro hh
    apply hesc
    have hQ : Q F (base F i) = (Q F a).map c := by
      rw [←Q_translate F,hga']
    rw [hQ] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hC' : C' ≤ stabilizer F (base F (!i)) ⊓ stabilizer F (base F i) := by
    rintro t ⟨d,hd,rfl⟩
    have hdx : d • x = x := (hC hd).1
    have hda : d • a = a := (hC hd).2
    constructor
    · change (g⁻¹*d*(g⁻¹)⁻¹) • base F (!i) = base F (!i)
      rw [inv_inv,mul_smul,mul_smul,hgx,hdx,hgx']
    · change (g⁻¹*d*(g⁻¹)⁻¹) • base F i = base F i
      rw [inv_inv,mul_smul,mul_smul,hga,hda,hga']
  have hadj : (graph F).Adj (base F (!i)) (base F i) :=
    ⟨by change (!i) ≠ i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F (!i) i⟩
  have hc : Nat.card C' = Nat.card C := card_map_of_injective (MulAut.conj g⁻¹).injective
  have hK' := source_edge_complement_transfer h hax.symm hadj
    (C.subgroupOf (stabilizer F x ⊓ stabilizer F a)) hK C' hC'
    (hc.symm ▸ hodd) (hc.trans (Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv).symm)
  have hnorm' : C' ≤ normalizer (D' : Set (G₀ L S)) :=
    (map_mono hnorm).trans (D.le_normalizer_map c)
  obtain ⟨hi,ht⟩ := linear_complement_invariant_transitive h i e T hT
    D' C' hD' hesc' hC' hK' (hc.symm ▸ hodd) hnorm'
  refine ⟨?_,?_⟩
  · have hh := relIndex_map_map_of_injective (Q F a) D (f := c) (MulAut.conj g⁻¹).injective
    change ((Q F a).map (MulAut.conj g⁻¹).toMonoidHom).relIndex D' = _ at hh
    rw [←Q_translate F,hga'] at hh
    exact hh.symm.trans hi
  · intro u v hu hv hux hvx
    have hadj' {z : Vertex F} (hz : (graph F).Adj a z) :
        (graph F).Adj (base F i) (g⁻¹ • z) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hz
      change (graph F).Adj (g⁻¹ • a) (g⁻¹ • z) at hh
      rwa [hga'] at hh
    have hne {z : Vertex F} (hz : z ≠ x) : g⁻¹ • z ≠ base F (!i) := by
      rw [←hgx']
      exact fun he => hz ((MulAction.injective g⁻¹) he)
    obtain ⟨t,ht,he⟩ := ht _ _ (hadj' hu) (hadj' hv) (hne hux) (hne hvx)
    obtain ⟨d,hd,rfl⟩ := ht
    refine ⟨d,hd,?_⟩
    apply MulAction.injective g⁻¹
    change (g⁻¹*d*(g⁻¹)⁻¹) • (g⁻¹ • u) = g⁻¹ • v at he
    simpa only [inv_inv,mul_smul,smul_inv_smul] using he

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
