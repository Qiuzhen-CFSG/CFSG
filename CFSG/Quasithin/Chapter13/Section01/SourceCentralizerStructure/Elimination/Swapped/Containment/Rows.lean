module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Containment.Inner
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.RowParameters

/-!
# The complete exchanged-orbit containment and Sylow sieve

The actual quotient of the exchanged orbit is a product of two copies of the
component quotient. The canonical radical and T_u generate a solvable group,
so their images supply the solvable product used by the four-model sieve.
This gives the field congruences and the Janko prime restriction. Together
with the proved orbit containment and exchanged complement factors, these
are all clauses of SwappedData, with no additional geometric input.

Source: Aschbacher--Smith, 13.1.12(3), printed p.874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding Chapter1.XiEmbedding.SwappedSylow
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {p : ℕ} [Fact p.Prime] {u : G}

theorem Context.swapped_row (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L)) :
    SwappedRow p (XiQuotient K) := by
  let V := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let D := componentOrbit K V
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  let R := P₀.subgroupOf D
  let q := QuotientGroup.mk' (pCore 2 D)
  have hcontained := h.swapped_containment o s e hr
  have hPD : P₀ ≤ D := (map_subtype_le _).trans hcontained
  have hshape := h.swapped_complement_shape P
  have hi : Function.Injective (q.subgroupMap R) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hc : (a : D) ∈ pCore 2 D :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val ha)
    exact Subtype.ext ((pCore_isPGroup.disjoint_of_coprime hshape.isPGroup.comap_subtype
      (Nat.coprime_two_left.mpr h.odd)).le_bot ⟨hc,a.property⟩)
  let er : P₀ ≃* R.map q := (subgroupOfEquivOfLe hPD).symm.trans
    (MulEquiv.ofBijective (q.subgroupMap R) ⟨hi,q.subgroupMap_surjective R⟩)
  have hR : XiOddQuotient p (R.map q) := hshape.of_mulEquiv er
  obtain ⟨S,hS⟩ := h.swapped_orbit_sylow s e
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 D))
  have hSbar : (Sbar : Subgroup (XiQuotient D)) = (V.subgroupOf D).map q := by
    rw [Sylow.coe_mapSurjective]
    congr 1
    have hs := congrArg (fun B => B.subgroupOf D) hS
    change ((S : Subgroup D).map D.subtype).comap D.subtype = _ at hs
    rw [comap_map_eq_self_of_injective D.subtype_injective] at hs
    change (S : Subgroup D) = (V ⊓ D).subgroupOf D at hs
    simpa only [inf_subgroupOf_right] using hs
  let J := XiP p L ⊔ V
  let B := R ⊔ V.subgroupOf D
  let := h.point_radical_join_solvable (u := u)
  have hBJ : B ≤ J.subgroupOf D := sup_le
    (fun x hx => (show P₀ ≤ J from (map_subtype_le _).trans le_sup_left) hx)
    (fun x hx => (show V ≤ J from le_sup_right) hx)
  let f : B →* J := (D.subtype.subgroupComap J).comp (inclusion hBJ)
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := f) (by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : J => (x : G)) he)
  have hsol : Group.IsSolvable (R.map q ⊔ (Sbar : Subgroup (XiQuotient D)) : Subgroup _) := by
    rw [hSbar,← Subgroup.map_sup]
    exact Group.isSolvable_of_surjective (q.subgroupMap_surjective B)
  let := hsol
  obtain ⟨product⟩ := h.swapped_quotient_product o s e hr
  let U := Sbar.mapSurjective (f := product.toMonoidHom) product.surjective
  let A := (R.map q).map product.toMonoidHom
  let : Group.IsSolvable (A ⊔ (U : Subgroup (XiQuotient K × XiQuotient K)) : Subgroup _) := by
    change Group.IsSolvable (((R.map q).map product.toMonoidHom) ⊔
      (Sbar : Subgroup (XiQuotient D)).map product.toMonoidHom : Subgroup _)
    rw [← Subgroup.map_sup]
    exact Group.isSolvable_of_surjective (product.toMonoidHom.subgroupMap_surjective _)
  have hA : IsPGroup p A := hR.isPGroup.map _
  have hne : A ≠ ⊥ := by
    intro hb
    have hz : R.map q = ⊥ := map_injective product.injective (hb.trans (Subgroup.map_bot _).symm)
    apply hR.not_isCyclic
    rw [hz]
    infer_instance
  have hH := h.hypothesis.simpleQTKE.involution_centralizer_sqtk (h.involution s.mem s.ne_one)
  cases h.reducible_component_model o s e hH hr with
  | linear_even n hn iso =>
    exact SwappedRow.linear_even n hn
      (binary_model_prod_restrictions hn iso h.odd U A hA hne).2 iso
  | linear_prime r hprime ho iso => exact SwappedRow.linear_prime r hprime ho iso
  | suzuki m hm iso =>
    exact SwappedRow.suzuki m hm (suzuki_prod_congruence hm iso.some h.odd U A hA hne) iso
  | janko iso =>
    have hp : 3 < p := (XiP_oddQuotient_of_A36
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      h.maximal.1.1
      (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2)
      h.nonquasisimple h.odd h.divides).1
    exact SwappedRow.janko (janko_prod_prime hp iso.some U A hA hne) iso

/-- The full exchanged-orbit sieve, for the actual ambient image of every
Sylow p-subgroup of the canonical radical. -/
theorem Context.swapped_data (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L)) :
    SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) :=
  h.swapped_data_of_row o s e hr P (h.swapped_row o s e hr P)

/-- Original 13.1.12(3): orbit containment, the elementary plane, the exchanged
Sylow factors, the literal product equality, and the restricted source row. -/
theorem Context.exists_swapped_data (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    ∃ P : Sylow p (XiP p L),
      SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) := by
  let P : Sylow p (XiP p L) := Classical.choice inferInstance
  exact ⟨P,h.swapped_data o s e hr P⟩

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
