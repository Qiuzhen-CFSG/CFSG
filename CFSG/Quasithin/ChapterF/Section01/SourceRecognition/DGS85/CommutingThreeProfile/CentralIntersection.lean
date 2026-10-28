module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.GeneratedIntersection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommonSylowIndex
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# The central intersection on DGS p.180

Suppose the intersection H = V_x intersect V_y centralizes the middle core.
The conjugated indices from (12.3)(a) show that the actor V_sigma intersect Q_y,
together with Q_m, covers the actual common Sylow at m. The cross-commutator
identity (12.1)(g) then bounds the fixed-subgroup index on H by q. Two generating
conjugate Sylows and the trivial center of the starred middle group bound |H|
by q squared. The earlier natural center has this order and lies in H, so
H = Z_m. The conclusion also preserves the literal original inclusion.

This is the central-case intermediate in the proof of (12.3)(c), not its
exclusion. The common-Sylow markings, the earlier Chapter 8 natural-center
order and commutator bounds, and the conjugated (12.3)(a) data remain explicit.
The middle-core product is a separate Chapter 12 obligation; it is not assumed
or proved here. The original SL2 quotient marking is used to compute the
actual Sylow index, rather than replacing the starred endpoint by a model.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (12.1)(d--g) and (12.3), printed pp.178--180.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

private theorem centralizer_conj_map {A : Type*} [Group A]
    (T : Subgroup A) (g : A) :
    (centralizer (T : Set A)).map (MulAut.conj g).toMonoidHom =
      centralizer (T.map (MulAut.conj g).toMonoidHom : Set A) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro a ha
  refine ⟨(MulAut.conj g).symm a, ?_, (MulAut.conj g).apply_symm_apply a⟩
  intro t ht
  apply (MulAut.conj g).injective
  simpa only [map_mul, MulEquiv.apply_symm_apply] using
    ha ((MulAut.conj g) t) (mem_map_of_mem _ ht)

private theorem centralizer_index_sylow_eq {A : Type*} [Group A] [Finite A]
    (H : Subgroup A) [H.Normal] (T R : Sylow 2 A) :
    (centralizer (T : Set A)).relIndex H = (centralizer (R : Set A)).relIndex H := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A T R
  have he : (T : Subgroup A).map (MulAut.conj g).toMonoidHom = R :=
    congrArg (fun U : Sylow 2 A => (U : Subgroup A)) hg
  have hH : H.map (MulAut.conj g).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hi := relIndex_map_map_of_injective (centralizer (T : Set A)) H
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  simp only [← Sylow.coe_coe] at hi ⊢
  rw [centralizer_conj_map (T : Subgroup A) g, he, hH] at hi
  exact hi.symm

private theorem card_le_square_of_sylow_fixed_index {A : Type*} [Group A] [Finite A]
    (H : Subgroup A) [H.Normal] (T R : Sylow 2 A)
    (hgen : (T : Subgroup A) ⊔ R = ⊤) (hz : center A = ⊥)
    {q : ℕ} (hbound : (centralizer (T : Set A)).relIndex H ≤ q) :
    Nat.card H ≤ q ^ 2 := by
  have he : centralizer (T : Set A) ⊓ centralizer (R : Set A) = ⊥ := by
    apply bot_unique
    intro a ha
    have hc : (T : Subgroup A) ⊔ R ≤ centralizer ({a} : Set A) := by
      apply sup_le
      · intro t ht
        exact mem_centralizer_singleton_iff.mpr (ha.1 t ht)
      · intro t ht
        exact mem_centralizer_singleton_iff.mpr (ha.2 t ht)
    have hac : a ∈ center A := mem_center_iff.mpr fun t =>
      mem_centralizer_singleton_iff.mp (hc (hgen ▸ mem_top t))
    rwa [hz] at hac
  have hi := relIndex_inf_le (H := centralizer (T : Set A))
    (K := centralizer (R : Set A)) (L := H)
  rw [he, relIndex_bot_left, ← centralizer_index_sylow_eq H T R] at hi
  exact hi.trans (by simpa only [pow_two] using Nat.mul_le_mul hbound hbound)

open Subgroup.CosetGeometry.RankTwo Reduction
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The central case on DGS p.180 collapses to the actual natural middle center. -/
theorem source_central_intersection_eq_center
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcentral : V (reducedFamily L S) x 1 ⊓
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ≤
        centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k) :
    let F := reducedFamily L S
    let H := V F x 1 ⊓ V F (base F (!i)) 1
    H = Z F (base F i) ∧
      H.map (G₀ L S).subtype = (Z F (base F i)).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let A := star L S i
  let m := base F i
  let y := base F (!i)
  let H := V F x 1 ⊓ V F y 1
  let J := V F σ 1 ⊓ Q F y
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (L := L) (S := S) i))
    (inclusion_injective _)
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  let : Finite (V F y 1) := Finite.of_injective
    (inclusion ((V_le_neighbor_Q F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hadj.symm).trans
        (Q_le_stabilizer F m))) (inclusion_injective _)
  have hgen : A = (Q F x ⊔ Q F y) ⊔ Q F m := by
    have hh := star_three_core_generation h i hxadj hne T R hT hR
    simpa only [sup_comm, sup_left_comm, sup_assoc] using hh
  have hgenTR : (T : Subgroup A) ⊔ R = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, hT, hR, ← MonoidHom.range_eq_map, range_subtype, hgen]
    ac_rfl
  have hQA : Q F m ≤ A := le_sup_right.trans hgen.ge
  have hYA : Q F y ≤ A := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hJA : J ≤ A := inf_le_right.trans hYA
  have hHA : H ≤ A := (inf_le_left.trans (V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hxadj.symm)).trans hQA
  let : Finite H := Finite.of_injective (inclusion hHA) (inclusion_injective _)
  have hnH : A ≤ normalizer (H : Set (G₀ L S)) := by
    rw [hgen]
    exact intersection_normalized F (fun v => (source_Z_Q_U (reduced_triple h) v).2)
      hxadj.symm hadj.symm hcommx hcommy hzx hzy
  let : (H.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hnH
  let QA := (Q F m).subgroupOf A
  let JA := J.subgroupOf A
  let YA := (Q F y).subgroupOf A
  have hQAcore : QA = pCore 2 A := by
    change (Q (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf A = _
    rw [← star_core h i]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  let : QA.Normal := hQAcore ▸ inferInstance
  have hTY : (T : Subgroup A) = YA ⊔ QA := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hYA, map_subgroupOf_eq_of_le hQA]
    exact hT
  have hiJ : QA.relIndex JA = Nat.card k := by
    rw [relIndex_subgroupOf hJA]
    exact hactor
  obtain ⟨P, _, hP, _⟩ := source_common_sylow_core_index h i e T hT
  have hiY : QA.relIndex YA = Nat.card k := by
    rw [relIndex_subgroupOf hYA]
    rw [inf_relIndex_left] at hP
    exact hP.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 P).symm.toEquiv)
  have hJT : JA ⊔ QA ≤ (T : Subgroup A) := by
    rw [hTY]
    exact sup_le_sup (subgroupOf_mono A inf_le_right) le_rfl
  have hfull : JA ⊔ QA = (T : Subgroup A) := by
    have hiT : QA.relIndex (T : Subgroup A) = Nat.card k := by
      rw [hTY, relIndex_sup_right, hiY]
    have hi := relIndex_mul_relIndex QA (JA ⊔ QA) (T : Subgroup A) le_sup_right hJT
    rw [relIndex_sup_right, hiJ, hiT] at hi
    have hindex : (JA ⊔ QA).relIndex (T : Subgroup A) = 1 :=
      Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := k)) (by simpa using hi)
    exact le_antisymm hJT (relIndex_eq_one.mp hindex)
  have hkill : H ⊓ Q F σ ≤ centralizer (J : Set (G₀ L S)) :=
    (inf_le_inf_right _ inf_le_right).trans (commutator_eq_bot_iff_le_centralizer.mp hcross)
  have hfix : (H ⊓ Q F σ).subgroupOf A ≤ centralizer (T : Set A) := by
    intro a ha
    have hj : JA ≤ centralizer ({a} : Set A) := by
      intro j hj
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact hkill ha j hj
    have hq : QA ≤ centralizer ({a} : Set A) := by
      intro z hz
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact hcentral ha.1 z hz
    have hh : (T : Subgroup A) ≤ centralizer ({a} : Set A) := hfull ▸ sup_le hj hq
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hh ht)
  have hindex : (centralizer (T : Set A)).relIndex (H.subgroupOf A) ≤ Nat.card k := by
    have hi := relIndex_le_of_le_left (L := H.subgroupOf A) hfix
      (by exact index_ne_zero_of_finite)
    rw [relIndex_subgroupOf hHA, inf_relIndex_left] at hi
    exact hi.trans (((Q F σ).relIndex_le_of_le_right (show H ≤ V F y 1 from inf_le_right)
      (by exact index_ne_zero_of_finite)).trans hsmall)
  have hbound := card_le_square_of_sylow_fixed_index (H.subgroupOf A) T R hgenTR hz hindex
  rw [Nat.card_congr (subgroupOfEquivOfLe hHA).toEquiv] at hbound
  have hZH : Z F m ≤ H := le_inf
    (le_iSup_of_le m (le_iSup_of_le ((mem_ball_one F x m).mpr (Or.inl hxadj.symm)) le_rfl))
    (le_iSup_of_le m (le_iSup_of_le ((mem_ball_one F y m).mpr (Or.inl hadj.symm)) le_rfl))
  have he : H = Z F m := (eq_of_le_of_card_ge hZH (hbound.trans_eq hcard.symm)).symm
  exact ⟨he, congrArg (Subgroup.map (G₀ L S).subtype) he⟩

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
