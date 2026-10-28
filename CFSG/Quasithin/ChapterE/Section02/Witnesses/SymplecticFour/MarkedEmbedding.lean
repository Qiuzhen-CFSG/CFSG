module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.MiddleRecognition
public import Theory.GroupTheory.NormalCoreTwoClosedTransport
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Data.Fintype.Shrink
public import Theory.SpecificGroups.SymplecticFour.Sylow.CoreFree

/-!
# Marked symplectic pairs from actual matrix embeddings

An injective matrix model whose inverse images of the original Sylow and
maximal subgroup are the standard unipotent and Borel groups gives the
literal two-conjugate pair. Its Borel core is trivial for every finite binary
coefficient field, including the S6 endpoint. Original centrality then gives
the exact quotient-Sylow center mark used in E.2.13.

The field is transported to a small-universe copy only because MarkedModel
stores a field in Type; the explicit field equivalence preserves its order.
The source coefficient-copy adapter discharges the marking hypotheses below.

Source: Aschbacher--Smith E.2.7--9 and E.2.13, printed pp.219--225.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
variable {G K : Type*} [Group G] [Finite G] [Field K] [Finite K] [CharP K 2]

omit [Finite G] in
private theorem pair_map {D : Type*} [Group D] (f : D →* G) (V : Subgroup D) (g : D) :
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f =
      V.map f ⊔ (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup,map_map,map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

/-- An actual marked matrix embedding constructs the quotient pair. This
transport helper is applied below to the recognized literal coefficient copy. -/
theorem markedModel_of_embedding
    (T : Sylow 2 G) (M V : Subgroup G) (hVT : V ≤ T)
    (j : Sp K →* G) (hj : Function.Injective j)
    (hT : (T : Subgroup G).comap j = unipotent)
    (hM : M.comap j = Theory.SpecificGroups.SymplecticFour.borel)
    (g : Sp K) (hgen : V ⊔ V.map (MulAut.conj (j g)).toMonoidHom = j.range)
    (hcentral : ∀ v ∈ V, ∀ s ∈ (T : Subgroup G) ⊓ j.range, v*s=s*v) :
    Nonempty (MarkedModel T M V) := by
  let := Fintype.ofFinite K
  obtain ⟨n,_,hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  let I := j.range
  let e : Sp K ≃* I := MonoidHom.ofInjective hj
  have he (x : Sp K) : (e x : G) = j x := rfl
  have hVI : V ≤ I := by change V ≤ j.range; rw [←hgen]; exact le_sup_left
  let t : I := e g
  have hgenerate : V.subgroupOf I ⊔
      (V.subgroupOf I).map (MulAut.conj t).toMonoidHom = ⊤ := by
    apply map_injective I.subtype_injective
    rw [pair_map,map_subgroupOf_eq_of_le hVI,←MonoidHom.range_eq_map,range_subtype]
    exact hgen
  let U := unipotentSylow hK n.pos
  let P := U.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPeq : (P : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I := by
    change (unipotent.map e.toMonoidHom).map I.subtype = _
    rw [map_map]
    change unipotent.map j = _
    rw [←hT,map_comap_eq]
    exact inf_comm _ _
  have hA : M.subgroupOf I = (Theory.SpecificGroups.SymplecticFour.borel (F := K)).comap e.symm.toMonoidHom := by
    ext x
    change (x : G) ∈ M ↔ e.symm x ∈ Theory.SpecificGroups.SymplecticFour.borel
    rw [←hM]
    change (x : G) ∈ M ↔ j (e.symm x) ∈ M
    rw [←he,e.apply_symm_apply]
  have hcore : (M.subgroupOf I).normalCore = ⊥ := by
    rw [hA,normalCore_comap_of_surjective _ e.symm.surjective,
      borel_normalCore_eq_bot,MonoidHom.comap_bot,
      (MonoidHom.ker_eq_bot_iff e.symm.toMonoidHom).mpr e.symm.injective]
  let w : QuotientLift.Pair T M V := {
    subgroup := I
    le := hVI
    conjugator := t
    generate := hgenerate
    sylow := P
    sylow_eq := hPeq
    core_two_closed := by rw [hcore]; exact ⟨default,inferInstance⟩ }
  let k : K ≃+* Shrink.{0} K := (Shrink.ringEquiv.{0,_} K).symm
  let : CharP (Shrink.{0} K) 2 := (k.toRingHom.charP_iff_charP 2).mp inferInstance
  let a := Binary.fieldEquivSp k
  let r := e.symm.trans a
  let q := BenderPlacement.coreFreeQuotientEquiv (M.subgroupOf I) hcore
  let Q := P.mapSurjective (f := r.toMonoidHom) r.surjective
  have hS : (P : Subgroup I).map e.symm.toMonoidHom = unipotent := by
    change (unipotent.map e.toMonoidHom).map e.symm.toMonoidHom = unipotent
    rw [map_map]
    simp
  have hB : (M.subgroupOf I).map e.symm.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel := by
    rw [hA,map_comap_eq_self_of_surjective e.symm.surjective]
  have hNP : normalizer ((P : Subgroup I) : Set I) = M.subgroupOf I := by
    apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
    rw [map_normalizer_eq_of_bijective (P : Subgroup I) (f := e.symm.toMonoidHom)
      e.symm.bijective,hS,hB,←borel_eq_normalizer_unipotent]
  have hN : (M.subgroupOf I).map r.toMonoidHom = normalizer (Q : Set (Sp (Shrink.{0} K))) := by
    change (M.subgroupOf I).map r.toMonoidHom =
      normalizer (((P : Subgroup I).map r.toMonoidHom) : Set (Sp (Shrink.{0} K)))
    rw [←map_normalizer_eq_of_bijective (P : Subgroup I) (f := r.toMonoidHom) r.bijective,hNP]
  have hqmap : (q.trans r).toMonoidHom.comp
      (QuotientGroup.mk' (M.subgroupOf I).normalCore) = r.toMonoidHom := by
    ext x
    rfl
  refine ⟨{
    pair := w
    F := Shrink.{0} K
    model := q.trans r
    modelSylow := Q
    borel_placement := ?_
    center_placement := ?_
    exponent := n
    field_card := (Nat.card_congr k.toEquiv.symm).trans hK
    exponent_positive := n.pos }⟩
  · rw [map_map,hqmap]
    exact hN
  · rw [hqmap]
    rintro _ ⟨v,hv,rfl⟩
    have hvP : v ∈ (P : Subgroup I) := by
      have hvTI : (v : G) ∈ (T : Subgroup G) ⊓ I := ⟨hVT hv,v.property⟩
      rw [←hPeq] at hvTI
      obtain ⟨u,hu,heu⟩ := hvTI
      exact (I.subtype_injective heu) ▸ hu
    have hvQ : r v ∈ (Q : Subgroup (Sp (Shrink.{0} K))) := mem_map_of_mem _ hvP
    refine ⟨⟨r v,hvQ⟩,mem_center_iff.mpr ?_,rfl⟩
    intro s
    obtain ⟨u,hu,heu⟩ := s.property
    apply Subtype.ext
    change (s : Sp (Shrink.{0} K)) * r v = r v * (s : Sp (Shrink.{0} K))
    rw [←heu]
    change r u * r v = r v * r u
    rw [←map_mul,←map_mul]
    apply congrArg r
    apply Subtype.ext
    have huTI : (u : G) ∈ (T : Subgroup G) ⊓ I := hPeq ▸ mem_map_of_mem I.subtype hu
    exact (hcentral v hv u huTI).symm

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
