module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment.ReducedPair

/-!
# Restoring the original overlap and endpoint quotients

For the genuine F.1.1 pair, put S₀ = O₂(B), B₀ = B(L,S₀), and
Pᵢ₀ = Pᵢ(L,S₀). The existing reduction identifies B₀ with the DGS
product of both starred Borel intersections and O₂(B), and preserves
both embedded endpoint cores. Here the product decompositions prove
Pᵢ₀ ∩ B = B₀ and Pᵢ₀ ∩ S = S₀. Inclusion induces the marked
isomorphisms B/B₀ ≃ Pᵢ/Pᵢ₀, all of which are two-groups, and the
identity |S| = |S₀|[B:B₀]. Inclusion on core quotients is injective.

These are restoration tools for DGS (15.1)–(15.3), printed pp.226–231,
and Aschbacher–Smith F.1.9–12, printed pp.261–264. They do not identify
an arbitrary reduced pair with a model or classify its outer action.
Normality is relative to the original endpoint or overlap throughout.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

theorem borel_normalizes_reduced (h : HypothesisF11 L S) :
    commonBorel L S ≤ normalizer (commonBorel L (reducedSylow L S) : Set G) := by
  unfold commonBorel
  rw [reduced_borel h 0, reduced_borel h 1]
  apply (le_inf ((le_inf (h.commonBorel_normalizes_borel 0)
    (h.commonBorel_normalizes_borel 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) ?_).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact (commonBorel L S).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

theorem parabolic_normalizes_reduced (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L S i ≤ normalizer (parabolic L (reducedSylow L S) i : Set G) := by
  rw [parabolic_eq_sup_commonBorel, parabolic_eq_sup_commonBorel]
  exact sup_le (le_sup_left.trans (L i ⊔ commonBorel L (reducedSylow L S)).le_normalizer)
    ((le_inf (h.commonBorel_normalizes_local i)
      (borel_normalizes_reduced h)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))

theorem reduced_borel_normal (h : HypothesisF11 L S) :
    ((commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S)).Normal :=
  normal_subgroupOf_of_le_normalizer (borel_normalizes_reduced h)

theorem reduced_parabolic_normal (h : HypothesisF11 L S) (i : Fin 2) :
    ((parabolic L (reducedSylow L S) i).subgroupOf (parabolic L S i)).Normal :=
  normal_subgroupOf_of_le_normalizer (parabolic_normalizes_reduced h i)

theorem reduced_borel_supplement (h : HypothesisF11 L S) :
    commonBorel L (reducedSylow L S) ⊔ S = commonBorel L S := by
  unfold commonBorel
  rw [reduced_borel h 0, reduced_borel h 1, sup_assoc,
    sup_eq_right.mpr (reducedSylow_le h)]

theorem reduced_parabolic_supplement (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (reducedSylow L S) i ⊔ commonBorel L S = parabolic L S i := by
  rw [parabolic_eq_sup_commonBorel, parabolic_eq_sup_commonBorel, sup_assoc,
    sup_eq_right.mpr (reduced_commonBorel_le h)]

theorem reduced_parabolic_inf_borel (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (reducedSylow L S) i ⊓ commonBorel L S =
      commonBorel L (reducedSylow L S) := by
  apply le_antisymm _ (le_inf (commonBorel_le_parabolic i) (reduced_commonBorel_le h))
  intro x hx
  have hxprod : x ∈ (L i : Set G) * (commonBorel L (reducedSylow L S) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      ((reduced_hypothesis h).commonBorel_normalizes_local i)]
    change x ∈ L i ⊔ commonBorel L (reducedSylow L S)
    rw [← parabolic_eq_sup_commonBorel]
    exact hx.1
  obtain ⟨l, hl, b, hb, rfl⟩ := hxprod
  have hlB : l ∈ commonBorel L S :=
    ((commonBorel L S).mul_mem_cancel_right (reduced_commonBorel_le h hb)).mp hx.2
  have hlb : l ∈ borel (L i) (reducedSylow L S) := by
    rw [reduced_borel h i, ← h.local_inf_commonBorel i]
    exact ⟨hl, hlB⟩
  exact (commonBorel L (reducedSylow L S)).mul_mem (borel_le_commonBorel i hlb) hb

theorem reduced_borel_inf_sylow (h : HypothesisF11 L S) :
    commonBorel L (reducedSylow L S) ⊓ S = reducedSylow L S := by
  obtain ⟨T, hT⟩ := (reduced_hypothesis h).sylow_commonBorel
  have hle : (T : Subgroup (commonBorel L (reducedSylow L S))) ≤
      S.subgroupOf (commonBorel L (reducedSylow L S)) := by
    intro x hx
    have hx' : (x : G) ∈ (T : Subgroup (commonBorel L (reducedSylow L S))).map
        (commonBorel L (reducedSylow L S)).subtype := mem_map_of_mem _ hx
    rw [hT] at hx'
    exact reducedSylow_le h hx'
  have he := T.is_maximal' h.S_isP.comap_subtype hle
  have hm := congrArg (fun A : Subgroup (commonBorel L (reducedSylow L S)) =>
    A.map (commonBorel L (reducedSylow L S)).subtype) he
  change (S.subgroupOf (commonBorel L (reducedSylow L S))).map
    (commonBorel L (reducedSylow L S)).subtype = _ at hm
  rw [subgroupOf_map_subtype, hT, inf_comm] at hm
  exact hm

theorem reduced_parabolic_inf_sylow (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (reducedSylow L S) i ⊓ S = reducedSylow L S := by
  calc
    _ = (parabolic L (reducedSylow L S) i ⊓ commonBorel L S) ⊓ S := by
      rw [inf_assoc, inf_eq_right.mpr (show S ≤ commonBorel L S from le_sup_right)]
    _ = _ := by rw [reduced_parabolic_inf_borel h i, reduced_borel_inf_sylow h]

def borelToParabolicQuotient (h : HypothesisF11 L S) (i : Fin 2) :
    letI := reduced_parabolic_normal h i
    commonBorel L S →* parabolic L S i ⧸
      (parabolic L (reducedSylow L S) i).subgroupOf (parabolic L S i) :=
  letI := reduced_parabolic_normal h i
  (QuotientGroup.mk' _).comp (inclusion (commonBorel_le_parabolic i))

theorem borelToParabolicQuotient_ker (h : HypothesisF11 L S) (i : Fin 2) :
    letI := reduced_parabolic_normal h i
    (borelToParabolicQuotient h i).ker =
      (commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S) := by
  let := reduced_parabolic_normal h i
  ext x
  change QuotientGroup.mk (inclusion (commonBorel_le_parabolic i) x) =
    (1 : parabolic L S i ⧸ _) ↔ (x : G) ∈ commonBorel L (reducedSylow L S)
  rw [QuotientGroup.eq_one_iff, ← reduced_parabolic_inf_borel h i]
  exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩

theorem borelToParabolicQuotient_surjective (h : HypothesisF11 L S) (i : Fin 2) :
    letI := reduced_parabolic_normal h i
    Function.Surjective (borelToParabolicQuotient h i) := by
  let := reduced_parabolic_normal h i
  intro z
  induction z using QuotientGroup.induction_on with
  | H x =>
    have hxprod : (x : G) ∈ (L i : Set G) * (commonBorel L S : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (h.commonBorel_normalizes_local i)]
      change (x : G) ∈ L i ⊔ commonBorel L S
      rw [← parabolic_eq_sup_commonBorel]
      exact x.property
    obtain ⟨l, hl, b, hb, he⟩ := hxprod
    let l' : parabolic L S i := ⟨l, (le_sup_left.trans le_sup_left :
      L i ≤ parabolic L S i) hl⟩
    have hkill : (QuotientGroup.mk' ((parabolic L (reducedSylow L S) i).subgroupOf
        (parabolic L S i))) l' = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ((le_sup_left.trans le_sup_left :
        L i ≤ parabolic L (reducedSylow L S) i) hl)
    have hx : l' * inclusion (commonBorel_le_parabolic i) ⟨b, hb⟩ = x := Subtype.ext he
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [← hx]
    change _ = (QuotientGroup.mk' _) (_ * _)
    rw [map_mul, hkill, one_mul]
    rfl

@[expose] def borelQuotientEquivParabolic (h : HypothesisF11 L S) (i : Fin 2) :
    letI := reduced_borel_normal h
    letI := reduced_parabolic_normal h i
    (commonBorel L S ⧸ (commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S)) ≃*
      (parabolic L S i ⧸ (parabolic L (reducedSylow L S) i).subgroupOf (parabolic L S i)) :=
  letI := reduced_borel_normal h
  letI := reduced_parabolic_normal h i
  (QuotientGroup.quotientMulEquivOfEq (borelToParabolicQuotient_ker h i).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (borelToParabolicQuotient_surjective h i))

@[simp] theorem borelQuotientEquivParabolic_mk (h : HypothesisF11 L S) (i : Fin 2)
    (b : commonBorel L S) :
    letI := reduced_borel_normal h
    letI := reduced_parabolic_normal h i
    borelQuotientEquivParabolic h i (QuotientGroup.mk b) =
      QuotientGroup.mk (inclusion (commonBorel_le_parabolic i) b) := by rfl

theorem parabolic_extension_index (h : HypothesisF11 L S) (i : Fin 2) :
    (parabolic L (reducedSylow L S) i).relIndex (parabolic L S i) =
      (commonBorel L (reducedSylow L S)).relIndex (commonBorel L S) := by
  let := reduced_borel_normal h
  let := reduced_parabolic_normal h i
  exact (Nat.card_congr (borelQuotientEquivParabolic h i).toEquiv).symm

theorem sylow_extension_index (h : HypothesisF11 L S) :
    (reducedSylow L S).relIndex S =
      (commonBorel L (reducedSylow L S)).relIndex (commonBorel L S) := by
  let B := commonBorel L S
  let N := (commonBorel L (reducedSylow L S)).subgroupOf B
  let := reduced_borel_normal h
  have hi := relIndex_sup_left (S.subgroupOf B) N
  rw [← subgroupOf_sup (reduced_commonBorel_le h)
    (show S ≤ B from le_sup_right), reduced_borel_supplement h,
    relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf (show S ≤ B from le_sup_right)] at hi
  rw [← inf_relIndex_right _ S, reduced_borel_inf_sylow h] at hi
  exact hi.symm

theorem original_sylow_card (h : HypothesisF11 L S) :
    Nat.card S = Nat.card (reducedSylow L S) *
      (commonBorel L (reducedSylow L S)).relIndex (commonBorel L S) := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (reducedSylow L S) S
    bot_le (reducedSylow_le h)
  simpa only [relIndex_bot_left, sylow_extension_index h] using hc.symm

/-- The full original overlap adds only a two-group to the reduced overlap. -/
theorem borel_extension_isPGroup (h : HypothesisF11 L S) :
    letI := reduced_borel_normal h
    IsPGroup 2 (commonBorel L S ⧸
      (commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S)) := by
  let := reduced_borel_normal h
  apply isPGroup_quotient_of_sup_eq_top _ (S.subgroupOf (commonBorel L S))
    h.S_isP.comap_subtype
  rw [← subgroupOf_sup (reduced_commonBorel_le h)
    (show S ≤ commonBorel L S from le_sup_right), reduced_borel_supplement h]
  exact subgroupOf_self _

/-- The same actual two-group is added at either endpoint. -/
theorem parabolic_extension_isPGroup (h : HypothesisF11 L S) (i : Fin 2) :
    letI := reduced_parabolic_normal h i
    IsPGroup 2 (parabolic L S i ⧸
      (parabolic L (reducedSylow L S) i).subgroupOf (parabolic L S i)) := by
  let := reduced_borel_normal h
  let := reduced_parabolic_normal h i
  exact (borel_extension_isPGroup h).of_equiv (borelQuotientEquivParabolic h i)

private theorem core_mem_iff (h : HypothesisF11 L S) (i : Fin 2)
    (x : parabolic L (reducedSylow L S) i) :
    inclusion (reduced_parabolic_le h i) x ∈ pCore 2 (parabolic L S i) ↔
      x ∈ pCore 2 (parabolic L (reducedSylow L S) i) := by
  rw [← mem_map_iff_mem (f := (parabolic L S i).subtype)
    (parabolic L S i).subtype_injective,
    ← mem_map_iff_mem (f := (parabolic L (reducedSylow L S) i).subtype)
    (parabolic L (reducedSylow L S) i).subtype_injective]
  change (x : G) ∈ twoCore (parabolic L S i) ↔
    (x : G) ∈ twoCore (parabolic L (reducedSylow L S) i)
  rw [reduced_parabolic_core h i]

/-- Inclusion on the literal intrinsic core quotients. -/
def coreQuotientMap (h : HypothesisF11 L S) (i : Fin 2) :
    (parabolic L (reducedSylow L S) i ⧸ pCore 2 (parabolic L (reducedSylow L S) i)) →*
      (parabolic L S i ⧸ pCore 2 (parabolic L S i)) :=
  QuotientGroup.map _ _ (inclusion (reduced_parabolic_le h i))
    (fun x hx => (core_mem_iff h i x).mpr hx)

@[simp] theorem coreQuotientMap_mk (h : HypothesisF11 L S) (i : Fin 2)
    (x : parabolic L (reducedSylow L S) i) :
    coreQuotientMap h i (QuotientGroup.mk x) =
      QuotientGroup.mk (inclusion (reduced_parabolic_le h i) x) := by rfl

/-- Preservation of the original two-core makes the quotient inclusion injective. -/
theorem coreQuotientMap_injective (h : HypothesisF11 L S) (i : Fin 2) :
    Function.Injective (coreQuotientMap h i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H x =>
    change coreQuotientMap h i (QuotientGroup.mk x) = 1 at hz
    rw [coreQuotientMap_mk, QuotientGroup.eq_one_iff, core_mem_iff h i x] at hz
    exact mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr hz)

/-- Solvability passes back to the original endpoint through the unchanged local quotient. -/
theorem parabolic_solvable_iff_reduced (h : HypothesisF11 L S) (i : Fin 2) :
    Group.IsSolvable (parabolic L S i) ↔
      Group.IsSolvable (parabolic L (reducedSylow L S) i) :=
  (h.parabolic_solvable_iff_local_quotient i).trans
    ((reduced_hypothesis h).parabolic_solvable_iff_local_quotient i).symm

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
