module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.CoreIdentification
public import Theory.GroupTheory.HomocyclicFourSquareRoots

/-!
# The actual homocyclic core and its natural quotient

The identified core has order 64, exponent four, and square kernel V.
Every involution therefore has a square root. The finite abelian recognition
lemma gives the actual C₄³ isomorphism, transported to the intrinsic O₂(L).
Squaring also identifies the original quotient P/V with V; its formula
intertwines the original L-conjugation actions.

Source: Aschbacher--Smith, 14.3.33(1), printed p.1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The constructed center span is homocyclic of rank three and exponent four. -/
theorem centerSpan_homocyclic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    Nonempty (centerSpan L F ≃* (Fin 3 → Multiplicative (ZMod 4))) := by
  let := centerSpan_abelian h structural F s
  have hk := centerSpan_square_kernel_and_card h structural alternatives F s hne
  apply homocyclic_four_of_square_roots 3 hk.2 (centerSpan_exponent_four h structural F s)
  intro x hx
  have hv : (x : G) ∈ V := (hk.1 x x.property).mp (congrArg Subtype.val hx)
  obtain ⟨y, hy, he⟩ := seed_exists_centerSpan_square h F s hv
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- The homocyclic field needed by the final HS consumer, on intrinsic O₂(L). -/
theorem core_homocyclic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    Nonempty (pCore 2 L ≃* (Fin 3 → Multiplicative (ZMod 4))) := by
  obtain ⟨e⟩ := centerSpan_homocyclic h structural alternatives F s hne
  exact ⟨((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).trans
    ((MulEquiv.subgroupCongr (centerSpan_eq_core h structural alternatives F s hne).symm).trans e)⟩

/-- Squaring identifies P/V with the original V. The displayed formula fixes
both the quotient map and the natural module marking. -/
theorem core_quotient_square_equiv
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    ∃ hn : (V.subgroupOf (L.pCoreIn 2)).Normal,
      letI := hn
      ∃ e : (L.pCoreIn 2 ⧸ V.subgroupOf (L.pCoreIn 2)) ≃* V,
        ∀ x : L.pCoreIn 2, (e (QuotientGroup.mk' (V.subgroupOf (L.pCoreIn 2)) x) : G) =
          (x : G) ^ 2 := by
  have heP := centerSpan_eq_core h structural alternatives F s hne
  obtain ⟨f, hf, hfx⟩ := centerSpan_square_map h structural F s
  let t := MulEquiv.subgroupCongr heP.symm
  let q : L.pCoreIn 2 →* V := f.comp t.toMonoidHom
  have hq : Function.Surjective q := hf.comp t.surjective
  have hqx (x : L.pCoreIn 2) : (q x : G) = (x : G) ^ 2 := hfx (t x)
  have hk : q.ker = V.subgroupOf (L.pCoreIn 2) := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff, hqx]
    exact (centerSpan_square_kernel_and_card h structural alternatives F s hne).1 x (t x).property
  let hn : (V.subgroupOf (L.pCoreIn 2)).Normal := hk ▸ q.normal_ker
  let := hn
  let e : (L.pCoreIn 2 ⧸ V.subgroupOf (L.pCoreIn 2)) ≃* V :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  refine ⟨hn, e, ?_⟩
  intro x
  change ((QuotientGroup.quotientKerEquivOfSurjective q hq)
    (QuotientGroup.quotientMulEquivOfEq hk.symm
      (QuotientGroup.mk' (V.subgroupOf (L.pCoreIn 2)) x)) : G) = _
  rw [QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  exact hqx x

/-- Explicit L-equivariance of the marked square quotient, retaining the actual
ambient conjugation and the same quotient representatives. -/
theorem core_quotient_square_equivariant
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    ∃ hn : (V.subgroupOf (L.pCoreIn 2)).Normal,
      letI := hn
      ∃ e : (L.pCoreIn 2 ⧸ V.subgroupOf (L.pCoreIn 2)) ≃* V,
        (∀ x : L.pCoreIn 2, (e (QuotientGroup.mk' (V.subgroupOf (L.pCoreIn 2)) x) : G) =
          (x : G) ^ 2) ∧
        ∀ (l : L) (x : L.pCoreIn 2),
          (e (QuotientGroup.mk' (V.subgroupOf (L.pCoreIn 2))
            ⟨(l : G) * x * (l : G)⁻¹,
              (mem_normalizer_iff.mp ((L.le_normalizer.trans
                (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) l.property) x).mp
                  x.property⟩) : G) =
            (l : G) * e (QuotientGroup.mk' (V.subgroupOf (L.pCoreIn 2)) x) * (l : G)⁻¹ := by
  obtain ⟨hn, e, he⟩ := core_quotient_square_equiv h structural alternatives F s hne
  let := hn
  refine ⟨hn, e, he, ?_⟩
  intro l x
  rw [he, he]
  exact (map_pow (MulAut.conj (l : G)) (x : G) 2).symm

/-- Both full ambient normalizers coincide before the terminal transfer step.
The seed is recovered intrinsically as the square kernel of O₂(L). -/
theorem actor_normalizer_eq_seed_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    normalizer (L : Set G) = normalizer (V : Set G) := by
  let := h.chosen.elementary
  have heP := centerSpan_eq_core h structural alternatives F s hne
  have hVP : V ≤ L.pCoreIn 2 := (seed_le_centerSpan h F).trans_eq heP
  apply le_antisymm ?_ (h.seed_normalizer_le_at structural)
  apply le_normalizer_iff.mpr
  intro g hg v hv
  have hgP := normalizer_le_normalizer_characteristic_image L (pCore 2 L) hg
  have hx : g * v * g⁻¹ ∈ L.pCoreIn 2 := (mem_normalizer_iff.mp hgP v).mp (hVP hv)
  have hxP : g * v * g⁻¹ ∈ centerSpan L F := heP.symm ▸ hx
  apply (centerSpan_square_kernel_and_card h structural alternatives F s hne).1 _ hxP |>.mp
  change (MulAut.conj g v) ^ 2 = 1
  rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian v hv, map_one]

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
