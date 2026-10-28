module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.Centralizer
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.Residual
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# Faithful lifting from the exceptional six-letter quotient

In the exceptional branch preceding Aschbacher–Smith's final paragraph after
15.4.23 (printed p.1165), the two-perfect factors lie in the normal Sylow
supplement `K`. An actual equivalence `K ≃* A₆` makes `K` centerless, so the
quotient by its centralizer is injective on the entire factor join. This
proves lifting for the factors, their embedded two-cores and their intersection.

The quotient centralizer is proved equal to the source `C_T(K)`. No
identification of either factor is assumed. These are conditional lifting
results; the exceptional witnesses and the finite S₆ recognition are separate.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.Source
variable {G : Type*} [Group G] {d : Geometry G} (h : LocalData d)

/-- Two-perfectness puts both factors inside every normal Sylow supplement. -/
theorem LocalData.factorJoin_le_supplement (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤) :
    d.X i ⊔ d.Y j ≤ K.map (d.I i j).subtype := by
  rw [← h.residual_I i j]
  apply map_mono
  exact sInf_le ⟨inferInstance,
    isPGroup_quotient_of_sup_eq_top K (h.sylow i j) (h.sylow i j).isPGroup' hgen⟩

private theorem center_eq_bot_of_equiv_a6 {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 6)) : center H = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  apply mem_bot.mp
  rw [← Theory.SpecificGroups.SymmetricSix.a6_center_eq_bot]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  simpa only [← map_mul] using congrArg e (mem_center_iff.mp hx z)

/-- The intrinsic normal centralizer gives exactly the source quotient kernel. -/
theorem LocalData.exceptional_centralizer_T (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6)) :
    (((d.T : Subgroup G) ⊓ centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf
      (d.I i j)) = centralizer (K : Set (d.I i j)) := by
  have hk := h.factorJoin_le_supplement i j K hgen
  exact h.centralizer_T_subgroupOf_eq i j K hgen (center_eq_bot_of_equiv_a6 eK)
    (le_sup_left.trans hk) (le_sup_right.trans hk)

/-- Convert an equivalence for the printed `I/C_T(K)` quotient to the
intrinsic centralizer quotient used by `recognitionMap`. -/
noncomputable def LocalData.exceptionalQuotientEquiv (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    [(((d.T : Subgroup G) ⊓ centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf
      (d.I i j)).Normal]
    (eT : ((d.I i j) ⧸ (((d.T : Subgroup G) ⊓
      centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf (d.I i j))) ≃*
      Equiv.Perm (Fin 6)) :
    ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq
    (h.exceptional_centralizer_T i j K hgen eK).symm).trans eT

/-- The actual quotient homomorphism followed by the supplied S₆ equivalence. -/
def recognitionMap (i j : Bool) (K : Subgroup (d.I i j)) [K.Normal]
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6)) :
    d.I i j →* Equiv.Perm (Fin 6) :=
  eQ.toMonoidHom.comp (QuotientGroup.mk' (centralizer (K : Set (d.I i j))))

theorem recognitionMap_surjective (i j : Bool) (K : Subgroup (d.I i j)) [K.Normal]
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6)) :
    Function.Surjective (recognitionMap i j K eQ) :=
  eQ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem recognitionMap_ker (i j : Bool) (K : Subgroup (d.I i j)) [K.Normal]
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6)) :
    (recognitionMap i j K eQ).ker = centralizer (K : Set (d.I i j)) := by
  ext x
  change eQ ((QuotientGroup.mk' (centralizer (K : Set (d.I i j)))) x) = 1 ↔ _
  rw [← eQ.map_one, eQ.injective.eq_iff, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

/-- The entire quotient kernel is contained in the common Sylow subgroup. -/
theorem LocalData.recognitionMap_ker_le_sylow (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6)) :
    (recognitionMap i j K eQ).ker ≤ (h.sylow i j : Subgroup (d.I i j)) := by
  rw [recognitionMap_ker]
  exact centralizer_le_sylow_of_centerless_supplement K (h.sylow i j) hgen
    (center_eq_bot_of_equiv_a6 eK)

/-- The quotient loses no element of the factor join, hence no element of either core. -/
theorem LocalData.recognitionMap_injective_on_factorJoin (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6)) :
    Function.Injective ((recognitionMap i j K eQ).comp
      (inclusion (sup_le (d.X_le_I i j) (d.Y_le_I i j)))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxC : (inclusion (sup_le (d.X_le_I i j) (d.Y_le_I i j)) x) ∈
      centralizer (K : Set (d.I i j)) := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply eQ.injective
    change eQ ((QuotientGroup.mk' (centralizer (K : Set (d.I i j))))
      (inclusion (sup_le (d.X_le_I i j) (d.Y_le_I i j)) x)) = 1 at hx
    simpa only [QuotientGroup.mk'_apply, map_one] using hx
  have hxK : (inclusion (sup_le (d.X_le_I i j) (d.Y_le_I i j)) x) ∈ K := by
    have hx' := h.factorJoin_le_supplement i j K hgen x.property
    obtain ⟨y, hy, he⟩ := hx'
    have he' : y = inclusion (sup_le (d.X_le_I i j) (d.Y_le_I i j)) x :=
      Subtype.ext he
    exact he' ▸ hy
  have hz : (⟨inclusion (sup_le (d.X_le_I i j) (d.Y_le_I i j)) x, hxK⟩ : K) ∈
      center K := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (hxC k k.property)
  rw [center_eq_bot_of_equiv_a6 eK, mem_bot] at hz
  exact Subtype.ext (congrArg (fun k : K => ((k : d.I i j) : G)) hz)

end CFSG.Quasithin.Chapter15.Section04.Source

namespace CFSG.Quasithin.Chapter15.Section04.Source
open Subgroup
variable {G : Type*} [Group G] {d : Geometry G} (h : LocalData d)

/-- The ambient quotient map restricts to an equivalence on every subgroup
of the selected factor join, including the factors and their core join. -/
noncomputable def LocalData.recognitionEquiv (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6))
    (L : Subgroup G) (hL : L ≤ d.X i ⊔ d.Y j) :
    L ≃* ((L.subgroupOf (d.I i j)).map (recognitionMap i j K eQ)) := by
  let f := recognitionMap i j K eQ
  let A := L.subgroupOf (d.I i j)
  have hLI : L ≤ d.I i j := hL.trans (sup_le (d.X_le_I i j) (d.Y_le_I i j))
  refine (subgroupOfEquivOfLe hLI).symm.trans (MulEquiv.ofBijective (f.subgroupMap A) ?_)
  refine ⟨?_, f.subgroupMap_surjective A⟩
  intro x y he
  have he' : f x.val = f y.val := congrArg Subtype.val he
  have hh := h.recognitionMap_injective_on_factorJoin i j K hgen eK eQ
    (a₁ := ⟨x.val.val, hL x.property⟩) (a₂ := ⟨y.val.val, hL y.property⟩) he'
  exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(d.X i ⊔ d.Y j) => (z : G)) hh))

theorem LocalData.recognitionEquiv_apply (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6))
    (L : Subgroup G) (hL : L ≤ d.X i ⊔ d.Y j) (x : L) :
    (h.recognitionEquiv i j K hgen eK eQ L hL x : Equiv.Perm (Fin 6)) =
      recognitionMap i j K eQ ⟨x, hL.trans (sup_le (d.X_le_I i j) (d.Y_le_I i j)) x.property⟩ := rfl

/-- Embedded two-cores lift because the quotient restricts to an equivalence. -/
theorem LocalData.recognition_core_map (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6))
    (L : Subgroup G) (hL : L ≤ d.X i ⊔ d.Y j) :
    ((L.pCoreIn 2).subgroupOf (d.I i j)).map (recognitionMap i j K eQ) =
      ((L.subgroupOf (d.I i j)).map (recognitionMap i j K eQ)).pCoreIn 2 := by
  let e := h.recognitionEquiv i j K hgen eK eQ L hL
  have hLI : L ≤ d.I i j := hL.trans (sup_le (d.X_le_I i j) (d.Y_le_I i j))
  have hc : (L.pCoreIn 2).subgroupOf (d.I i j) =
      (pCore 2 L).map (inclusion hLI) := by
    apply Subgroup.map_injective (d.I i j).subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 L).trans hLI), map_map]
    rfl
  rw [hc, map_map, pCoreIn, ← pCore_map_iso 2 e, map_map]
  rfl

/-- Injectivity on the whole join preserves intersections, not just factor orders. -/
theorem LocalData.recognition_inf_map (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6))
    (A B : Subgroup G) (hA : A ≤ d.X i ⊔ d.Y j) (hB : B ≤ d.X i ⊔ d.Y j) :
    ((A ⊓ B).subgroupOf (d.I i j)).map (recognitionMap i j K eQ) =
      ((A.subgroupOf (d.I i j)).map (recognitionMap i j K eQ)) ⊓
      ((B.subgroupOf (d.I i j)).map (recognitionMap i j K eQ)) := by
  apply le_antisymm
  · exact le_inf (map_mono (comap_mono inf_le_left)) (map_mono (comap_mono inf_le_right))
  · rintro x ⟨⟨a, ha, hax⟩, b, hb, hbx⟩
    have hab := h.recognitionMap_injective_on_factorJoin i j K hgen eK eQ
      (a₁ := ⟨a.val, hA ha⟩) (a₂ := ⟨b.val, hB hb⟩) (hax.trans hbx.symm)
    have he : a = b := Subtype.ext (congrArg (fun z : ↥(d.X i ⊔ d.Y j) => (z : G)) hab)
    exact ⟨a, ⟨ha, he ▸ hb⟩, hax⟩

end CFSG.Quasithin.Chapter15.Section04.Source
