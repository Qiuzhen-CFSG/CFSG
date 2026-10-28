module
public import Theory.GroupTheory.PCoreNormalizerAction.Residual
public import Theory.GroupTheory.NormalQuotientActionSylowSupplement
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Frattini factorization for a residual inside a normal section

Let K be normal in a finite group, and let X ≤ K be p-perfect and normalized
by O_p(K) and by a Sylow p-subgroup of the ambient group. If Out(K/O_p(K))
is a p-group, then K and the normalizer of X generate the ambient group.
Indeed the Sylow subgroup covers the outer action, while the quotient-action
kernel preserves the image of X. Perfect residual recovery lifts this to X
itself. The relative form keeps all factors in the specified overgroup.

Source application: Aschbacher--Smith 8.3.7, printed pp.724--725, for the
invariant component of the original point centralizer.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A Sylow outer supplement and residual recovery give the normalizer factor. -/
theorem normal_sup_residual_normalizer_eq_top
    (P : Sylow p G) (K X : Subgroup G) [K.Normal]
    (hXK : X ≤ K) (hX : IsPPerfect p X)
    (hcore : K.pCoreIn p ≤ normalizer (X : Set G))
    (hPX : (P : Subgroup G) ≤ normalizer (X : Set G))
    (ho : IsPGroup p (MulAut.Outer (K ⧸ pCore p K))) :
    K ⊔ normalizer (X : Set G) = ⊤ := by
  have hk : (normalQuotientAction K (pCore p K)).ker ≤ normalizer (X : Set G) := by
    intro g hg
    let a : normalizer (K : Set G) := ⟨g, le_normalizer_of_normal (mem_top g)⟩
    have ha : pCoreNormalizerAction p K a = 1 := by
      apply MulEquiv.ext
      intro y
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore p K) y
      rw [pCoreNormalizerAction_mk]
      have he := DFunLike.congr_fun (show normalQuotientAction K (pCore p K) g = 1 from hg)
        (QuotientGroup.mk' (pCore p K) k)
      rw [normalQuotientAction_apply_mk] at he
      exact he
    apply mem_normalizer_of_pCoreNormalizerAction_preserves_image K X hXK hX hcore a
    rw [ha]
    exact map_id _
  apply top_unique
  rw [←normalQuotientAction_sup_sylow_ker P K (pCore p K) ho]
  exact sup_le (sup_le le_sup_left (hPX.trans le_sup_right)) (hk.trans le_sup_right)

/-- The same factorization inside a specified overgroup, with relative normality. -/
theorem relative_residual_normalizer_factor
    (H K X : Subgroup G) (P : Sylow p H)
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hXK : X ≤ K)
    (hX : IsPPerfect p X) (hcore : K.pCoreIn p ≤ normalizer (X : Set G))
    (hPX : (P : Subgroup H).map H.subtype ≤ normalizer (X : Set G))
    (ho : IsPGroup p (MulAut.Outer (K ⧸ pCore p K))) :
    K ⊔ (H ⊓ normalizer (X : Set G)) = H := by
  let K' := K.subgroupOf H
  let X' := X.subgroupOf H
  let : K'.Normal := hKn
  have hXH := hXK.trans hKH
  have hp : IsPPerfect p X' := hX.of_surjective
    (subgroupOfEquivOfLe hXH).symm.toMonoidHom (subgroupOfEquivOfLe hXH).symm.surjective
  have hc : K'.pCoreIn p ≤ normalizer (X' : Set H) := by
    rw [←subgroupOf_normalizer_eq hXH]
    have he : (K'.pCoreIn p).map H.subtype = K.pCoreIn p := by
      rw [pCoreIn_subgroupOf p K H hKH,map_subgroupOf_eq_of_le ((K.pCoreIn_le p).trans hKH)]
    exact map_le_iff_le_comap.mp (he ▸ hcore)
  have ht : (P : Subgroup H) ≤ normalizer (X' : Set H) := by
    rw [←subgroupOf_normalizer_eq hXH]
    exact map_le_iff_le_comap.mp hPX
  let c := QuotientGroup.congr (pCore p K') (pCore p K)
    (subgroupOfEquivOfLe hKH) (pCore_map_iso p _)
  have ho' : IsPGroup p (MulAut.Outer (K' ⧸ pCore p K')) :=
    ho.of_injective (MulAut.outerCongr c).toMonoidHom (MulAut.outerCongr c).injective
  have he := normal_sup_residual_normalizer_eq_top P K' X' (comap_mono hXK) hp hc ht ho'
  have hm := congrArg (Subgroup.map H.subtype) he
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKH,←subgroupOf_normalizer_eq hXH,
    subgroupOf_map_subtype,←MonoidHom.range_eq_map,H.range_subtype,inf_comm] at hm
  exact hm

/-- The relative factorization is an exact setwise product. -/
theorem relative_residual_normalizer_product
    (H K X : Subgroup G) (P : Sylow p H)
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hXK : X ≤ K)
    (hX : IsPPerfect p X) (hcore : K.pCoreIn p ≤ normalizer (X : Set G))
    (hPX : (P : Subgroup H).map H.subtype ≤ normalizer (X : Set G))
    (ho : IsPGroup p (MulAut.Outer (K ⧸ pCore p K))) :
    (H : Set G) = (K : Set G) * (H ⊓ normalizer (X : Set G) : Subgroup G) := by
  have hn : H ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  rw [←coe_mul_of_right_le_normalizer_left K _ (inf_le_left.trans hn),
    relative_residual_normalizer_factor H K X P hKH hKn hXK hX hcore hPX ho]
end Subgroup
