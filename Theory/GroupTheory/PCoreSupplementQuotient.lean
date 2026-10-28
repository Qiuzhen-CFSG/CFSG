module
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The prime core of a supplement to a local prime core

If `R O_p(L) = L`, restriction of the literal quotient map identifies
`O_p(R)` with `R ∩ O_p(L)` and gives `R/O_p(R) ≃ L/O_p(L)`.
Only the local group `L` is finite; the ambient completion need not be.
Normality of `R` in `L` is not required.

This is the quotient restriction used for the root-generated local actor
in DGS, *Groups and Graphs* (1985), (14.3)(a), printed p.212.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
variable {L R : Subgroup G} [Finite L]

omit [Fact p.Prime] [Finite L] in
private theorem supplement_quotient_surjective (hRL : R ≤ L)
    (hcover : R ⊔ L.pCoreIn p = L) :
    Function.Surjective ((QuotientGroup.mk' (pCore p L)).comp (inclusion hRL)) := by
  have hn : R ≤ normalizer (L.pCoreIn p : Set G) := by
    have hh := (pCore p L).le_normalizer_map L.subtype
    have hL : L ≤ normalizer (L.pCoreIn p : Set G) := by
      simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, Subgroup.pCoreIn] using hh
    exact hRL.trans hL
  have hprod : (L : Set G) = (L.pCoreIn p : Set G) * (R : Set G) := by
    conv_lhs => rw [← hcover, sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn
  intro z
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore p L) z
  obtain ⟨q,hq,r,hr,he⟩ := hprod ▸ (show l.val ∈ (L : Set G) from l.property)
  obtain ⟨q',hq',heq⟩ := hq
  refine ⟨⟨r,hr⟩,?_⟩
  change QuotientGroup.mk' (pCore p L) (inclusion hRL ⟨r,hr⟩) =
    QuotientGroup.mk' (pCore p L) l
  have hl : l = q' * inclusion hRL ⟨r,hr⟩ := by
    apply Subtype.ext
    change l.val = q'.val*r
    change q'.val = q at heq
    rw [heq]
    exact he.symm
  have hq0 : QuotientGroup.mk' (pCore p L) q' = 1 :=
    (QuotientGroup.eq_one_iff q').mpr hq'
  rw [hl, map_mul, hq0, one_mul]

private theorem supplement_quotient_kernel (hRL : R ≤ L)
    (hcover : R ⊔ L.pCoreIn p = L) :
    ((QuotientGroup.mk' (pCore p L)).comp (inclusion hRL)).ker = pCore p R := by
  let f := (QuotientGroup.mk' (pCore p L)).comp (inclusion hRL)
  let : Finite R := Finite.of_injective (inclusion hRL) (inclusion_injective hRL)
  have hker : IsPGroup p f.ker := by
    have he : f.ker = (pCore p L).comap (inclusion hRL) := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [he]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hRL)
  have hh := f.comap_pCore_of_ker_isPGroup
    (supplement_quotient_surjective hRL hcover) hker
  simpa only [pCore_quotient_pCore_eq_bot, MonoidHom.comap_bot] using hh

/-- The supplement's own prime core is the literal intersection with the
local prime core, without normality of the supplement. -/
theorem pCoreIn_eq_inf_of_supplement (hRL : R ≤ L)
    (hcover : R ⊔ L.pCoreIn p = L) :
    R.pCoreIn p = R ⊓ L.pCoreIn p := by
  have hk := supplement_quotient_kernel hRL hcover
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    refine ⟨r.property,inclusion hRL r,?_,rfl⟩
    have hmem := hk.ge hr
    exact (QuotientGroup.eq_one_iff _).mp hmem
  · rintro ⟨hr,l,hl,he⟩
    refine ⟨⟨x,hr⟩,hk.le ?_,rfl⟩
    change QuotientGroup.mk' (pCore p L) (inclusion hRL ⟨x,hr⟩)=1
    apply (QuotientGroup.eq_one_iff _).mpr
    have hel : inclusion hRL ⟨x,hr⟩=l := Subtype.ext he.symm
    rwa [hel]

/-- The quotient equivalence uses exactly the original inclusion into the
local group and both original prime-core projections. -/
theorem exists_pCoreQuotientEquiv_of_supplement (hRL : R ≤ L)
    (hcover : R ⊔ L.pCoreIn p = L) :
    ∃ e : (R ⧸ pCore p R) ≃* (L ⧸ pCore p L),
      ∀ r : R, e (QuotientGroup.mk' (pCore p R) r) =
        QuotientGroup.mk' (pCore p L) (inclusion hRL r) := by
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (supplement_quotient_kernel hRL hcover).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (supplement_quotient_surjective hRL hcover)),fun _ => rfl⟩

end Theory.GroupTheory
