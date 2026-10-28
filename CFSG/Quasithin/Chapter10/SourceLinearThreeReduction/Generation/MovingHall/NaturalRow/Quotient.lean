module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The marked original natural-pair quotient over an even field

The two original Sylow-conjugate components generate L₀. The intrinsic
simple-pair product theorem identifies its quotient by O₂(L₀) with two
copies of the specified SL₂ field model, preserving the given coordinates
on L and their conjugate on the other factor. Characteristic two makes
SL₂ equal to its projective quotient; n > 1 supplies simplicity.

This extends the original A₅ product construction without changing its
public interface. It does not classify the original moved module.
Source: Aschbacher--Smith D.3.5--7 and 10.1.1, pp.195--199,741.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {F : Type*} [Field F] [CharP F 2]

/-- The actual natural-pair quotient with the original marking on each factor. -/
theorem source_original_natural_pair_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hnormal : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ eR : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)),
      (∀ l : L, eR (QuotientGroup.mk' _ ⟨l,le_componentOrbit L T l.property⟩) =
        (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, eR (QuotientGroup.mk' _ (originalConjugateOrbitInclusion ht l)) =
        (1,e (QuotientGroup.mk' _ l))) := by
  let R := localOrbit T L
  have hLR : L ≤ R := le_componentOrbit L T
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  let τ : MulAut R := ((MulAut.conj t).subgroupMap R).trans (MulEquiv.subgroupCongr hRt)
  let A := L.subgroupOf R
  let B := A.map τ.toMonoidHom
  have hA : A.IsCComponent :=
    D.maximal.1.1.subgroupOf_of_le hLR (componentOrbit_le_sup L T)
  have hB : B.IsCComponent := hA.map_equiv τ
  have hmapA : A.map R.subtype = L := map_subgroupOf_eq_of_le hLR
  have hmapB : B.map R.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map τ.toMonoidHom from rfl,map_map,
      show R.subtype.comp τ.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp R.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map R.subtype) he).symm.trans hmapA)
  have hp : L ⊔ L.map (MulAut.conj t).toMonoidHom = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hnormal)
      inf_le_right ht htn).symm
  have hgen : A ⊔ B = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,←MonoidHom.range_eq_map,range_subtype,hp]
  let a : A ≃* L := subgroupOfEquivOfLe hLR
  let eA := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  let b : A ≃* B := τ.subgroupMap A
  let eB := (QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)).trans eA
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2:ℕ)) (by omega : 2 ≤ n)
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup SL(2,F) := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
  obtain ⟨q,hq,hk,hfirst,hsecond⟩ :=
    exists_twoCore_product_of_simple_pair A B hA hB hne hgen eA eB
  let eR : (R ⧸ pCore 2 R) ≃* (SL(2,F) × SL(2,F)) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  refine ⟨eR,?_,?_⟩
  · intro l
    exact hfirst (a.symm l)
  · intro l
    have hh := hsecond (b (a.symm l))
    change q (originalConjugateOrbitInclusion ht l) =
      (1,eA (QuotientGroup.mk' _ (b.symm (b (a.symm l))))) at hh
    rw [b.symm_apply_apply] at hh
    exact hh

end CFSG.Quasithin.Chapter10.MovingHall
