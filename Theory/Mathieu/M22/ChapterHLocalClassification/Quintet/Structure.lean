module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Inner
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Structure.Native
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient

/-!
# The native quintet cores and their literal symmetric quotient

The actual action on the five source tetrads other than the one containing
{0,9} is onto S5. The hexacode column-kernel calculation identifies its kernel
with the restricted E32 translations. Since S5 has trivial two-core, this is
exactly O₂(Q). Lifts fixing both deleted points also prove the inner core
identification. Consequently the actual outer core has order 32 and its
intersection with native M22 has order 16, both elementary abelian.

The quotient equivalence retains its equation on the literal quotient map and
NaturalQuotient.q. It unconditionally supplies the group inputs of the native
cocode top-factor irreducibility theorem. No splitting or conjugation-module
irreducibility is assumed here; the action assertions of H.14.3(2) remain
with their separate assembly owner.

Source: Aschbacher--Smith H.14.3(2) and its proof, printed p.397, with setup
on p.396; the consumer is H.15.4 on p.400. The concrete native/ATLAS comparison
and license attribution are documented in the imported Native and AtlasLocal
modules. All cores are intrinsic to their local stabilizers.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode MathieuCode.M22Quintet
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.Quintet
open Structure
open MathieuCode.M22Quintet.CocodeTransfer
/-- Surjectivity retains a representative fixing zero, hence lying in native M22. -/
theorem q_lift (τ : Equiv.Perm (Fin 5)) :
    ∃ g : Q, NaturalQuotient.q g = τ ∧ g.val.val.val 0 = 0 := by
  let f := finSuccAboveEquiv (0 : Fin 6)
  let u := Equiv.Perm.ofSubtype (f.permCongr τ)
  let σ := NaturalQuotient.partNumbering.permCongr u
  have hσ : σ (NaturalQuotient.partNumbering 0) = NaturalQuotient.partNumbering 0 := by
    change NaturalQuotient.partNumbering
      (u (NaturalQuotient.partNumbering.symm (NaturalQuotient.partNumbering 0))) = _
    rw [NaturalQuotient.partNumbering.symm_apply_apply]
    congr 1
  obtain ⟨g,hg,h0⟩ := Native.lift_parts σ hσ
  refine ⟨g,?_,h0⟩
  apply Equiv.ext
  intro i
  apply Fin.succ_injective
  apply NaturalQuotient.partNumbering.injective
  rw [NaturalQuotient.q_part_compatible,hg]
  change NaturalQuotient.partNumbering (u
    (NaturalQuotient.partNumbering.symm (NaturalQuotient.partNumbering i.succ))) = _
  rw [NaturalQuotient.partNumbering.symm_apply_apply]
  congr 1

theorem q_surjective : Function.Surjective NaturalQuotient.q :=
  fun τ => (q_lift τ).imp fun _ h => h.1

private theorem symmetric_five_core : pCore 2 (Equiv.Perm (Fin 5)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 (Equiv.Perm (Fin 5))) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 5)) hnt
  have hp : IsPGroup 2 (alternatingGroup (Fin 5)) :=
    pCore_isPGroup.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hd : 3 ∣ 2 ^ n := by
    rw [← hn, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

/-- The literal action on all six source parts has kernel O₂(Q). -/
theorem partAction_ker : NaturalQuotient.partAction.ker = pCore 2 Q := by
  have hp : IsPGroup 2 NaturalQuotient.q.ker := by
    rw [NaturalQuotient.q_ker_eq_partAction_ker,Native.part_kernel]
    exact (IsElementaryAbelian.isPGroup 2 outerTranslationGroup).comap_subtype
  have h := NaturalQuotient.q.comap_pCore_of_ker_isPGroup q_surjective hp
  rw [symmetric_five_core,MonoidHom.comap_bot,NaturalQuotient.q_ker_eq_partAction_ker] at h
  exact h

/-- The source translation restriction equals the actual outer quintet two-core. -/
theorem outerTranslations_eq_core :
    Sextet.outerTranslations = m22OuterQuintetKernel m22SourceSextet := by
  have h := congrArg (fun H : Subgroup Q => H.map Q.subtype)
    (Native.part_kernel.symm.trans partAction_ker)
  rw [Subgroup.map_subgroupOf_eq_of_le
    (Sextet.outerTranslations_le_core.trans (Subgroup.map_subtype_le _))] at h
  exact h
private def innerToQ : m22InnerQuintetStabilizer m22SourceSextet →* Q where
  toFun g := ⟨m22ToPairStabilizer g.val,g.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

private theorem innerToQ_injective : Function.Injective innerToQ := by
  intro a b h
  apply Subtype.ext
  apply m22Embedding_injective
  exact congrArg (fun g : Q => g.val.val) h

private def innerQ : m22InnerQuintetStabilizer m22SourceSextet →* Equiv.Perm (Fin 5) :=
  NaturalQuotient.q.comp innerToQ

private theorem innerQ_surjective : Function.Surjective innerQ := by
  intro τ
  obtain ⟨g,hg,h0⟩ := q_lift τ
  obtain ⟨a,ha⟩ := (m22ToPairStabilizer_mem_range_iff_fixed_zero g.val).mpr h0
  have hi : a ∈ m22InnerQuintetStabilizer m22SourceSextet := by
    change m22Embedding a ∈ sextetStabilizer m22SourceSextet
    have he : m22Embedding a = g.val.val := congrArg Subtype.val ha
    rw [he]
    exact g.property
  refine ⟨⟨a,hi⟩,?_⟩
  change NaturalQuotient.q (innerToQ ⟨a,hi⟩) = τ
  have he : innerToQ ⟨a,hi⟩ = g := Subtype.ext ha
  rw [he,hg]

private theorem innerQ_ker :
    innerQ.ker = Sextet.innerTranslations.subgroupOf (m22InnerQuintetStabilizer m22SourceSextet) := by
  ext a
  change innerToQ a ∈ NaturalQuotient.q.ker ↔ _
  rw [NaturalQuotient.q_ker_eq_partAction_ker,Native.part_kernel]
  rfl

/-- The intrinsic inner core is exactly the pointwise pair restriction of the source core. -/
theorem innerTranslations_eq_core :
    Sextet.innerTranslations = m22InnerQuintetKernel m22SourceSextet := by
  have hp : IsPGroup 2 innerQ.ker := by
    have he : innerQ.ker = (pCore 2 Q).comap innerToQ := by
      rw [← partAction_ker,← NaturalQuotient.q_ker_eq_partAction_ker]
      rfl
    rw [he]
    exact pCore_isPGroup.comap_of_injective innerToQ innerToQ_injective
  have h := innerQ.comap_pCore_of_ker_isPGroup innerQ_surjective hp
  rw [symmetric_five_core,MonoidHom.comap_bot,innerQ_ker] at h
  have hh := congrArg (fun H : Subgroup (m22InnerQuintetStabilizer m22SourceSextet) =>
    H.map (m22InnerQuintetStabilizer m22SourceSextet).subtype) h
  rw [Subgroup.map_subgroupOf_eq_of_le
    (Sextet.innerTranslations_le_core.trans (Subgroup.map_subtype_le _))] at hh
  exact hh

/-- The actual outer two-core is elementary abelian of binary dimension five. -/
instance core_elementary : IsElementaryAbelian 2 MathieuCode.M22Quintet.K := by
  rw [MathieuCode.M22Quintet.K, ← outerTranslations_eq_core]
  exact outerTranslationGroup_elementary

instance innerIntersection_elementary : IsElementaryAbelian 2 (MathieuCode.M22Quintet.K ⊓ L : Subgroup m22PairStabilizer) := by
  rw [MathieuCode.M22Quintet.K, ← outerTranslations_eq_core]
  exact innerTranslationGroup_elementary

theorem core_card : Nat.card MathieuCode.M22Quintet.K = 32 := by
  rw [MathieuCode.M22Quintet.K, ← outerTranslations_eq_core]
  exact outerTranslationGroup_card

theorem innerIntersection_card : Nat.card (MathieuCode.M22Quintet.K ⊓ L : Subgroup m22PairStabilizer) = 16 := by
  rw [MathieuCode.M22Quintet.K, ← outerTranslations_eq_core]
  exact innerTranslationGroup_card

theorem inner_core_card : Nat.card (m22InnerQuintetKernel m22SourceSextet) = 16 := by
  rw [← innerTranslations_eq_core]
  exact innerTranslations_card

/-- The canonical quotient isomorphism uses the literal action on the five remaining parts. -/
def quotientEquiv : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq
    (NaturalQuotient.q_ker_eq_partAction_ker.trans partAction_ker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective NaturalQuotient.q q_surjective)

@[simp] theorem quotientEquiv_mk (g : Q) :
    quotientEquiv (QuotientGroup.mk' (pCore 2 Q) g) = NaturalQuotient.q g := rfl

/-- Native H.14 group structure discharges both earlier group inputs of the cocode consumer. -/
theorem top_isIrreducible :
    Representation.IsIrreducible V6Subrepresentation.quotientRepresentation :=
  NaturalQuotient.top_isIrreducible partAction_ker quotientEquiv
end Sporadic.Mathieu.M22ChapterH.Quintet
