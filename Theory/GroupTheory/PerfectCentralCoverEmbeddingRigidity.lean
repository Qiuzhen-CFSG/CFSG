module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# Rigidity of embeddings in perfect central covers

A perfect central cover of a group with trivial Schur multiplier is an
isomorphism: lift the universal cover, use perfectness to make the lift
surjective, and use the trivial universal kernel to obtain injectivity.
Similarly, a subgroup surjecting onto the base of a perfect central cover
is the whole covering group; the subgroup need not be normal.

For a finite quasisimple subgroup K of H, restriction of H → H/Oₚ(H)
is a perfect central cover of its image. Its kernel is the normal p-subgroup
K ∩ Oₚ(H), hence lies in Oₚ(K) ≤ Z(K). Normality of K in H is unnecessary.

Source: the covering formalism of Aschbacher--Smith, I.1.1, printed p.407,
and the central-extension arguments A1 33.4--33.6 implemented in
`PerfectCentralCoverExistence`.
-/

public section

namespace PerfectCentralCovering

open Subgroup Theory.GroupTheory

/-- Triviality of the actual universal kernel makes every perfect central
cover injective. The perfectness of the base follows from the given cover. -/
theorem Cover.injective_of_universalProjection_ker_eq_bot
    {L G : Type*} [Group L] [Group G]
    (f : Cover L G) (hm : (universalProjection G).ker = ⊥) :
    Function.Injective f.toMonoidHom := by
  let : Group.IsPerfect L := f.isPerfect
  let : Group.IsPerfect G := Group.IsPerfect.ofSurjective f.surjective
  obtain ⟨h, hh, _⟩ := universalProjection_existsUnique_lift
    f.toMonoidHom f.surjective f.ker_le_center
  have hs : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect f.toMonoidHom h
      (hh ▸ universalProjection_surjective G) f.ker_le_center
  have hi := (universalProjection G).ker_eq_bot_iff.mp hm
  intro x y hxy
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  apply congrArg h
  apply hi
  simpa only [← hh, MonoidHom.comp_apply] using hxy

/-- The restricted prime-core quotient of a finite quasisimple subgroup
has central kernel, regardless of its normality in the ambient group. -/
theorem pCore_quotient_subgroupMap_ker_le_center
    {H : Type*} [Group H] [Finite H]
    (p : ℕ) [Fact p.Prime] (K : Subgroup H) [IsQuasisimple K] :
    ((QuotientGroup.mk' (pCore p H)).subgroupMap K).ker ≤ center K := by
  rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  apply le_trans _ (IsQuasisimple.pCore_le_center p)
  exact le_sSup ⟨inferInstance,
    pCore_isPGroup.comap_of_injective K.subtype K.subtype_injective⟩

/-- The actual homomorphism K → K Oₚ(H)/Oₚ(H), as a perfect central cover. -/
@[expose] def pCoreQuotientCover
    {H : Type*} [Group H] [Finite H]
    (p : ℕ) [Fact p.Prime] (K : Subgroup H) [IsQuasisimple K] :
    Cover K (K.map (QuotientGroup.mk' (pCore p H))) where
  toMonoidHom := (QuotientGroup.mk' (pCore p H)).subgroupMap K
  surjective := MonoidHom.subgroupMap_surjective _ _
  isPerfect := inferInstance
  ker_le_center := pCore_quotient_subgroupMap_ker_le_center p K

/-- Equal images force equality of nested subgroups when the larger subgroup
is perfect and the restricted kernel is central. No normality is needed. -/
theorem eq_of_le_of_map_eq_of_central_kernel
    {H Q : Type*} [Group H] [Group Q]
    {B K : Subgroup H} [Group.IsPerfect K] (hBK : B ≤ K) (π : H →* Q)
    (hker : (π.subgroupMap K).ker ≤ center K)
    (heq : B.map π = K.map π) : B = K := by
  have hs : Function.Surjective ((π.subgroupMap K).comp (inclusion hBK)) := by
    intro x
    have hx : (x : Q) ∈ B.map π := by rw [heq]; exact x.property
    obtain ⟨b, hb, hbx⟩ := hx
    exact ⟨⟨b, hb⟩, Subtype.ext hbx⟩
  have hi := surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    (π.subgroupMap K) (inclusion hBK) hs hker
  apply le_antisymm hBK
  intro k hk
  obtain ⟨b, hb⟩ := hi ⟨k, hk⟩
  have hb' : (b : H) = k := congrArg Subtype.val hb
  exact hb' ▸ b.property

end PerfectCentralCovering

end
