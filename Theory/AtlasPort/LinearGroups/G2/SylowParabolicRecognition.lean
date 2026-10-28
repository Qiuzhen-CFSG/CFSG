module

public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover

/-!
# Aligning a G₂ local subgroup with the two root parabolics

The normalizer of a nontrivial two-core lies in a conjugate root parabolic.
Sylow conjugacy inside its intersection with the derived carrier then aligns
an arbitrary component Sylow with the restricted positive roots, while keeping
the given subgroup in that parabolic. The two restricted parabolics are proper
in a two-reduced derived carrier, and every automorphism fixing the standard
Sylow fixes each of them.

This is the model-geometric step used in Aschbacher–Smith, 15.3.28, printed
p.1131 of the combined manuscript (1 March 2004). Nontriviality of the local
two-core is an explicit premise, not a consequence asserted here. The full
binary model and its proper derived subgroup are never identified. Root and
hexagon calculations come from the licensed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup
open Atlas.G2 Atlas.G2.LieParabolicSetup
namespace Atlas.G2.SylowParabolicRecognition
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def rootParabolic (i : Fin 2) : Subgroup (commutator (Model F)) :=
  (if i = 0 then parabolic₁ else parabolic₂).subgroupOf _

omit [CharP F 2] in
private theorem longRoot_le_derived : longRootLocal (F := F) ≤ commutator (Model F) := by
  by_cases hq : Nat.card F = 2
  · let e := fieldEquiv (binaryFieldEquiv hq)
    have he : (commutator (Model F)).map e.toMonoidHom =
        commutator (Model (ZMod 2)) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    intro x hx
    apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    rw [he, BinaryParabolicPair.commutator_eq_longRootClosure]
    apply subset_normalClosure
    rw [← fieldEquiv_longRootLocal_image (binaryFieldEquiv hq)]
    exact ⟨x, hx, rfl⟩
  · let : Group.IsPerfect (Model F) := isPerfect (by
      have := Finite.one_lt_card (α := F)
      omega)
    rw [Group.IsPerfect.commutator_eq_top]
    exact le_top

omit [Finite F] [CharP F 2] in
private theorem highestRoot_le_longRoot : highestRoot (F := F) ≤ longRootLocal := by
  rintro _ ⟨a, rfl⟩
  exact rootA_mem_longRootLocal a.toAdd

/-- Both restricted root parabolics are proper whenever the derived carrier
has trivial two-core. -/
theorem rootParabolic_ne_top
    (hcore : pCore 2 (commutator (Model F)) = ⊥) (i : Fin 2) :
    rootParabolic (F := F) i ≠ ⊤ := by
  let D := commutator (Model F)
  have prove (N : Subgroup (Model F)) (hND : N ≤ D)
      (hNU : N ≤ unipotent) (hN : Nat.card N ≠ 1) :
      (normalizer (N : Set (Model F))).subgroupOf D ≠ ⊤ := by
    rw [subgroupOf_normalizer_eq hND]
    intro ht
    let : (N.subgroupOf D).Normal := normalizer_eq_top_iff.mp ht
    have hp : IsPGroup 2 (N.subgroupOf D) :=
      (unipotent_isTwoGroup.to_le hNU).of_equiv (subgroupOfEquivOfLe hND).symm
    have hn : N.subgroupOf D ≤ pCore 2 D := le_sSup ⟨inferInstance, hp⟩
    have hb : N.subgroupOf D = ⊥ := bot_unique (hn.trans_eq hcore)
    apply hN
    rw [← Nat.card_congr (subgroupOfEquivOfLe hND).toEquiv, hb, card_bot]
  fin_cases i
  · change parabolic₁.subgroupOf D ≠ ⊤
    rw [← SylowParabolicInvariance.normalizer_highestRoot]
    apply prove highestRoot (highestRoot_le_longRoot.trans longRoot_le_derived)
      (highestRoot_le_longRoot.trans longRootLocal_le_unipotent)
    rw [card_highestRoot]
    exact ne_of_gt Finite.one_lt_card
  · change parabolic₂.subgroupOf D ≠ ⊤
    rw [← SylowParabolicInvariance.normalizer_longRootLocal]
    apply prove longRootLocal longRoot_le_derived longRootLocal_le_unipotent
    rw [card_longRootLocal]
    exact ne_of_gt (one_lt_pow₀ Finite.one_lt_card (by decide : 2 ≠ 0))

theorem rootParabolic_invariant (b : MulAut (commutator (Model F)))
    (hb : (unipotent.subgroupOf (commutator (Model F))).map b.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    (rootParabolic (F := F) i).map b.toMonoidHom = rootParabolic i := by
  obtain ⟨h₁, h₂⟩ := SylowParabolicInvariance.restricted_parabolics_invariant b hb
  fin_cases i
  · exact h₁
  · exact h₂

/-- A nonzero intrinsic two-core puts an overgroup in a root parabolic,
with its Sylow subgroup aligned to the standard restricted positive roots.
The conjugations preserve the actual derived carrier. -/
theorem exists_aligned_parabolic_of_twoCore
    {L : Type*} [Group L] [Finite L] (e : L ≃* commutator (Model F))
    (Q : Sylow 2 L) (H : Subgroup L) (hQH : (Q : Subgroup L) ≤ H)
    (hcore : pCore 2 H ≠ ⊥) :
    ∃ (f : L ≃* commutator (Model F)) (i : Fin 2),
      (Q : Subgroup L).map f.toMonoidHom = unipotent.subgroupOf (commutator (Model F)) ∧
      H.map f.toMonoidHom ≤ rootParabolic i := by
  let D := commutator (Model F)
  let j : H →* Model F := D.subtype.comp (e.toMonoidHom.comp H.subtype)
  have hj : Function.Injective j := D.subtype_injective.comp (e.injective.comp H.subtype_injective)
  let R := (pCore 2 H).map j
  have hR : R ≠ ⊥ := fun h => hcore
    (((pCore 2 H).map_eq_bot_iff_of_injective hj).mp h)
  have hHR (h : H) : j h ∈ normalizer (R : Set (Model F)) := by
    apply (pCore 2 H).le_normalizer_map j
    exact ⟨h, by rw [normalizer_eq_top]; trivial, rfl⟩
  obtain ⟨g, hg⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic R hR
    (pCore_isPGroup.map j)
  let f := e.trans (MulAut.conjNormal (H := D) g)
  have hplace : ∃ i : Fin 2, H.map f.toMonoidHom ≤ rootParabolic i := by
    rcases hg with hg | hg
    · refine ⟨0, ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      exact hg ⟨j ⟨h, hh⟩, hHR ⟨h, hh⟩, rfl⟩
    · refine ⟨1, ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      exact hg ⟨j ⟨h, hh⟩, hHR ⟨h, hh⟩, rfl⟩
  obtain ⟨i, hi⟩ := hplace
  obtain ⟨T, hT⟩ := (sylow (F := F)).exists_subgroupOf_eq_of_normal D
  let Q' := Q.mapSurjective (f := f.toMonoidHom) f.surjective
  have hQP : (Q' : Subgroup D) ≤ rootParabolic i := (map_mono hQH).trans hi
  have hTP : (T : Subgroup D) ≤ rootParabolic i := by
    rw [hT, sylow_coe]
    fin_cases i
    · exact comap_mono (sylow_le_borel.trans borel_le_parabolic₁)
    · exact comap_mono (sylow_le_borel.trans borel_le_parabolic₂)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (rootParabolic (F := F) i)
    (Q'.subtype hQP) (T.subtype hTP)
  rw [Sylow.smul_subtype] at hk
  have hk' : (Q' : Subgroup D).map (MulAut.conj k.val).toMonoidHom = T :=
    congrArg Sylow.toSubgroup (Sylow.subtype_injective hk)
  refine ⟨f.trans (MulAut.conj k.val), i, ?_, ?_⟩
  · change (Q : Subgroup L).map ((MulAut.conj k.val).toMonoidHom.comp f.toMonoidHom) = _
    rw [← map_map]
    exact hk'.trans hT
  · change H.map ((MulAut.conj k.val).toMonoidHom.comp f.toMonoidHom) ≤ _
    rw [← map_map]
    rintro _ ⟨x, hx, rfl⟩
    exact (rootParabolic i).mul_mem
      ((rootParabolic i).mul_mem k.property (hi hx)) ((rootParabolic i).inv_mem k.property)

end Atlas.G2.SylowParabolicRecognition
