module

public import Theory.GroupTheory.ReducedNormal.Inheritance
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.GroupTheory.PCoreCentralQuotient

/-!
# Reduced closures of irreducible sections in characteristic two

Let a group of characteristic two have an elementary abelian subgroup V
containing the kernel of a surjection. Suppose a Sylow overgroup acts
irreducibly on the nonzero image of V and normalizes V. Then the image's
normal closure is two-reduced, with the literal centralizer quotient.

The normal centralizer of the kernel has characteristic two, as does its
image through the central kernel. The nonzero intersection of the seed
with the Sylow center therefore lies in the target two-core. Irreducibility
puts the whole seed in that core and makes it central there. Its closure
is elementary abelian. The same Sylow-center intersection generates that
closure, so reducedness follows from Sylow-overgroup inheritance.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.2, printed p.332, using the normal inheritance in 1.1.3(2),
central-quotient descent A.1.8, and the reducedness argument of B.2.13.
The commutator decomposition also asserted in B.2.13 is not needed here.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem normalizes_image {H : Type*} [Group H] (f : G →* H)
    {A V : Subgroup G} (h : A ≤ normalizer (V : Set G)) :
    A.map f ≤ normalizer (V.map f : Set H) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨a, ha, rfl⟩ _ ⟨v, hv, rfl⟩
  exact ⟨a * v * a⁻¹, le_normalizer_iff.mp h a ha v hv, by simp⟩

private theorem normalizes_preimage {H : Type*} [Group H] (f : G →* H)
    {A : Subgroup G} {V : Subgroup H} (h : A.map f ≤ normalizer (V : Set H)) :
    A ≤ normalizer (V.comap f : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha v hv
  change f (a * v * a⁻¹) ∈ V
  simpa using le_normalizer_iff.mp h (f a) (mem_map_of_mem f ha) (f v) hv

private theorem minimal_image {K : Type*} [Group K] (q : G →* K)
    (V A : Subgroup G) (hNV : q.ker ≤ V) (hAV : A ≤ normalizer (V : Set G))
    (hirr : ∀ E : Subgroup G, q.ker ≤ E → E ≤ V → A ≤ normalizer (E : Set G) →
      E = q.ker ∨ E = V) :
    ∀ B : Subgroup K, B ≤ V.map q → A.map q ≤ normalizer (B : Set K) →
      B = ⊥ ∨ B = V.map q := by
  intro B hB hn
  let E := B.comap q ⊓ V
  have hNE : q.ker ≤ E := by
    intro x hx
    exact ⟨by change q x ∈ B; rw [show q x = 1 from hx]; exact B.one_mem, hNV hx⟩
  have hAE : A ≤ normalizer (E : Set G) :=
    (le_inf (normalizes_preimage q hn) hAV).trans inf_normalizer_le_normalizer_inf
  have hmap : E.map q = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro b hb
      obtain ⟨v, hv, rfl⟩ := hB hb
      exact ⟨v, ⟨hb, hv⟩, rfl⟩
  rcases hirr E hNE inf_le_right hAE with he | he
  · left
    rw [← hmap, he]
    exact (map_eq_bot_iff q.ker).mpr le_rfl
  · right
    rw [← hmap, he]

variable [Finite G]

private theorem sylow_center_seed (T : Sylow 2 G) (V : Subgroup G)
    (hVT : V ≤ T) (hn : (T : Subgroup G) ≤ normalizer (V : Set G)) (hne : V ≠ ⊥) :
    ∃ Z : Subgroup G, Z ≠ ⊥ ∧ Z ≤ V ∧ Z ≤ centralizer (T : Set G) := by
  let E := V.subgroupOf (T : Subgroup G)
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hVT).mpr hn
  have hE : E ≠ ⊥ := by
    intro he
    have hh := congrArg (fun K : Subgroup (T : Subgroup G) => K.map (T : Subgroup G).subtype) he
    rw [map_subgroupOf_eq_of_le hVT, Subgroup.map_bot] at hh
    exact hne hh
  let Z := (center (T : Subgroup G) ⊓ E).map (T : Subgroup G).subtype
  refine ⟨Z, ?_, ?_, ?_⟩
  · exact fun he => center_inf_ne_bot_of_normal T.isPGroup' E hE
      ((map_eq_bot_iff_of_injective _ (T : Subgroup G).subtype_injective).mp he)
  · calc
      Z ≤ E.map (T : Subgroup G).subtype := map_mono inf_le_right
      _ = V := map_subgroupOf_eq_of_le hVT
  · rintro _ ⟨x, hx, rfl⟩ t ht
    exact congrArg Subtype.val ((mem_center_iff.mp hx.1) ⟨t, ht⟩)

private theorem normalClosure_reduced_of_sylow_center (T : Sylow 2 G)
    (Z : Subgroup G) (hZT : Z ≤ T) (hc : Z ≤ centralizer (T : Set G))
    (he : IsElementaryAbelian 2 (normalClosure (Z : Set G))) :
    IsPReduced 2 (normalClosure (Z : Set G)) := by
  let E := Z.subgroupOf (T : Subgroup G)
  have hEZ : E ≤ center (T : Subgroup G) := by
    intro z hz
    exact mem_center_iff.mpr fun t => Subtype.ext (hc hz t t.property)
  let : E.Normal := ⟨by
    intro z hz t
    have hc := (mem_center_iff.mp (hEZ hz)) t
    simpa only [hc, mul_inv_cancel_right] using hz⟩
  let := he
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le le_normalClosure
  have hE : IsPReduced 2 E := by
    refine ⟨inferInstance, IsElementaryAbelian.subgroupOf hZT, ?_⟩
    have hC : centralizer (E : Set (T : Subgroup G)) = ⊤ := by
      apply top_unique
      intro t _ z hz
      exact ((mem_center_iff.mp (hEZ hz)) t).symm
    apply bot_unique
    intro x _
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (centralizer (E : Set (T : Subgroup G))) x
    exact (QuotientGroup.eq_one_iff t).mpr (hC.symm ▸ mem_top t)
  have hh := hE.normalClosure_of_sylow_le T (T : Subgroup G) le_rfl E
  rw [map_subgroupOf_eq_of_le hZT] at hh
  exact hh he

/-- The quotient normal closure of an irreducible seed in characteristic two.
The kernel is contained in the elementary seed and is normal in the whole group. -/
public theorem isPReduced_normalClosure_image_of_irreducible {K : Type*} [Group K] [Finite K]
    (q : G →* K) (hq : Function.Surjective q) (V A : Subgroup G) (T : Sylow 2 G)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (he : IsElementaryAbelian 2 V) (hNV : q.ker ≤ V) (hne : q.ker ≠ V)
    (hVT : V ≤ T) (hTA : (T : Subgroup G) ≤ A)
    (hAV : A ≤ normalizer (V : Set G))
    (hirr : ∀ E : Subgroup G, q.ker ≤ E → E ≤ V → A ≤ normalizer (E : Set G) →
      E = q.ker ∨ E = V) :
    let W := normalClosure (V.map q : Set K)
    IsPReduced 2 W := by
  let V' := V.map q
  let A' := A.map q
  let T' := T.mapSurjective hq
  let Q := pCore 2 K
  let C := centralizer (q.ker : Set G)
  let C' := C.map q
  let := he
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.map q
  have hVC : V ≤ C := by
    intro v hv n hn
    exact congrArg Subtype.val (mul_comm (⟨n, hNV hn⟩ : V) ⟨v, hv⟩)
  have hCchar : centralizer (pCore 2 C' : Set C') ≤ pCore 2 C' := by
    apply (q.subgroupMap C).centralizer_pCore_le_of_surjective_centralKernel
      (q.subgroupMap_surjective C)
    · intro x hx
      have hxN : x.val ∈ q.ker := congrArg Subtype.val hx
      apply mem_center_iff.mpr
      intro c
      exact Subtype.ext ((c.property x hxN).symm)
    · exact normal_core_selfCentralizing hchar C
  let : C'.Normal := Normal.map inferInstance q hq
  have hCcore : C'.pCoreIn 2 ≤ Q :=
    le_sSup ⟨by change ((pCore 2 C').map C'.subtype).Normal; infer_instance,
      isPGroup_pCoreIn 2 C'⟩
  have hQT : Q ≤ T' := pCore_isPGroup.le_sylow_of_normal T'
  have hV'T : V' ≤ T' := map_mono hVT
  have hT'A : (T' : Subgroup K) ≤ A' := map_mono hTA
  have hA'V : A' ≤ normalizer (V' : Set K) := normalizes_image q hAV
  have hVne : V' ≠ ⊥ := by
    intro hbot
    have hvn : V ≤ q.ker := (map_eq_bot_iff V).mp hbot
    exact hne (le_antisymm hNV hvn)
  obtain ⟨Z, hZne, hZV, hZcent⟩ := sylow_center_seed T' V' hV'T (hT'A.trans hA'V) hVne
  have hZQ : Z ≤ Q := by
    intro z hz
    have hzC : z ∈ C' := map_mono hVC (hZV hz)
    apply hCcore
    refine mem_map.mpr ⟨⟨z, hzC⟩, hCchar ?_, rfl⟩
    intro c hc
    exact Subtype.ext (hZcent hz c (hQT (hCcore (mem_map_of_mem C'.subtype hc))))
  have hmin := minimal_image q V A hNV hAV hirr
  have hVQ : V' ≤ Q := by
    have hn : A' ≤ normalizer (V' ⊓ Q : Set K) :=
      (le_inf hA'V le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
    rcases hmin (V' ⊓ Q) inf_le_left hn with hh | hh
    · exact False.elim (hZne (bot_unique (hh ▸ le_inf hZV hZQ)))
    · exact hh.symm.le.trans inf_le_right
  have hVA : V' ≤ A' := hV'T.trans hT'A
  have hQA : Q ≤ A' := hQT.trans hT'A
  have hQcore : Q ≤ A'.pCoreIn 2 :=
    le_pCoreIn_of_normalizes pCore_isPGroup hQA le_normalizer_of_normal
  have hVcentral : V' ≤ centralizer (Q : Set K) :=
    le_centralizer_iff.mp (hQcore.trans
      (pCoreIn_le_centralizer_of_irreducible V' A' A'
        (IsElementaryAbelian.isPGroup 2 V') hVA hA'V le_rfl hmin))
  let W := normalClosure (V' : Set K)
  have hWQ : W ≤ Q := normalClosure_le_normal hVQ
  have hWcent : W ≤ centralizer (Q : Set K) := normalClosure_le_normal hVcentral
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp
    (hWcent.trans (centralizer_le hWQ))
  have hWe : IsElementaryAbelian 2 W := IsElementaryAbelian.normalClosure_of_isMulCommutative V'
  have hgen : normalClosure (Z : Set K) = W := by
    apply le_antisymm (normalClosure_le_normal (hZV.trans le_normalClosure))
    apply normalClosure_le_normal
    have hn : A' ≤ normalizer (V' ⊓ normalClosure (Z : Set K) : Set K) :=
      (le_inf hA'V le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
    rcases hmin (V' ⊓ normalClosure (Z : Set K)) inf_le_left hn with hh | hh
    · exact False.elim (hZne (bot_unique (hh ▸ le_inf hZV le_normalClosure)))
    · exact hh.symm.le.trans inf_le_right
  change IsPReduced 2 W
  rw [← hgen] at hWe ⊢
  exact normalClosure_reduced_of_sylow_center T' Z (hZV.trans hV'T) hZcent hWe
end Theory.GroupTheory
