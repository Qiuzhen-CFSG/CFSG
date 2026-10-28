module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MaximalNormalizer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalChiefBound
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# The actual maximal normalizer satisfies Goldschmidt’s local chief bound

The edge normalizer is a Sylow two-subgroup of index three in the first
local normalizer. The proved characteristic-normal exclusion makes that
Sylow nonnormal, so its quotient by the two-core is S₃. We transport the
exclusion along the literal subgroup inclusions and apply the proved local
residual classification. Thus no local S₃ identification, pushing-up input,
or chief-factor bound is an additional hypothesis of the source application.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.3),
printed p.395, first paragraph, using the local result (2.14).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem edgeNormalizer_relIndex_local (Q : Subgroup G) (i : Bool) :
    (edgeNormalizer F Q).relIndex (localNormalizer F Q i) =
      (F false ⊓ F true).relIndex (localNormalizer F Q i) := by
  have he : (edgeNormalizer F Q).subgroupOf (localNormalizer F Q i) =
      (F false ⊓ F true).subgroupOf (localNormalizer F Q i) := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.property.1, hx⟩⟩
  exact congrArg Subgroup.index he

private theorem characteristic_map_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (D : Subgroup H) [D.Characteristic] :
    (D.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply _

/-- The actual edge Sylow, its S₃ quotient, and the original local
characteristic-normal hypothesis are all supplied by maximality. -/
theorem MaximalNormalizerCandidate.local_pushingUp_input
    (h : CubicTreeAction F) {Q : Subgroup G} (hQ : MaximalNormalizerCandidate F Q) :
    ∃ P : Sylow 2 (localNormalizer F Q false),
      (P : Subgroup (localNormalizer F Q false)) =
        (edgeNormalizer F Q).subgroupOf (localNormalizer F Q false) ∧
      Nonempty (((localNormalizer F Q false) ⧸ pCore 2 (localNormalizer F Q false)) ≃*
        Equiv.Perm (Fin 3)) ∧
      ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (P : Subgroup (localNormalizer F Q false)).subtype).Normal := by
  let E := edgeNormalizer F Q
  let L := localNormalizer F Q false
  let EP := E.subgroupOf L
  let : Finite L := h.finite_localNormalizer Q false
  have hEL : E ≤ L := edgeNormalizer_le_local Q false
  have hi : EP.index = 3 := by
    change E.relIndex L = 3
    rw [edgeNormalizer_relIndex_local]
    exact hQ.left_index
  have hpE : IsPGroup 2 E := h.primitive.sylow.isPGroup.to_le inf_le_right
  have hpEP : IsPGroup 2 EP := hpE.comap_subtype
  let P : Sylow 2 L := hpEP.toSylow (by rw [hi]; decide)
  have hn : ¬ EP.Normal := by
    intro hn
    let : EP.Normal := hn
    let : (E.subgroupOf E).Characteristic := by
      rw [Subgroup.subgroupOf_self]
      infer_instance
    have he := hQ.characteristic_normal_eq_bot h E le_rfl
    exact hQ.nontrivial (bot_unique (he ▸ hQ.le_edge))
  have hproper : pCore 2 L < (P : Subgroup L) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) ?_
    intro he
    apply hn
    change (P : Subgroup L).Normal
    rw [← he]
    infer_instance
  refine ⟨P, rfl, sylow_index_three_core_quotient P hi hproper, ?_⟩
  intro K hK hKne hKn
  let : K.Characteristic := hK
  let f : P →* G := L.subtype.comp (P : Subgroup L).subtype
  let H := K.map f
  have hHE : H ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact x.property
  let e : P ≃* E := subgroupOfEquivOfLe hEL
  have he : H.subgroupOf E = K.map e.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      exact ⟨y, hy, Subtype.ext heq⟩
    · rintro ⟨y, hy, heq⟩
      exact ⟨y, hy, congrArg Subtype.val heq⟩
  let : (H.subgroupOf E).Characteristic :=
    he.symm ▸ characteristic_map_equiv e K
  have hHn : (H.subgroupOf L).Normal := by
    change (H.comap L.subtype).Normal
    have heH : H = (K.map (P : Subgroup L).subtype).map L.subtype := by
      rw [Subgroup.map_map]
    rw [heH, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    exact hKn
  let : (H.subgroupOf L).Normal := hHn
  have hH := hQ.characteristic_normal_eq_bot h H hHE
  exact hKne ((Subgroup.map_eq_bot_iff_of_injective K
    (L.subtype_injective.comp (P : Subgroup L).subtype_injective)).mp hH)

/-- Every complete chief series of the actual maximal local normalizer
has at most one noncentral binary factor. -/
theorem MaximalNormalizerCandidate.local_chief_count_le_one
    (h : CubicTreeAction F) {Q : Subgroup G} (hQ : MaximalNormalizerCandidate F Q)
    (s : NoncentralChiefRefinement.ChiefSeries (localNormalizer F Q false))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.noncentralTwoCount ≤ 1 := by
  let : Finite (localNormalizer F Q false) := h.finite_localNormalizer Q false
  obtain ⟨P, _, ⟨e⟩, hP⟩ := hQ.local_pushingUp_input h
  exact local_noncentralTwoCount_le_one e P hP s h0 h1

/-- The corresponding bound retains any supplied literal cubic subgroup. -/
theorem MaximalNormalizerCandidate.local_cubic_index_le_four
    (h : CubicTreeAction F) {Q : Subgroup G} (hQ : MaximalNormalizerCandidate F Q)
    (X : Subgroup (localNormalizer F Q false)) (hX : Nat.card X = 3) :
    (centralizer (X : Set (localNormalizer F Q false))).relIndex
      (pCore 2 (localNormalizer F Q false)) ≤ 4 := by
  let : Finite (localNormalizer F Q false) := h.finite_localNormalizer Q false
  obtain ⟨P, _, ⟨e⟩, hP⟩ := hQ.local_pushingUp_input h
  exact local_cubic_centralizer_relIndex_le_four e P hP X hX

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
