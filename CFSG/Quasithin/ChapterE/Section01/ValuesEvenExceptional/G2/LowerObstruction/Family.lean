module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.GroupTheory.ConjugacyFamilySpan
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The highest-root family for the lower G₂ calculation

Embed the actual highest-root group through a model equivalence and take its
orbit under the whole ambient group. Its members are elementary of order q,
and lie in the normal socle. After Sylow alignment its weak closure is
nontrivial, lies in the socle, and has proper normalizer when the socle is
simple. These facts include ambient outer automorphisms.

This constructs a candidate family for Aschbacher--Smith E.1.14(1), printed
p.214, citing Asc82a Lemma 4.7. It does not prove confinement of E-members.
The root coordinates and Sylow center identification come from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G F : Type*} [Group G] [Field F]

/-- Embed the full octonion model in its specified ambient copy. -/
def modelEmbedding (L : Subgroup G) (e : L ≃* Model F) : Model F →* G :=
  L.subtype.comp e.symm.toMonoidHom

theorem modelEmbedding_injective (L : Subgroup G) (e : L ≃* Model F) :
    Function.Injective (modelEmbedding L e) := L.subtype_injective.comp e.symm.injective

/-- The embedded additive highest-root group. -/
def root (L : Subgroup G) (e : L ≃* Model F) : Subgroup G :=
  highestRoot.map (modelEmbedding L e)

/-- All conjugates under G, including conjugation outside the socle. -/
def family (L : Subgroup G) (e : L ≃* Model F) : Set (Subgroup G) :=
  Set.range (fun g : G => (root L e).map (MulAut.conj g).toMonoidHom)

/-- The expected trapping parabolic; its confinement properties are separate. -/
def shortOvergroup (L T : Subgroup G) (e : L ≃* Model F) : Subgroup G :=
  parabolic₁.map (modelEmbedding L e) ⊔ T

theorem root_le_socle (L : Subgroup G) (e : L ≃* Model F) : root L e ≤ L := by
  rintro _ ⟨x, _, rfl⟩
  exact (e.symm x).property

theorem root_mem_family (L : Subgroup G) (e : L ≃* Model F) :
    root L e ∈ family L e := by
  refine ⟨1, ?_⟩
  simp only [map_one]
  exact Subgroup.map_id _

theorem family_conjugationInvariant (L : Subgroup G) (e : L ≃* Model F) :
    SubgroupFamily.ConjugationInvariant (family L e) := by
  rintro A ⟨g, rfl⟩ h
  refine ⟨h * g, ?_⟩
  rw [map_map]
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem family_le_socle (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {A : Subgroup G} (hA : A ∈ family L e) : A ≤ L := by
  obtain ⟨g, rfl⟩ := hA
  rintro _ ⟨a, ha, rfl⟩
  exact (inferInstance : L.Normal).conj_mem a (root_le_socle L e ha) g

private theorem highestRoot_elementary [CharP F 2] :
    IsElementaryAbelian 2 (highestRoot (F := F)) where
  toIsMulCommutative := ⟨⟨fun x y => highestRootEquiv.symm.injective (by
    simp only [map_mul, mul_comm])⟩⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply highestRootEquiv.symm.injective
    rw [map_pow, map_one, pow_two]
    apply Multiplicative.toAdd.injective
    exact CharTwo.add_self_eq_zero _

theorem family_elementary [CharP F 2] (L : Subgroup G) (e : L ≃* Model F) :
    IsElementaryFamily (family L e) := by
  constructor
  · rintro A ⟨g, rfl⟩
    let := highestRoot_elementary (F := F)
    let : IsElementaryAbelian 2 (root L e) := IsElementaryAbelian.map (modelEmbedding L e)
    exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  · intro g A hA
    exact family_conjugationInvariant L e A hA g

theorem card_root (L : Subgroup G) (e : L ≃* Model F) :
    Nat.card (root L e) = Nat.card F := by
  rw [root, card_map_of_injective (modelEmbedding_injective L e), card_highestRoot]

theorem card_family_member (L : Subgroup G) (e : L ≃* Model F)
    {A : Subgroup G} (hA : A ∈ family L e) : Nat.card A = Nat.card F := by
  obtain ⟨g, rfl⟩ := hA
  rw [card_map_of_injective (MulAut.conj g).injective, card_root]

theorem root_le_of_aligned (L T : Subgroup G) (e : L ≃* Model F)
    (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) : root L e ≤ T := by
  rintro _ ⟨x, hx, rfl⟩
  have hu : x ∈ unipotent := by
    obtain ⟨a, rfl⟩ := hx
    exact (fiveRootSubgroup_le_unipotent _ _) (rootA_mem_radical₁ _)
  rw [← he] at hu
  obtain ⟨y, hy, hyx⟩ := hu
  change (e.symm x : G) ∈ T
  simpa only [← hyx, MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using (show (y : G) ∈ T from hy)

theorem weakClosure_le_socle (L T : Subgroup G) [L.Normal] (e : L ≃* Model F) :
    weakClosure T (family L e) ≤ L :=
  sSup_le fun _ hA => family_le_socle L e hA.1

theorem root_le_weakClosure (L T : Subgroup G) (e : L ≃* Model F)
    (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) :
    root L e ≤ weakClosure T (family L e) :=
  le_sSup ⟨root_mem_family L e, root_le_of_aligned L T e he⟩

theorem weakClosure_ne_bot (L T : Subgroup G) (e : L ≃* Model F)
    (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) (hq : 1 < Nat.card F) :
    weakClosure T (family L e) ≠ ⊥ := by
  intro h
  have hr : root L e = ⊥ := bot_unique (h ▸ root_le_weakClosure L T e he)
  have hc := card_root L e
  rw [hr, Subgroup.card_bot] at hc
  omega

theorem le_weakClosure_normalizer [Finite G] (L T : Subgroup G)
    (e : L ≃* Model F) :
    T ≤ normalizer (weakClosure T (family L e) : Set G) :=
  T.le_normalizer.trans (SubgroupFamily.normalizer_le_span_normalizer
    (family_conjugationInvariant L e) T)

private theorem unipotent_ne_top [Finite F] (hq : 1 < Nat.card F) :
    unipotent (K := F) ≠ ⊤ := by
  intro h
  have hi := unipotent_index (F := F)
  rw [h, Subgroup.index_top] at hi
  have h2 : 4 ≤ Nat.card F ^ 2 := by nlinarith
  have h6 : 64 ≤ Nat.card F ^ 6 := by
    have := Nat.pow_le_pow_left (show 2 ≤ Nat.card F by omega) 6
    norm_num at this ⊢
    exact this
  have h6' : 63 ≤ Nat.card F ^ 6 - 1 := by omega
  have h2' : 3 ≤ Nat.card F ^ 2 - 1 := by omega
  nlinarith

/-- Simplicity makes the normalizer proper without assuming any confinement
or any failure of E-generation. -/
theorem weakClosure_normalizer_ne_top [Finite F] (L T : Subgroup G)
    [L.Normal] [IsSimpleGroup L] (e : L ≃* Model F)
    (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) (hq : 1 < Nat.card F) :
    normalizer (weakClosure T (family L e) : Set G) ≠ ⊤ := by
  intro hn
  let W := weakClosure T (family L e)
  have hWL : W ≤ L := weakClosure_le_socle L T e
  have hW : W ≠ ⊥ := weakClosure_ne_bot L T e he hq
  let : W.Normal := normalizer_eq_top_iff.mp hn
  rcases (inferInstance : (W.subgroupOf L).Normal).eq_bot_or_eq_top with hb | ht
  · apply hW
    have hm := congrArg (Subgroup.map L.subtype) hb
    simpa only [map_subgroupOf_eq_of_le hWL, Subgroup.map_bot] using hm
  · have hLT : L ≤ T := (subgroupOf_eq_top.mp ht).trans (weakClosure_le T _)
    have htop : T.subgroupOf L = ⊤ := subgroupOf_eq_top.mpr hLT
    apply unipotent_ne_top hq
    rw [← he, htop, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]

variable [Finite G] [Finite F] [CharP F 2]

/-- Sylow conjugacy aligns an actual full-model equivalence with T intersect L. -/
theorem exists_aligned_equiv (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (e : L ≃* Model F) :
    ∃ a : L ≃* Model F, ((T : Subgroup G).subgroupOf L).map a.toMonoidHom =
      unipotent := by
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal L
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) Q' (sylow (F := F))
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hm := congrArg Sylow.toSubgroup hg
  change ((Q : Subgroup L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hm
  rw [hQ, map_map, sylow_coe] at hm
  exact hm

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction
