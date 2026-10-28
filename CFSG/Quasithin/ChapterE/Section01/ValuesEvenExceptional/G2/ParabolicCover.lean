module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.AtlasPort.LinearGroups.G2.DerivedParabolicGeneration
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicRecognition

/-!
# The two parabolic overgroups for E.1.14's derived G₂ case

An actual model equivalence embeds the restricted root parabolics in the
ambient group. Their joins with T generate G whenever L T = G, including
at q = 2. Sylow conjugacy aligns T intersect L with the restricted positive
roots. Every element of T then preserves both parabolics, by the intrinsic
Sylow characterization of their defining root groups. Consequently each
joined overgroup intersects L in exactly its original parabolic.

This supplies literal subgroups for E.1.12, not an E-generation assumption.
The binary application proves their E-generation separately by solvability;
for larger fields the local rank-one calculation is still required.

Source: Aschbacher--Smith, E.1.12 and E.1.14(1), printed p.214. The concrete
root calculations are reused from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.SylowParabolicRecognition
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2
variable {G F : Type*} [Group G] [Field F]

def derivedEmbedding (L : Subgroup G) (e : L ≃* commutator (Model F)) :
    commutator (Model F) →* G := L.subtype.comp e.symm.toMonoidHom

theorem derivedEmbedding_range (L : Subgroup G) (e : L ≃* commutator (Model F)) :
    (derivedEmbedding L e).range = L := by
  rw [derivedEmbedding, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
    ← MonoidHom.range_eq_map, L.range_subtype]

def ambientParabolic (L : Subgroup G) (e : L ≃* commutator (Model F)) (i : Fin 2) :
    Subgroup G := (rootParabolic i).map (derivedEmbedding L e)

def parabolicOvergroup (L T : Subgroup G) (e : L ≃* commutator (Model F))
    (i : Fin 2) : Subgroup G := ambientParabolic L e i ⊔ T

def parabolicOvergroups (L T : Subgroup G) (e : L ≃* commutator (Model F)) :
    Set (Subgroup G) := Set.range (parabolicOvergroup L T e)

theorem ambientParabolic_le (L : Subgroup G) (e : L ≃* commutator (Model F))
    (i : Fin 2) : ambientParabolic L e i ≤ L := by
  exact (map_le_range (H := rootParabolic i) (f := derivedEmbedding L e)).trans_eq
    (derivedEmbedding_range L e)

theorem le_parabolicOvergroup (L T : Subgroup G) (e : L ≃* commutator (Model F))
    (i : Fin 2) : T ≤ parabolicOvergroup L T e i := le_sup_right

theorem parabolicOvergroups_generate [Finite F] (L T : Subgroup G)
    (e : L ≃* commutator (Model F)) (hLT : L ⊔ T = ⊤) :
    sSup (parabolicOvergroups L T e) = ⊤ := by
  have hpair : rootParabolic (F := F) 0 ⊔ rootParabolic 1 = ⊤ := by
    apply map_injective (commutator (Model F)).subtype_injective
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype]
    change (parabolic₁.subgroupOf _).map _ ⊔ (parabolic₂.subgroupOf _).map _ = _
    rw [subgroupOf_map_subtype, subgroupOf_map_subtype]
    exact DerivedParabolicGeneration.restricted_parabolics_generate
  have hp : ambientParabolic L e 0 ⊔ ambientParabolic L e 1 = L := by
    rw [ambientParabolic, ambientParabolic, ← Subgroup.map_sup, hpair,
      ← MonoidHom.range_eq_map, derivedEmbedding_range]
  apply top_unique
  rw [← hLT]
  conv_lhs => rw [← hp]
  apply sup_le
  · exact sup_le
      (le_sup_left.trans (le_sSup (Set.mem_range_self (0 : Fin 2))))
      (le_sup_left.trans (le_sSup (Set.mem_range_self (1 : Fin 2))))
  · exact le_sup_right.trans (le_sSup (Set.mem_range_self (0 : Fin 2)))

variable [Finite G] [Finite F] [CharP F 2]

theorem exists_sylow_aligned_equiv (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* commutator (Model F)) :
    ∃ a : L ≃* commutator (Model F),
      ((T : Subgroup G).subgroupOf L).map a.toMonoidHom =
        unipotent.subgroupOf (commutator (Model F)) := by
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal L
  obtain ⟨P, hP⟩ := (sylow (F := F)).exists_subgroupOf_eq_of_normal
    (commutator (Model F))
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (commutator (Model F)) Q' P
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hm := congrArg Sylow.toSubgroup hg
  change ((Q : Subgroup L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hm
  rw [hQ, map_map, hP, sylow_coe] at hm
  exact hm

theorem sylow_normalizes_ambientParabolic (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    (T : Subgroup G) ≤ normalizer (ambientParabolic L e i : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  let b := MulAut.conjNormal (H := L) t
  let β : MulAut (commutator (Model F)) := (e.symm.trans b).trans e
  have transport (K : Subgroup L) :
      (K.map e.toMonoidHom).map β.toMonoidHom =
        (K.map b.toMonoidHom).map e.toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change e (b (e.symm (e x))) = e (b x)
    rw [e.symm_apply_apply]
  have hfixed : ((T : Subgroup G).subgroupOf L).map b.toMonoidHom =
      (T : Subgroup G).subgroupOf L := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact ((T : Subgroup G).le_normalizer ht (x : G)).mp hx
    · rw [card_map_of_injective (f := b.toMonoidHom) b.injective]
  have hU : (unipotent.subgroupOf (commutator (Model F))).map β.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F)) := by
    rw [← he, transport, hfixed]
  have hPi := rootParabolic_invariant β hU i
  have hcomp : (derivedEmbedding L e).comp β.toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp (derivedEmbedding L e) := by
    ext x
    change ((e.symm (e (b (e.symm x))) : L) : G) =
      t * ((e.symm x : L) : G) * t⁻¹
    rw [e.symm_apply_apply]
    rfl
  change ((rootParabolic i).map (derivedEmbedding L e)).map (MulAut.conj t).toMonoidHom = _
  rw [map_map, ← hcomp, ← map_map, hPi]
  rfl

omit [Finite G] [Finite F] [CharP F 2] in
theorem sylow_inf_le_ambientParabolic (L : Subgroup G) (T : Sylow 2 G)
    (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    (T : Subgroup G) ⊓ L ≤ ambientParabolic L e i := by
  intro x hx
  have hxU : e ⟨x, hx.2⟩ ∈ unipotent.subgroupOf (commutator (Model F)) :=
    he ▸ mem_map_of_mem _ hx.1
  have hxP : e ⟨x, hx.2⟩ ∈ rootParabolic i := by
    fin_cases i
    · exact ((show unipotent ≤ borel (K := F) from le_sup_left).trans borel_le_parabolic₁) hxU
    · exact ((show unipotent ≤ borel (K := F) from le_sup_left).trans borel_le_parabolic₂) hxU
  refine ⟨e ⟨x, hx.2⟩, hxP, ?_⟩
  change ((e.symm (e ⟨x, hx.2⟩) : L) : G) = x
  rw [e.symm_apply_apply]

theorem parabolicOvergroup_inf_socle (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    parabolicOvergroup L T e i ⊓ L = ambientParabolic L e i := by
  apply le_antisymm
  · intro x hx
    have hm : x ∈ (ambientParabolic L e i : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        (sylow_normalizes_ambientParabolic L T e he i)]
      exact hx.1
    obtain ⟨a, ha, t, ht, rfl⟩ := hm
    have htL : t ∈ L := by
      have h := L.mul_mem (L.inv_mem (ambientParabolic_le L e i ha)) hx.2
      simpa using h
    exact (ambientParabolic L e i).mul_mem ha
      (sylow_inf_le_ambientParabolic L T e he i ⟨ht, htL⟩)
  · exact le_inf le_sup_left (ambientParabolic_le L e i)
end CFSG.Quasithin.ChapterE.ExceptionalValues.G2
