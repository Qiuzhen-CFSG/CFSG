module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.GroupTheory.AutomorphismTowerSimple
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsImageIntersectionsNative

/-!
# Intersections of the original Higman--Sims automorphism images

An elementary automorphism group of order 32 has an inner part of order 16:
the outer group has order at most two, while the intrinsic two-rank is four.
Purity identifies this inner part with the marked sixteen-subgroup. Its full
automorphism centralizer has order 32, so it is the entire given image.

If two images have intersection of order greater than four, the common inner
part contains a nonidentity element. The two markings can be chosen to send
that same element to the marked involution. Their relative automorphism fixes
the marked involution, and the native ten-orbit certificate gives equality
or intersection of order at most four.

The public conclusion assumes only elementary images, their orders, and the
original fixed-letter purity. All finite native inputs are proved in the
imported carrier certificate; no closure or intersection hypothesis is added.
Source: Aschbacher--Smith 12.6.12, printed pp.825--826.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsImageIntersections
open Sporadic.LeechRelated.HS

private theorem inner_injective : Function.Injective (MulAut.conj : Carrier →* MulAut Carrier) :=
  MulAut.conj_injective_of_center_eq_bot BlockNormalizer.center_carrier_eq_bot

private theorem card_le_twice_inner (E : Subgroup (MulAut Carrier)) :
    Nat.card E ≤ 2 * Nat.card (E.comap (MulAut.conj : Carrier →* MulAut Carrier)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup Carrier)
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map E q
  have hm : Nat.card (E.map q) ≤ 2 :=
    (Subgroup.card_le_card_group (E.map q)).trans
      (Nat.le_of_dvd (by decide) outer_card_dvd_two)
  have hi : Nat.card (E.comap (MulAut.conj : Carrier →* MulAut Carrier)) =
      Nat.card (E ⊓ MulAut.innerSubgroup Carrier : Subgroup (MulAut Carrier)) := by
    rw [←card_map_of_injective inner_injective,map_comap_eq]
    rw [inf_comm]
  rw [QuotientGroup.ker_mk'] at hprod
  rw [hi]
  nlinarith

private theorem inner_card_sixteen (E : Subgroup (MulAut Carrier))
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 32) :
    Nat.card (E.comap (MulAut.conj : Carrier →* MulAut Carrier)) = 16 := by
  let := IsElementaryAbelian.comap_of_injective (p := 2) (MulAut.conj : Carrier →* MulAut Carrier)
    inner_injective E
  have hb := (primeRank_le_iff_elementary_card_le Carrier).mp twoRank_le_four
    (E.comap (MulAut.conj : Carrier →* MulAut Carrier)) inferInstance
  have hl := card_le_twice_inner E
  rw [hE] at hl
  change Nat.card (E.comap (MulAut.conj : Carrier →* MulAut Carrier)) ≤ 16 at hb
  omega

private theorem inner_map_transport (W : Subgroup Carrier) (α : MulAut Carrier) :
    (W.map α.toMonoidHom).map (MulAut.conj : Carrier →* MulAut Carrier) =
      (W.map (MulAut.conj : Carrier →* MulAut Carrier)).map
        (MulAut.conj α).toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x y
  simp

private theorem automorphism_conj_mul (E : Subgroup (MulAut Carrier))
    (α β : MulAut Carrier) :
    (E.map (MulAut.conj β).toMonoidHom).map (MulAut.conj α).toMonoidHom =
      E.map (MulAut.conj (α * β)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem mark_at_point
    (E : Subgroup (MulAut Carrier)) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (M : Subgroup Carrier)
    (hM : Nat.card (centralizer (M.map (MulAut.conj : Carrier →* MulAut Carrier) :
      Set (MulAut Carrier))) = 32)
    (hconj : ∃ g : Carrier,
      (E.comap (MulAut.conj : Carrier →* MulAut Carrier)).map
        (MulAut.conj g).toMonoidHom = M)
    (z : Carrier)
    (htrans : ∀ y ∈ M, y ≠ 1 → ∃ g : Carrier,
      g ∈ normalizer (M : Set Carrier) ∧ (MulAut.conj g) y = z)
    (x : Carrier) (hx : MulAut.conj x ∈ E) (hne : x ≠ 1) :
    ∃ α : MulAut Carrier,
      E.map (MulAut.conj α).toMonoidHom =
        centralizer (M.map (MulAut.conj : Carrier →* MulAut Carrier) : Set (MulAut Carrier)) ∧
      α x = z := by
  let W := E.comap (MulAut.conj : Carrier →* MulAut Carrier)
  obtain ⟨g,hg⟩ := hconj
  have hxM : (MulAut.conj g) x ∈ M := hg ▸ mem_map_of_mem _ hx
  have hxne : (MulAut.conj g) x ≠ 1 := by
    intro he
    exact hne ((MulAut.conj g).injective (he.trans (map_one (MulAut.conj g)).symm))
  obtain ⟨k,hk,hkx⟩ := htrans _ hxM hxne
  let α : MulAut Carrier := MulAut.conj k * MulAut.conj g
  have hWM : W.map α.toMonoidHom = M := by
    change W.map ((MulAut.conj k).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = M
    rw [←Subgroup.map_map,hg]
    exact mem_normalizer_iff_map_conj_eq.mp hk
  have hinner : M.map (MulAut.conj : Carrier →* MulAut Carrier) =
      (W.map (MulAut.conj : Carrier →* MulAut Carrier)).map
        (MulAut.conj α).toMonoidHom := by
    rw [←hWM]
    exact inner_map_transport W α
  refine ⟨α,eq_of_le_of_card_ge ?_ ?_,hkx⟩
  · rintro _ ⟨a,ha,rfl⟩ b hb
    rw [hinner] at hb
    obtain ⟨_,⟨y,hy,rfl⟩,rfl⟩ := hb
    have hc : MulAut.conj y * a = a * MulAut.conj y :=
      congrArg Subtype.val (mul_comm (⟨MulAut.conj y,hy⟩ : E) ⟨a,ha⟩)
    simpa only [map_mul] using congrArg (MulAut.conj α).toMonoidHom hc
  · rw [hM,card_map_of_injective (MulAut.conj α).injective,hE]

private theorem common_inner_point (E F : Subgroup (MulAut Carrier))
    (hlarge : 4 < Nat.card (E ⊓ F : Subgroup (MulAut Carrier))) :
    ∃ x : Carrier, x ≠ 1 ∧ MulAut.conj x ∈ E ∧ MulAut.conj x ∈ F := by
  let W := (E ⊓ F).comap (MulAut.conj : Carrier →* MulAut Carrier)
  have hW : W ≠ ⊥ := by
    intro he
    have hh := card_le_twice_inner (E ⊓ F)
    change Nat.card (E ⊓ F : Subgroup (MulAut Carrier)) ≤ 2 * Nat.card W at hh
    rw [he] at hh
    simp only [Subgroup.card_bot,mul_one] at hh
    omega
  obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  exact ⟨x,fun he => hx (Subtype.ext he),x.property.1,x.property.2⟩

private theorem overlap_assembly
    (E F : Subgroup (MulAut Carrier)) [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 32) (hF : Nat.card F = 32)
    (M : Subgroup Carrier)
    (hM : Nat.card (centralizer (M.map (MulAut.conj : Carrier →* MulAut Carrier) :
      Set (MulAut Carrier))) = 32)
    (hconjE : ∃ g : Carrier,
      (E.comap (MulAut.conj : Carrier →* MulAut Carrier)).map
        (MulAut.conj g).toMonoidHom = M)
    (hconjF : ∃ g : Carrier,
      (F.comap (MulAut.conj : Carrier →* MulAut Carrier)).map
        (MulAut.conj g).toMonoidHom = M)
    (z : Carrier)
    (htrans : ∀ y ∈ M, y ≠ 1 → ∃ g : Carrier,
      g ∈ normalizer (M : Set Carrier) ∧ (MulAut.conj g) y = z)
    (hlocal : let A := centralizer (M.map (MulAut.conj : Carrier →* MulAut Carrier) :
      Set (MulAut Carrier))
      ∀ α : MulAut Carrier, α z = z →
        A = A.map (MulAut.conj α).toMonoidHom ∨
          Nat.card (A ⊓ A.map (MulAut.conj α).toMonoidHom : Subgroup (MulAut Carrier)) ≤ 4) :
    E = F ∨ Nat.card (E ⊓ F : Subgroup (MulAut Carrier)) ≤ 4 := by
  by_cases hb : Nat.card (E ⊓ F : Subgroup (MulAut Carrier)) ≤ 4
  · exact .inr hb
  have hlarge : 4 < Nat.card (E ⊓ F : Subgroup (MulAut Carrier)) := by omega
  obtain ⟨x,hx,hxE,hxF⟩ := common_inner_point E F hlarge
  obtain ⟨α,hα,hαx⟩ := mark_at_point E hE M hM hconjE z htrans x hxE hx
  obtain ⟨β,hβ,hβx⟩ := mark_at_point F hF M hM hconjF z htrans x hxF hx
  let A := centralizer (M.map (MulAut.conj : Carrier →* MulAut Carrier) : Set (MulAut Carrier))
  let δ : MulAut Carrier := α * β⁻¹
  have hδ : δ z = z := by
    change α (β.symm z) = z
    calc
      α (β.symm z) = α (β.symm (β x)) := congrArg (fun t => α (β.symm t)) hβx.symm
      _ = α x := congrArg α (β.symm_apply_apply x)
      _ = z := hαx
  have hδβ : δ * β = α := by simp [δ]
  have hrel : A.map (MulAut.conj δ).toMonoidHom = F.map (MulAut.conj α).toMonoidHom := by
    change (centralizer (M.map (MulAut.conj : Carrier →* MulAut Carrier) : Set (MulAut Carrier))).map _ = _
    rw [←hβ,automorphism_conj_mul,hδβ]
  rcases hlocal δ hδ with he | he
  · left
    apply Subgroup.map_injective (f := (MulAut.conj α).toMonoidHom) (MulAut.conj α).injective
    exact hα.trans (he.trans hrel)
  · rw [hrel,←hα,←Subgroup.map_inf _ _ _ (MulAut.conj α).injective,
      card_map_of_injective (MulAut.conj α).injective] at he
    exact (hb he).elim

private theorem fixed_letter_transport (α : MulAut Carrier) (x : Carrier)
    (hx : ∃ p : Fin 100, (x : Equiv.Perm (Fin 100)) p = p) :
    ∃ p : Fin 100, (α x : Equiv.Perm (Fin 100)) p = p := by
  obtain ⟨n,rfl⟩ := normalizer_surjective_of_pointStabilizer_map pointStabilizer_map α
  obtain ⟨p,hp⟩ := hx
  refine ⟨n.val p,?_⟩
  rw [normalizerMonoidHom_apply_apply_coe]
  simp only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply,hp]

/-- The original fixed-letter purity is preserved by every abstract
automorphism conjugating the image subgroup. -/
theorem purity_conjugate
    (E : Subgroup (MulAut Carrier)) (α : MulAut Carrier)
    (hp : ∀ x : Carrier, MulAut.conj x ∈ E →
      ∃ p : Fin 100, (x : Equiv.Perm (Fin 100)) p = p) :
    ∀ x : Carrier, MulAut.conj x ∈ E.map (MulAut.conj α).toMonoidHom →
      ∃ p : Fin 100, (x : Equiv.Perm (Fin 100)) p = p := by
  intro x hx
  obtain ⟨a,ha,he⟩ := hx
  have heq : a = MulAut.conj (α.symm x) := by
    apply (MulAut.conj α).injective
    calc
      (MulAut.conj α) a = MulAut.conj x := he
      _ = (MulAut.conj α) (MulAut.conj (α.symm x)) := by ext y; simp
  have hh := fixed_letter_transport α (α.symm x) (hp _ (heq ▸ ha))
  simpa only [α.apply_symm_apply] using hh

/-- Distinct pure elementary images of order 32 in the full automorphism
group of the original degree-100 HS carrier meet in order at most four. -/
theorem pure_elementary_thirty_two_intersection
    (E F : Subgroup (MulAut Carrier))
    (heE : IsElementaryAbelian 2 E) (heF : IsElementaryAbelian 2 F)
    (hE : Nat.card E = 32) (hF : Nat.card F = 32)
    (hpE : ∀ x : Carrier, MulAut.conj x ∈ E →
      ∃ p : Fin 100, (x : Equiv.Perm (Fin 100)) p = p)
    (hpF : ∀ x : Carrier, MulAut.conj x ∈ F →
      ∃ p : Fin 100, (x : Equiv.Perm (Fin 100)) p = p) :
    E = F ∨ Nat.card (E ⊓ F : Subgroup (MulAut Carrier)) ≤ 4 := by
  let := heE
  let := heF
  let WE := E.comap (MulAut.conj : Carrier →* MulAut Carrier)
  let WF := F.comap (MulAut.conj : Carrier →* MulAut Carrier)
  have heWE : IsElementaryAbelian 2 WE :=
    IsElementaryAbelian.comap_of_injective _ inner_injective E
  have heWF : IsElementaryAbelian 2 WF :=
    IsElementaryAbelian.comap_of_injective _ inner_injective F
  have hcE := OriginalHigmanSimsImageIntersectionsNative.pure_sixteen_conjugate
    WE heWE (inner_card_sixteen E hE) hpE
  have hcF := OriginalHigmanSimsImageIntersectionsNative.pure_sixteen_conjugate
    WF heWF (inner_card_sixteen F hF) hpF
  exact overlap_assembly E F hE hF
    OriginalHigmanSimsImageIntersectionsNative.markedW
    OriginalHigmanSimsImageIntersectionsNative.markedE_card hcE hcF
    EvenLocalCandidates.e0
    OriginalHigmanSimsImageIntersectionsNative.markedW_point_transitive
    OriginalHigmanSimsImageIntersectionsNative.markedE_conjugate_overlap

/-- The original pure image and any of its abstract automorphism conjugates
are equal or meet in order at most four; purity is required only initially. -/
theorem pure_elementary_thirty_two_conjugate_intersection
    (E : Subgroup (MulAut Carrier)) (α : MulAut Carrier)
    (he : IsElementaryAbelian 2 E) (hc : Nat.card E = 32)
    (hp : ∀ x : Carrier, MulAut.conj x ∈ E →
      ∃ p : Fin 100, (x : Equiv.Perm (Fin 100)) p = p) :
    E = E.map (MulAut.conj α).toMonoidHom ∨
      Nat.card (E ⊓ E.map (MulAut.conj α).toMonoidHom : Subgroup (MulAut Carrier)) ≤ 4 := by
  let := he
  exact pure_elementary_thirty_two_intersection E (E.map (MulAut.conj α).toMonoidHom)
    he (IsElementaryAbelian.map _) hc
    ((card_map_of_injective (MulAut.conj α).injective).trans hc) hp (purity_conjugate E α hp)

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsImageIntersections
