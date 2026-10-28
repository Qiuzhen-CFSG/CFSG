module
public import Theory.SpecificGroups.G2Even.RadicalNormalizers
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelCommutator
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.SpecificGroups.Classical.QuinticRankOne

/-!
# Quintic actors normalized by a G₂ radical normalizer

In a five-free G₂ model an order-five actor preserving a two-radical fixes
an ambient Sylow subgroup inside its normalizer. That radical normalizer
contains the full Sylow normalizer. If the actor group has a two-group inner
intersection, every Borel displacement lies in the Sylow subgroup. This
contradicts the proved nontrivial-field Borel displacement bound. Alignment
and transport retain the actual radical, actor and component isomorphism.

Source application: Aschbacher--Smith 14.6.15, printed p.1035. The octonion
model and field action retain the imported ATLAS attribution in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.SpecificGroups.G2Quintic
open Atlas.G2 Atlas.G2.LieAutomorphismExtensions Atlas.G2.LieParabolicSetup
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem invariant_sylow
    {X : Type*} [Group X] [Finite X]
    (a : MulAut X) (ha : orderOf a = 5) (hX : ¬ 5 ∣ Nat.card X) :
    ∃ S : Sylow 2 X, (S : Subgroup X).map a.toMonoidHom = S := by
  let A := zpowers a
  have hA : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ha,pow_one])
  have hd : Nat.card (Sylow 2 X) ∣ Nat.card X :=
    (Sylow.card_dvd_index (Classical.choice (inferInstance : Nonempty (Sylow 2 X)))).trans
      (index_dvd_card _)
  obtain ⟨S,hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 X)
    (fun hh => hX (hh.trans hd))
  exact ⟨S,congrArg Sylow.toSubgroup (hS ⟨a,mem_zpowers a⟩)⟩

private theorem aut_normalizes_normalizer {X : Type*} [Group X]
    (Q : Subgroup X) (a : MulAut X) (hQ : Q.map a.toMonoidHom = Q) :
    (normalizer (Q : Set X)).map a.toMonoidHom = normalizer (Q : Set X) := by
  rw [map_equiv_normalizer_eq,hQ]

/-- An invariant two-radical in a five-free G₂ model supplies an invariant
ambient Sylow whose full normalizer stays inside the radical normalizer. -/
theorem invariant_sylow_in_radical_normalizer
    (Q : Subgroup (Model F)) (hQ : Q.IsPRadical 2)
    (a : MulAut (Model F)) (ha : orderOf a = 5)
    (hfix : Q.map a.toMonoidHom = Q) (hfive : ¬5 ∣ Nat.card (Model F)) :
    ∃ S : Sylow 2 (Model F), (S : Subgroup (Model F)).map a.toMonoidHom = S ∧
      normalizer (S : Set (Model F)) ≤ normalizer (Q : Set (Model F)) := by
  let N := normalizer (Q : Set (Model F))
  have hN := aut_normalizes_normalizer Q a hfix
  let b : MulAut N := (a.subgroupMap N).trans (MulEquiv.subgroupCongr hN)
  have hb5 : b^5=1 := by
    have hh : a^5=1 := ha ▸ pow_orderOf_eq_one a
    ext x : 1
    apply Subtype.ext
    exact congrArg (fun t : MulAut (Model F) => t x) hh
  have hbX : ¬5 ∣ Nat.card N := fun hd => hfive (hd.trans N.card_subgroup_dvd_card)
  have hs : ∃ P : Sylow 2 N, (P : Subgroup N).map b.toMonoidHom = P := by
    by_cases hb : b = 1
    · refine ⟨Classical.choice Sylow.nonempty,?_⟩
      rw [hb]
      exact map_id _
    · apply invariant_sylow b (orderOf_eq_prime (by simpa using hb5) hb) hbX
  obtain ⟨P,hP⟩ := hs
  obtain ⟨S,hPS⟩ := P.exists_comap_subtype_eq
  obtain ⟨S0,hS0⟩ := Atlas.G2.exists_sylow_normalizer_le_radical_normalizer Q hQ
  have hS0N : (S0 : Subgroup (Model F)) ≤ N := S0.toSubgroup.le_normalizer.trans hS0
  have hmap : (P : Subgroup N).map N.subtype = (S : Subgroup (Model F)) := by
    have hcard : Nat.card P = Nat.card S := by
      rw [Nat.card_congr (P.equiv (S0.subtype hS0N)).toEquiv]
      change Nat.card ((S0 : Subgroup (Model F)).subgroupOf N) = Nat.card S
      rw [Nat.card_congr (subgroupOfEquivOfLe hS0N).toEquiv,
        Nat.card_congr (S0.equiv S).toEquiv]
    apply eq_of_le_of_card_ge
    · rw [←hPS]; exact map_comap_le _ _
    · rw [card_map_of_injective N.subtype_injective,hcard]
  have hSN : (S : Subgroup (Model F)) ≤ N := hmap ▸ map_subtype_le _
  refine ⟨S,?_,Atlas.G2.sylow_normalizer_le_of_radical_normalizer_le Q hQ S N hSN le_rfl⟩
  rw [←hmap,map_map]
  have he : a.toMonoidHom.comp N.subtype = N.subtype.comp b.toMonoidHom := rfl
  rw [he,←map_map,hP]
/-- An outer actor fixing the standard Sylow cannot belong to an actor group
normalized by the Borel with a two-group inner intersection. -/
theorem no_outer_borel_actor (hq : 2 < Nat.card F)
    (A : Subgroup (MulAut (Model F)))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup (Model F) : Subgroup _))
    (hN : borel.map (MulAut.conj : Model F →* MulAut (Model F)) ≤ normalizer (A : Set _))
    (a : MulAut (Model F)) (ha : a ∈ A)
    (hfix : unipotent.map a.toMonoidHom = unipotent)
    (hout : a ∉ MulAut.innerSubgroup (Model F)) : False := by
  let D := (A ⊓ MulAut.innerSubgroup (Model F)).comap MulAut.conj
  have hD : IsPGroup 2 D := hi.comap_of_injective _
    (MulAut.conj_injective_of_center_eq_bot (model_center_eq_bot hq))
  have hbfix (b : zpowers a) : unipotent.map b.val.toMonoidHom = unipotent :=
    (zpowers_le.mpr hfix : zpowers a ≤ MulAction.stabilizer (MulAut (Model F)) unipotent) b.property
  have hbA (b : zpowers a) : b.val ∈ A := (zpowers_le.mpr ha) b.property
  have hd (b : zpowers a) (x : Model F) (hx : x ∈ borel) :
      x⁻¹ * b.val x ∈ unipotent := by
    have hn := hN (mem_map_of_mem MulAut.conj hx)
    have ha' : (MulAut.conj x)⁻¹ * b.val * MulAut.conj x ∈ A :=
      (mem_normalizer_iff.mp (inv_mem hn) b.val).mp (hbA b)
    have he : MulAut.conj (x⁻¹ * b.val x) =
        ((MulAut.conj x)⁻¹ * b.val * MulAut.conj x) * b.val⁻¹ := by
      ext y : 1
      change (x⁻¹ * b.val x) * y * (x⁻¹ * b.val x)⁻¹ =
        x⁻¹ * b.val (x * b.val.symm y * x⁻¹) * x
      simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
      group
    have hm : x⁻¹ * b.val x ∈ D :=
      ⟨he ▸ A.mul_mem ha' (A.inv_mem (hbA b)),⟨_,rfl⟩⟩
    have hb : borel.map b.val.toMonoidHom = borel := by
      rw [←Atlas.G2.SylowNormalizer.normalizer_unipotent]
      exact aut_normalizes_normalizer _ _ (hbfix b)
    have hx' : b.val x ∈ borel := hb ▸ mem_map_of_mem b.val.toMonoidHom hx
    have hh : x⁻¹ * b.val x ∈ D ⊓ normalizer (sylow (F := F) : Set (Model F)) :=
      ⟨hm,by
        change x⁻¹ * b.val x ∈ normalizer (unipotent (K := F) : Set (Model F))
        rw [Atlas.G2.SylowNormalizer.normalizer_unipotent]
        exact borel.mul_mem (borel.inv_mem hx) hx'⟩
    rw [hD.inf_normalizer_sylow sylow] at hh
    exact hh.2
  let C := commutatorSubgroup (zpowers a) (Model F) borel
  have hC : C ≤ unipotent := by
    apply (closure_le _).mpr
    rintro x ⟨b,y,hy,rfl⟩
    exact hd b y hy
  have hp : IsPGroup 2 C := unipotent_isTwoGroup.to_le hC
  have hc : pCore 2 C = ⊤ := top_unique (le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩)
  have hh := Atlas.G2.EvenBorelTorus.outer_commutator_quotient_gt_three
    (semilinearAction_surjective hq) a hfix hout
  change 3 < Nat.card (C ⧸ pCore 2 C) at hh
  rw [hc] at hh
  rw [←index_eq_card,index_top] at hh
  omega

/-- Transport the Borel obstruction along the supplied component and Sylow marking. -/
theorem no_outer_marked_sylow_actor
    {C : Type*} [Group C] [Finite C] (e : C ≃* Model F)
    (hq : 2 < Nat.card F) (S : Sylow 2 C)
    (hS : (S : Subgroup C).map e.toMonoidHom = unipotent)
    (A : Subgroup (MulAut C))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup C : Subgroup _))
    (hN : (normalizer (S : Set C)).map (MulAut.conj : C →* MulAut C) ≤
      normalizer (A : Set _))
    (a : MulAut C) (ha : a ∈ A)
    (hfix : (S : Subgroup C).map a.toMonoidHom = S)
    (hout : a ∉ MulAut.innerSubgroup C) : False := by
  let f := (MulAut.congr e).toMonoidHom
  let D := A.map f
  have hB : (normalizer (S : Set C)).map e.toMonoidHom = borel := by
    change (normalizer ((S : Subgroup C) : Set C)).map e.toMonoidHom = borel
    rw [map_equiv_normalizer_eq,hS,Atlas.G2.SylowNormalizer.normalizer_unipotent]
  have hiD : IsPGroup 2 (D ⊓ MulAut.innerSubgroup (Model F) : Subgroup _) := by
    have hh : (A ⊓ MulAut.innerSubgroup C).map f = D ⊓ MulAut.innerSubgroup (Model F) := by
      rw [map_inf _ _ f (MulAut.congr e).injective,MulAut.map_innerSubgroup_congr e]
    exact hh ▸ hi.map f
  have hND : (borel (K := F)).map (MulAut.conj : Model F →* MulAut (Model F)) ≤
      normalizer (D : Set (MulAut (Model F))) := by
    have hc : f.comp (MulAut.conj : C →* MulAut C) =
        (MulAut.conj : Model F →* MulAut (Model F)).comp e.toMonoidHom := by
      ext x : 1
      exact MulAut.congr_conj e x
    have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    rwa [map_map,hc,←map_map,hB] at hh
  have hfixD : unipotent.map (MulAut.congr e a).toMonoidHom = unipotent := by
    rw [←hS,map_map]
    have hc : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by
      ext x : 1
      change e (a (e.symm (e x))) = e (a x)
      rw [e.symm_apply_apply]
    rw [hc,←map_map,hfix]
  have houtD : MulAut.congr e a ∉ MulAut.innerSubgroup (Model F) := by
    rw [←MulAut.map_innerSubgroup_congr e]
    exact fun hh => hout ((mem_map_iff_mem (MulAut.congr e).injective).mp hh)
  exact no_outer_borel_actor hq D hiD hND _ (mem_map_of_mem f ha) hfixD houtD

/-- A quintic actor preserving a two-radical in five-free G₂ is incompatible
with normalization of its actor group by the full radical normalizer. -/
theorem no_radical_quintic_actor (hq : 2 < Nat.card F)
    (hfive : ¬5 ∣ Nat.card (Model F))
    (Q : Subgroup (Model F)) (hQ : Q.IsPRadical 2)
    (A : Subgroup (MulAut (Model F)))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup (Model F) : Subgroup _))
    (hN : (normalizer (Q : Set (Model F))).map MulAut.conj ≤ normalizer (A : Set _))
    (a : MulAut (Model F)) (ha : a ∈ A) (ha5 : orderOf a = 5)
    (hfix : Q.map a.toMonoidHom = Q) : False := by
  obtain ⟨S,hS,hSN⟩ := invariant_sylow_in_radical_normalizer Q hQ a ha5 hfix hfive
  obtain ⟨g,hg,_⟩ := Atlas.G2.EvenBorelTorus.sylow_normalizer_conjugate S
  let e := (MulAut.conj g).symm
  have he : (S : Subgroup (Model F)).map e.toMonoidHom = unipotent := by
    rw [←hg,map_map]
    have hc : e.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id (Model F) := by
      ext x : 1
      exact e.apply_symm_apply x
    rw [hc,map_id]
  exact no_outer_marked_sylow_actor e hq S he A hi ((map_mono hSN).trans hN) a ha hS
    (MulAut.prime_order_not_inner_of_not_dvd_card a ha5 hfive)

/-- The same radical obstruction on an isomorphic component, retaining the
specified radical and automorphism subgroup. -/
theorem no_radical_quintic_actor_of_equiv
    {C : Type*} [Group C] [Finite C] (e : C ≃* Model F)
    (hq : 2 < Nat.card F) (hfive : ¬5 ∣ Nat.card (Model F))
    (Q : Subgroup C) (hQ : Q.IsPRadical 2) (A : Subgroup (MulAut C))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup C : Subgroup _))
    (hN : (normalizer (Q : Set C)).map MulAut.conj ≤ normalizer (A : Set _))
    (a : MulAut C) (ha : a ∈ A) (ha5 : orderOf a = 5)
    (hfix : Q.map a.toMonoidHom = Q) : False := by
  let f := (MulAut.congr e).toMonoidHom
  let D := A.map f
  have hiD : IsPGroup 2 (D ⊓ MulAut.innerSubgroup (Model F) : Subgroup _) := by
    have hh : (A ⊓ MulAut.innerSubgroup C).map f = D ⊓ MulAut.innerSubgroup (Model F) := by
      rw [map_inf _ _ f (MulAut.congr e).injective,MulAut.map_innerSubgroup_congr e]
    exact hh ▸ hi.map f
  have hND : (normalizer (Q.map e.toMonoidHom : Set (Model F))).map MulAut.conj ≤
      normalizer (D : Set _) := by
    have hc : f.comp (MulAut.conj : C →* MulAut C) =
        (MulAut.conj : Model F →* MulAut (Model F)).comp e.toMonoidHom := by
      ext x : 1
      exact MulAut.congr_conj e x
    have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    rwa [map_map,hc,←map_map,map_equiv_normalizer_eq] at hh
  have hfixD : (Q.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom = Q.map e.toMonoidHom := by
    rw [map_map]
    have hc : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by
      ext x : 1
      change e (a (e.symm (e x))) = e (a x)
      rw [e.symm_apply_apply]
    rw [hc,←map_map,hfix]
  exact no_radical_quintic_actor hq hfive _ (hQ.map_equiv e) D hiD hND _
    (mem_map_of_mem f ha) ((MulAut.congr e).orderOf_eq a |>.trans ha5) hfixD

end Theory.SpecificGroups.G2Quintic
