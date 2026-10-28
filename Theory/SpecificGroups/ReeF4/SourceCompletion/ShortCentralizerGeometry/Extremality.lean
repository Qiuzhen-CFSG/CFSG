module
public import Theory.GroupTheory.SaturatedCentralizer
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Extremality through a full endpoint comparison

An involution in a subgroup containing the ambient Sylow is chosen extremal
inside that subgroup. An embedding identifying its entire model centralizer,
together with one-way ambient-to-model involution fusion on that endpoint,
makes it extremal in the ambient group. A Sylow subgroup of the ambient
centralizer is conjugated into the original Sylow; model fusion then embeds
it in the model centralizer and bounds its order by the local Sylow order.

This is the finite-group extremality argument used for the Ree instance of
Aschbacher–Smith F.4.40, printed p.294 (`refs/quasithin.pdf`).
-/

open Subgroup Theory.GroupTheory
open scoped Pointwise
public noncomputable section
namespace ReeF4.SourceCompletion.ShortCentralizerGeometry

private theorem pGroup_card_le_sylow {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p H) (f : H →* G) (hf : Function.Injective f)
    (S : Sylow p G) : Nat.card H ≤ Nat.card S := by
  obtain ⟨R,hR⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  calc
    Nat.card H = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    _ ≤ Nat.card R := Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hR)
    _ = Nat.card S := Nat.card_congr (R.equiv S).toEquiv

/-- Full endpoint fusion and an entire model centralizer transfer extremality. -/
theorem sylow_centralizer_of_endpoint_fusion
    {G E : Type*} [Group G] [Finite G] [Group E] [Finite E]
    (T : Sylow 2 G) (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (f : P →* E) (hf : Function.Injective f)
    (v : P) (hvT : v.val ∈ T) (hv2 : orderOf v.val = 2)
    (hfusion : ∀ x y : P, orderOf x.val = 2 → orderOf y.val = 2 →
      IsConj x.val y.val → IsConj (f x) (f y))
    (hC : (centralizer ({v} : Set P)).map f = centralizer ({f v} : Set E))
    (hlocal : ∃ R : Sylow 2 (centralizer ({v} : Set P)),
      (R : Subgroup (centralizer ({v} : Set P))) =
        ((T : Subgroup G).subgroupOf P).subgroupOf (centralizer ({v} : Set P))) :
    ∃ R : Sylow 2 (centralizer ({v.val} : Set G)),
      (R : Subgroup (centralizer ({v.val} : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G)) := by
  let C := centralizer ({v.val} : Set G)
  let U := (T : Subgroup G).subgroupOf C
  obtain ⟨Q,hUQ⟩ := (T.isPGroup'.comap_subtype (K := C)).exists_le_sylow
  let K := (Q : Subgroup C).map C.subtype
  obtain ⟨S,hKS⟩ := (Q.isPGroup'.map C.subtype).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S T
  let a : G ≃* G := MulAut.conj g
  have hKP : ∀ x : Q, a x.val.val ∈ P := by
    intro x
    apply hTP
    rw [←hg]
    exact mem_map_of_mem a.toMonoidHom (hKS (mem_map_of_mem C.subtype x.property))
  have hvK : v.val ∈ K := mem_map_of_mem C.subtype
    (hUQ (show (⟨v.val,mem_centralizer_singleton_iff.mpr rfl⟩ : C) ∈ U from hvT))
  have hwT : a v.val ∈ T := by
    rw [←hg]
    exact mem_map_of_mem a.toMonoidHom (hKS hvK)
  let w : P := ⟨a v.val,hTP hwT⟩
  have hw2 : orderOf w.val = 2 := (a.orderOf_eq v.val).trans hv2
  obtain ⟨b,hb⟩ := isConj_iff.mp (hfusion w v hw2 hv2
    (isConj_iff.mpr ⟨g,rfl⟩).symm)
  let j : Q →* P := (a.toMonoidHom.comp (C.subtype.comp (Q : Subgroup C).subtype)).codRestrict P hKP
  have hj : Function.Injective j := (MonoidHom.injective_codRestrict _ _ _).mpr
    (a.injective.comp (C.subtype_injective.comp (Q : Subgroup C).subtype_injective))
  let k : Q →* E := (MulAut.conj b).toMonoidHom.comp (f.comp j)
  have hk : Function.Injective k := (MulAut.conj b).injective.comp (hf.comp hj)
  have hkC (x : Q) : k x ∈ centralizer ({f v} : Set E) := by
    have hcomm : Commute (j x) w := by
      change j x * w = w * j x
      apply Subtype.ext
      exact (show Commute x.val.val v.val from
        mem_centralizer_singleton_iff.mp x.val.property).map a.toMonoidHom |>.eq
    have hh := (hcomm.map f).map (MulAut.conj b).toMonoidHom
    change Commute (k x) (b * f w * b⁻¹) at hh
    rw [hb] at hh
    exact mem_centralizer_singleton_iff.mpr hh.eq
  let e : centralizer ({v} : Set P) ≃* centralizer ({f v} : Set E) :=
    ((centralizer ({v} : Set P)).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr hC)
  let kC := k.codRestrict _ hkC
  obtain ⟨R,hR⟩ := hlocal
  have hcard := pGroup_card_le_sylow Q.isPGroup' (e.symm.toMonoidHom.comp kC)
    (e.symm.injective.comp ((MonoidHom.injective_codRestrict _ _ _).mpr hk)) R
  have hRU : Nat.card R = Nat.card U := by
    rw [hR]
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨⟨x.val.val.val,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.val.property))⟩,x.property⟩
      invFun := fun x => ⟨⟨⟨x.val.val,hTP x.property⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Q,(eq_of_le_of_card_ge hUQ (hcard.trans_eq hRU)).symm⟩

private theorem exists_sylow_of_saturated
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (x : T)
    (hmax : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({x} : Set T)).map (T : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({x.val} : Set G) →
      V = (centralizer ({x} : Set T)).map (T : Subgroup G).subtype) :
    ∃ R : Sylow 2 (centralizer ({x.val} : Set G)),
      (R : Subgroup (centralizer ({x.val} : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer ({x.val} : Set G)) := by
  let C := centralizer ({x.val} : Set G)
  obtain ⟨R,hR⟩ := (T.isPGroup'.comap_subtype (K := C)).exists_le_sylow
  refine ⟨R,?_⟩
  apply map_injective C.subtype_injective
  rw [subgroupOf_map_subtype]
  have he := hmax ((R : Subgroup C).map C.subtype) (R.isPGroup'.map _) ?_
    (map_subtype_le _)
  · rwa [map_subtype_centralizer_singleton] at he
  · rw [map_subtype_centralizer_singleton,←subgroupOf_map_subtype]
    exact map_mono hR

/-- Select an extremal conjugate within the full endpoint, then transfer its
extremality to the ambient group through the same map. -/
theorem exists_extremal_endpoint_conjugate
    {G E : Type*} [Group G] [Finite G] [Group E] [Finite E]
    (T : Sylow 2 G) (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (f : P →* E) (hf : Function.Injective f)
    (v : P) (hvT : v.val ∈ T) (hv2 : orderOf v.val = 2)
    (hfusion : ∀ x y : P, orderOf x.val = 2 → orderOf y.val = 2 →
      IsConj x.val y.val → IsConj (f x) (f y))
    (hC : (centralizer ({v} : Set P)).map f = centralizer ({f v} : Set E)) :
    ∃ (g w : P), g * v * g⁻¹ = w ∧ w.val ∈ T ∧ orderOf w.val = 2 ∧
      (centralizer ({w} : Set P)).map f = centralizer ({f w} : Set E) ∧
      (∃ R : Sylow 2 (centralizer ({w} : Set P)),
        (R : Subgroup (centralizer ({w} : Set P))) =
          ((T : Subgroup G).subgroupOf P).subgroupOf (centralizer ({w} : Set P))) ∧
      ∃ R : Sylow 2 (centralizer ({w.val} : Set G)),
        (R : Subgroup (centralizer ({w.val} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({w.val} : Set G)) := by
  let S := T.subtype hTP
  obtain ⟨w,hvw,hmax⟩ := S.exists_conjugate_with_saturated_centralizer ⟨v,hvT⟩
  obtain ⟨g,hg⟩ := isConj_iff.mp hvw
  have hw2 : orderOf w.val.val = 2 := by
    have he : (MulAut.conj g.val) v.val = w.val.val := congrArg Subtype.val hg
    rw [←he,(MulAut.conj g.val).orderOf_eq,hv2]
  have hmap : (centralizer ({w.val} : Set P)).map f =
      centralizer ({f w.val} : Set E) := by
    have hcg : (MulAut.conj g) v = w.val := hg
    have hcf : (MulAut.conj (f g)) (f v) = f w.val := by
      simpa only [MulAut.conj_apply,map_mul,map_inv] using congrArg f hg
    rw [←hcg,←CentralizerSmallKernelTransport.map_centralizer,Subgroup.map_map]
    have hc : f.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (f g)).toMonoidHom.comp f := by
      ext a
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
        map_mul,map_inv]
    rw [hc,←Subgroup.map_map,hC,CentralizerSmallKernelTransport.map_centralizer,hcf,hcg]
  have hlocal := exists_sylow_of_saturated S w hmax
  exact ⟨g,w.val,hg,w.property,hw2,hmap,hlocal,
    sylow_centralizer_of_endpoint_fusion T P hTP f hf w.val w.property hw2 hfusion hmap hlocal⟩

end ReeF4.SourceCompletion.ShortCentralizerGeometry
