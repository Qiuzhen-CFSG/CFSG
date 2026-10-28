module
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.CenterTwoCoreSylowPromotion
public import Theory.Quasithin.EvenCharacteristic

/-!
# Center-two normal radicals and marked Sylow promotion

A normal self-centralizing two-subgroup with center of order two forces the
same center order for the full two-core: its central involution is fixed by
the whole group, and every central element of the two-core centralizes the
radical. An injective local embedding whose central involution has no extra
ambient centralizer therefore carries every local Sylow to an ambient Sylow.
The actual embedding and chosen Sylow are preserved.

Source: the local argument in Aschbacher--Smith F.4.33, printed p.291.
-/

public section
noncomputable section
namespace Subgroup
variable {P : Type*} [Group P]

theorem center_twoCore_card_of_normal_selfCentralizing
    (Q : Subgroup P) [Q.Normal] (hq : IsPGroup 2 Q)
    (hc : centralizer (Q : Set P) ≤ Q) (hz : Nat.card (center Q) = 2) :
    Nat.card (center (pCore 2 P)) = 2 := by
  let O := pCore 2 P
  let Z := (center Q).map Q.subtype
  have hQO : Q ≤ O := le_sSup ⟨inferInstance, hq⟩
  have hZcard : Nat.card Z = 2 := (card_map_of_injective Q.subtype_injective).trans hz
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZcentral : Z ≤ center P := central_of_normal_card_two Z hZcard
  have he : (center O).map O.subtype = Z := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      have hyC : (y : P) ∈ centralizer (Q : Set P) := by
        intro q hq
        exact congrArg Subtype.val (mem_center_iff.mp hy ⟨q, hQO hq⟩)
      rw [centralizer_eq_mapped_center_of_le Q hc] at hyC
      exact hyC
    · rintro x ⟨y, hy, rfl⟩
      refine ⟨⟨y, hQO y.property⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro o
      exact Subtype.ext (mem_center_iff.mp (hZcentral ⟨y,hy,rfl⟩) o)
  have hh := congrArg (fun A : Subgroup P => Nat.card A) he
  rw [card_map_of_injective O.subtype_injective, hZcard] at hh
  exact hh

section GenericTransport
variable {G A : Type*} [Group G] [Group A] [Finite G]

theorem sylow_map_of_center_two_core
    (f : A →* G) (hf : Function.Injective f)
    (hcenter : Nat.card (center (pCore 2 A)) = 2)
    (hself : centralizer (pCore 2 A : Set A) ≤ pCore 2 A)
    (z : A) (hz : orderOf z = 2) (hzc : z ∈ center A)
    (hc : centralizer ({f z} : Set G) ≤ f.range) (T : Sylow 2 A) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = (T : Subgroup A).map f := by
  let : Finite A := Finite.of_injective f hf
  let C : Subgroup G := centralizer {f z}
  have hr : f.range = C := by
    apply le_antisymm _ hc
    rintro x ⟨a, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hzc a))
  let e : A ≃* C := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  have hcore : (pCore 2 A).map e.toMonoidHom = pCore 2 C := pCore_map_iso 2 e
  let ecore : pCore 2 A ≃* pCore 2 C :=
    (e.subgroupMap (pCore 2 A)).trans (MulEquiv.subgroupCongr hcore)
  have hcc : Nat.card (center (pCore 2 C)) = 2 :=
    (Nat.card_congr (centerCongr ecore.symm).toEquiv).trans hcenter
  have hcs : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hself
  have hzG : orderOf (f z) = 2 := (orderOf_injective f hf z).trans hz
  have heSurj : Function.Surjective e.toMonoidHom := fun x => ⟨e.symm x, e.apply_symm_apply x⟩
  obtain ⟨S, hS⟩ := (centralizer_structure_of_center_two_core (f z) hzG hcc hcs).2.2
    (T.mapSurjective (f := e.toMonoidHom) heSurj)
  refine ⟨S, hS.trans ?_⟩
  change ((T : Subgroup A).map e.toMonoidHom).map C.subtype = _
  rw [map_map]
  rfl
end GenericTransport

end Subgroup
