module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentStructure
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Centralizers
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.Quasithin.EvenCharacteristic

/-!
# Ambient separation of the paired involution marks

The centralizer of the original product mark has characteristic two by
1.1.3(2) and the literal hypotheses of 1.1.5. The second marked centralizer
contains the component selected in 2.4.32, so its mark cannot fuse with that
product. A chosen graph actor cannot fuse with the product either: its fixed
subgroup in the normal component is S₃, contradicting normal inheritance of
characteristic two inside the simultaneous centralizer.

The graph actor is an explicit element, allowing the replacement made in the
source proof; it is not identified with the initial coset representative.
The component and its marked S₃ fixed subgroup are supplied by the component
and faithful pair-model branches of 2.4.34.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, Lemma 2.4.34, printed
p. 548; the centralizer inheritance used is Lemma 1.1.3(2).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem characteristic_centralizer_conj {x y : G}
    (h : IsConj x y) (hc : HasCharacteristicTwo (centralizer ({x} : Set G))) :
    HasCharacteristicTwo (centralizer ({y} : Set G)) := by
  obtain ⟨a,rfl⟩ := isConj_iff.mp h
  exact hc.of_equiv (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj a) x)

/-- The literal marked centralizer in the original 1.1.5 hypotheses has
characteristic two by the centralizer clause of 1.1.3(2). -/
theorem marked_centralizer_characteristicTwo
    {H M : Subgroup G} {P : Sylow 2 H} {z : G}
    (h : Chapter1.Lemma115Hypotheses H P M z) :
    HasCharacteristicTwo (centralizer ({z} : Set G)) := by
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using h.involution)
  have hh := pCoreIn_selfCentralizing_centralizer h.mem_HeOver.1 hp
    (zpowers_le.mpr h.mem_intersection.2)
  have he : centralizer (zpowers z : Set G) = centralizer ({z} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hc : M ⊓ centralizer ({z} : Set G) = centralizer ({z} : Set G) :=
    inf_eq_right.mpr h.centralizer_le
  apply Chapter1.mem_He_iff.mp
  change (centralizer ({z} : Set G)) ⊓
    centralizer ((centralizer ({z} : Set G)).pCoreIn 2 : Set G) ≤ _
  simpa only [he,hc] using hh

/-- The actual component centralizer cannot fuse its marking to the
source characteristic-two mark. -/
theorem source_second_not_conj_product {M : Subgroup G} {d : MinimalBlockSetup M}
    {T : Sylow 2 G} {c : SourcePairCoordinates d T} (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) :
    ¬ IsConj g.z₂ (g.z₁*g.z₂) := by
  intro hf
  exact not_isComponent_of_twoCore
    (characteristic_centralizer_conj hf.symm (marked_centralizer_characteristicTwo h)) K hK

private theorem symmetric_three_not_characteristicTwo :
    ¬ HasCharacteristicTwo (Equiv.Perm (Fin 3)) := by
  have hc : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
      Function.surjective_id (by
        simp only [MonoidHom.ker_id]
        exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using hh.symm
  intro hh
  change centralizer (pCore 2 (Equiv.Perm (Fin 3)) : Set (Equiv.Perm (Fin 3))) ≤ _ at hh
  rw [hc, coe_bot] at hh
  have he : (Equiv.swap (0 : Fin 3) 1) = 1 := hh
    (mem_centralizer_singleton_iff.mpr (by simp))
  have hx := congrArg (fun a : Equiv.Perm (Fin 3) => a 0) he
  norm_num at hx

/-- In characteristic two, an involution centralizer cannot contain a normal
S₃. This is the source's odd-core obstruction, via normal inheritance. -/
theorem not_characteristicTwo_of_normal_symmetric_three_centralizer
    {i x : G} (hi : orderOf i = 2) (hix : Commute i x)
    (K : Subgroup (centralizer ({i} : Set G))) [K.Normal]
    (e : K.subgroupOf (centralizer
      ({(⟨x, mem_centralizer_singleton_iff.mpr hix.eq.symm⟩ : centralizer ({i} : Set G))} :
        Set (centralizer ({i} : Set G)))) ≃* Equiv.Perm (Fin 3)) :
    ¬ HasCharacteristicTwo (centralizer ({x} : Set G)) := by
  intro hx
  let H := centralizer ({i} : Set G)
  let xH : H := ⟨x, mem_centralizer_singleton_iff.mpr hix.eq.symm⟩
  let D := centralizer ({xH} : Set H)
  have hM : centralizer ({x} : Set G) ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr hx
  have hp : IsPGroup 2 (zpowers i) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers,pow_one] using hi)
  have hh := pCoreIn_selfCentralizing_centralizer hM hp
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hix.eq))
  have he : centralizer (zpowers i : Set G) = H := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hc : HasCharacteristicTwo (centralizer ({x} : Set G) ⊓ H : Subgroup G) := by
    apply Chapter1.mem_He_iff.mp
    change (centralizer ({x} : Set G) ⊓ H) ⊓
      centralizer ((centralizer ({x} : Set G) ⊓ H).pCoreIn 2 : Set G) ≤ _
    simpa only [he] using hh
  let f : (centralizer ({x} : Set G) ⊓ H : Subgroup G) ≃* D :=
    { toFun := fun a => ⟨⟨a,a.property.2⟩,
        mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp a.property.1))⟩
      invFun := fun a => ⟨a, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.property)), a.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hD := hc.of_equiv f
  have hK : HasCharacteristicTwo (K.subgroupOf D) :=
    normal_core_selfCentralizing hD (K.subgroupOf D)
  exact symmetric_three_not_characteristicTwo
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hK)

/-- Applied to the chosen graph actor, the S₃ fixed subgroup
excludes fusion with z₁z₂. The model fixed-group is supplied on this literal K. -/
theorem source_actor_not_conj_product {M : Subgroup G} {d : MinimalBlockSetup M}
    {T : Sylow 2 G} {c : SourcePairCoordinates d T} (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (x : G) (hx₂ : x ∈ involutionCentralizer g.z₂)
    (e : K.subgroupOf (centralizer ({(⟨x, hx₂⟩ : involutionCentralizer g.z₂)} :
      Set (involutionCentralizer g.z₂))) ≃* Equiv.Perm (Fin 3)) :
    ¬ IsConj x (g.z₁*g.z₂) := by
  intro hf
  have hx := characteristic_centralizer_conj hf.symm (marked_centralizer_characteristicTwo h)
  exact not_characteristicTwo_of_normal_symmetric_three_centralizer g.order_second
    (show Commute g.z₂ x from (mem_centralizer_singleton_iff.mp hx₂).symm) K e hx

end CFSG.Quasithin.Chapter2.DoubleA3
