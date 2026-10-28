module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FaithfulAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.OffenderActor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Line
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.MarkedActors
public import Theory.ThreeSubgroups

/-!
# The component module is its own commutator module

The earlier identity L = [L,Y₊], together with Y₊ ≤ L, makes L perfect.
Inside I, both L and U_I are normal. The three-subgroups lemma then gives
[[U_I,L],L] = [U_I,L]. We identify each linear action difference with its
original group commutator to transfer this equality to the coinvariant
kernel of componentAction. Restriction to the offender-generated actor
preserves that kernel. Thus the U of B.5.1 is exactly U_L, not a smaller
subspace of the module being classified.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and
15.3.26–27, printed pp.99–103 and 1130–1132. This is preparation for the
conditional specialization; it does not assert any module classification.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
variable {G : Type*} [Group G]

/-- The earlier full Y₊-commutator and Y₊ ≤ L make the actual component perfect. -/
theorem component_perfect (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L) : Group.IsPerfect c.L := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm ((Subgroup.commutator_le_sup c.L c.L).trans (sup_idem _).le)
  exact c.commutator_eq.le.trans (commutator_mono le_rfl hYL)

private theorem commutator_idempotent (U L : Subgroup G) [U.Normal] [L.Normal]
    (hL : ⁅L, L⁆ = L) : ⁅⁅U, L⁆, L⁆ = ⁅U, L⁆ := by
  apply le_antisymm (commutator_le_left _ _)
  have h : ⁅⁅L, L⁆, U⁆ ≤ ⁅⁅U, L⁆, L⁆ :=
    commutator_commutator_le_of_rotate
      (by rw [commutator_comm L U]) le_rfl
  simpa only [hL, commutator_comm L U] using h

/-- The three-subgroups lemma makes the full component module L-generated. -/
theorem componentModule_full [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hYL : d.Yplus ≤ c.L) :
    ⁅d.componentModule I c.L, c.L⁆ = d.componentModule I c.L := by
  have hUI := span_le d (show d.S ≤ I from hI ▸ le_sup_right)
  let _ : ((d.UI I).subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy d.Z I)
  let _ := hn
  let _ := component_perfect d c hYL
  have hL : ⁅c.L.subgroupOf I, c.L.subgroupOf I⁆ = c.L.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (component_le c),
      c.L.commutator_eq_self]
  have he := congrArg (fun H : Subgroup I => H.map I.subtype)
    (commutator_idempotent ((d.UI I).subgroupOf I) (c.L.subgroupOf I) hL)
  simpa only [map_commutator, map_subgroupOf_eq_of_le hUI,
    map_subgroupOf_eq_of_le (component_le c)] using he

private theorem coinvariants_full_of_commutator
    {K : Type*} [Group K] (W A : Subgroup G) [IsElementaryAbelian 2 W]
    (q : G →* K) (ρ : Representation (ZMod 2) K (Additive W))
    (haction : ∀ g v, ((ρ (q g) v).toMul : G) = g * (v.toMul : G) * g⁻¹)
    (hfull : ⁅W, A⁆ = W) :
    Representation.Coinvariants.ker (ρ.comp (A.map q).subtype) = ⊤ := by
  let C := Representation.Coinvariants.ker (ρ.comp (A.map q).subtype)
  let D : Subgroup G := C.toAddSubgroup.toSubgroup'.map W.subtype
  have hWD : W ≤ D := by
    rw [← hfull, commutator_comm W A]
    apply commutator_le.mpr
    intro a ha w hw
    let v : Additive W := Additive.ofMul ⟨w, hw⟩
    have hv : ρ (q a) v - v ∈ C :=
      Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp (A.map q).subtype)
        ⟨q a, mem_map_of_mem q ha⟩ v
    have hm := mem_map_of_mem W.subtype
      (show (ρ (q a) v - v).toMul ∈ C.toAddSubgroup.toSubgroup' from hv)
    change (((ρ (q a) v - v).toMul : W) : G) ∈ D at hm
    simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hm
    rw [haction] at hm
    exact hm
  apply top_unique
  intro v _
  obtain ⟨w, hw, he⟩ := hWD v.toMul.property
  have he' : Additive.ofMul w = v := by
    apply Additive.toMul.injective
    exact Subtype.ext he
  exact he' ▸ hw

/-- The full ambient commutator is the full coinvariant kernel of the actual star action. -/
theorem componentAction_full [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hchar : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]
    (hYL : d.Yplus ≤ c.L) :
    Representation.Coinvariants.ker
      ((componentAction d c hn hI hchar P hP).comp (d.starImage I c.L).subtype) = ⊤ := by
  apply coinvariants_full_of_commutator ((d.componentModule I c.L).subgroupOf I)
    (c.L.subgroupOf I) (d.starMap I)
  · intro i v
    exact Subtype.ext (componentAction_apply d c hn hI hchar P hP i v)
  · apply map_injective I.subtype_injective
    rw [map_commutator,
      map_subgroupOf_eq_of_le ((componentModule_le_span d c).trans
        (span_le d (hI ▸ le_sup_right))),
      map_subgroupOf_eq_of_le (component_le c)]
    exact componentModule_full d c hn hI hYL

/-- Restricting the ambient actor does not change commutators with a contained subgroup. -/
theorem coinvariants_subgroupOf {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) K V)
    (J L : Subgroup K) (hL : L ≤ J) :
    Representation.Coinvariants.ker ((ρ.comp J.subtype).comp (L.subgroupOf J).subtype) =
      Representation.Coinvariants.ker (ρ.comp L.subtype) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, v⟩, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker
      (ρ := ρ.comp L.subtype) ⟨l.val.val, l.property⟩ v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, v⟩, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker
      (ρ := (ρ.comp J.subtype).comp (L.subgroupOf J).subtype)
      ⟨⟨l, hL l.property⟩, l.property⟩ v

/-- In B.5.1 applied to the offender actor, U = [V,L] is the entire original U_L. -/
theorem offenderAction_full [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hchar : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]
    (hYL : d.Yplus ≤ c.L) (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (he : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    Representation.Coinvariants.ker
      ((offenderAction d c hn hI hchar P hP).comp
        (offenderComponent d c hn hI hchar P hP).subtype) = ⊤ := by
  rw [offenderAction, offenderComponent, coinvariants_subgroupOf _ _ _
    (component_le_offenderGroup d c hn hI hchar P hP e he)]
  exact componentAction_full d c hn hI hchar P hP hYL

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization

end
