module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceAssembly

/-!
# Literal support factors in the whole actor

A support decomposition for the subgroup PA transports along its inclusion
without changing the module or its moved subspaces. The factors are exactly
the canonical order-three plane-support family: any additional member fixes
every summand and contradicts faithfulness. Ambient conjugation therefore
permutes the same factors. These facts connect the D.2.14 local configurations
to both global normalizer bounds in D.2.22, printed p.189.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

noncomputable def SupportFactors.ofSubgroup {P H : Subgroup G} {s : ℕ}
    (hPH : P ≤ H) (d : SupportFactors (ρ.comp H.subtype) (P.subgroupOf H) s) :
    SupportFactors ρ P s := by
  classical
  let e := subgroupOfEquivOfLe hPH
  let F (i : Fin s) : Subgroup P := (d.factor i).map e.toMonoidHom
  have hF (i : Fin s) : (F i).map P.subtype = (d.ambient i).map H.subtype := by
    simp only [F, SupportFactors.ambient, map_map]
    rfl
  have hU (i : Fin s) : subspaceCommutator ρ ⊤ ((F i).map P.subtype) =
      subspaceCommutator (ρ.comp H.subtype) ⊤ (d.ambient i) := by
    rw [hF, subspaceCommutator_comp_map]
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (Nat.card_congr (e.subgroupMap (d.factor i)).toEquiv).symm.trans (d.card_factor i)
  · let ep : ((i : Fin s) → F i) ≃ ((i : Fin s) → d.factor i) :=
      Equiv.piCongrRight fun i => (e.subgroupMap (d.factor i)).symm.toEquiv
    have hb := e.bijective.comp (d.multiply_bijective.comp ep.bijective)
    convert hb using 1
    funext x
    simp only [Function.comp_apply, map_list_prod, List.map_ofFn]
    congr 1
  · intro i
    rw [hU]
    exact d.support_dim i
  · let ep : ((i : Fin s) → subspaceCommutator ρ ⊤ ((F i).map P.subtype)) ≃
        ((i : Fin s) → subspaceCommutator (ρ.comp H.subtype) ⊤ (d.ambient i)) :=
      Equiv.piCongrRight fun i => (LinearEquiv.ofEq _ _ (hU i)).toEquiv
    have hb := d.add_bijective.comp ep.bijective
    convert hb using 1
    funext x
    change (∑ i, (x i : V)) = ∑ i, ((LinearEquiv.ofEq _ _ (hU i)) (x i) : V)
    simp only [LinearEquiv.coe_ofEq_apply]

@[simp] theorem SupportFactors.ofSubgroup_ambient {P H : Subgroup G} {s : ℕ}
    (hPH : P ≤ H) (d : SupportFactors (ρ.comp H.subtype) (P.subgroupOf H) s)
    (i : Fin s) : (d.ofSubgroup ρ hPH).ambient i = (d.ambient i).map H.subtype := by
  simp only [SupportFactors.ofSubgroup, SupportFactors.ambient, map_map]
  rfl


theorem SupportFactors.factor_canonical [FiniteDimensional (ZMod 2) V] {P : Subgroup G} {s : ℕ}
    [P.Normal] [IsElementaryAbelian 3 P]
    (d : SupportFactors ρ P s) (i : Fin s) :
    let := Representation.BinaryGroupAction.action ρ
    d.ambient i ∈ smallSupportFactors G (Multiplicative V) 1 := by
  let := Representation.BinaryGroupAction.action ρ
  let : CommGroup P := IsMulCommutative.instCommGroup
  have hp : P ≤ fittingSubgroup G := le_sSup ⟨inferInstance, inferInstance⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨p,hp',rfl⟩
    exact hp p.property
  · exact (Subgroup.card_map_of_injective P.subtype_injective).trans (d.card_factor i)
  · rw [Representation.BinaryGroupAction.commutator_card]
    exact congrArg (fun n : ℕ => 2 ^ n) (d.support_dim i)

theorem SupportFactors.canonical_eq_factor [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) {P : Subgroup G} {s : ℕ}
    [P.Normal] [IsElementaryAbelian 3 P]
    (d : SupportFactors ρ P s) {X : Subgroup G}
    (hX : let := Representation.BinaryGroupAction.action ρ
      X ∈ smallSupportFactors G (Multiplicative V) 1) :
    ∃ i, X = d.ambient i := by
  classical
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let := Representation.BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  by_contra hn
  have hne (i : Fin s) : X ≠ d.ambient i := fun he => hn ⟨i,he⟩
  have hfix (i : Fin s) : subspaceCommutator ρ ⊤ (d.ambient i) ≤ fixedSpace ρ X := by
    have hh := smallSupportFactors_cross_fixed (V := Multiplicative V) (Or.inl rfl)
      hX (d.factor_canonical ρ i) (hne i)
    rw [Representation.BinaryGroupAction.commutator_eq,
      Representation.BinaryGroupAction.fixedPoints_eq] at hh
    exact (Representation.BinaryGroupAction.submoduleEquivSubgroup (V := V)).le_iff_le.mp hh
  have hx1 (x : X) : (x : G) = 1 := by
    apply hf
    ext v
    obtain ⟨w,hw⟩ := d.add_bijective.2 v
    simp only [map_one, Module.End.one_apply]
    rw [← hw,map_sum]
    exact Finset.sum_congr rfl (fun i _ => hfix i (w i).property x)
  have he : X = ⊥ := by
    apply bot_unique
    intro x hx
    exact hx1 ⟨x,hx⟩
  have hc := hX.2.1
  rw [he,Subgroup.card_bot] at hc
  norm_num at hc

theorem SupportFactors.factor_conj_closed [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) {P : Subgroup G} {s : ℕ}
    [P.Normal] [IsElementaryAbelian 3 P]
    (d : SupportFactors ρ P s) (g : G) (i : Fin s) :
    ∃ j, (d.ambient i).conjBy g = d.ambient j := by
  let := Representation.BinaryGroupAction.action ρ
  exact d.canonical_eq_factor ρ hf (smallSupportFactors_conjBy (d.factor_canonical ρ i) g)

end CFSG.Quasithin.ChapterD.FittingConfigurations
