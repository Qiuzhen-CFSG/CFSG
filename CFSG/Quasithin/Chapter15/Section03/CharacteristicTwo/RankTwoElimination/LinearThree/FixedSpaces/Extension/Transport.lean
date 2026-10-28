module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.FixedVectors

/-!
# The extension calculation in the actual component span

Restrict Basic's plus representation to L/O₂(L), with its specified matrix
marking. Its moving space and fixed space are exactly the ambient subgroups
[W_L,L] and C_WL(L). The involution calculation therefore gives
V ≤ [W_L,L] C_WL(L) whenever R ∩ L contains a lift of a nontrivial quotient
involution and the moving quotient has the specified natural coordinates.
The fixed-space containment is an output; no splitting is assumed.

The component representation is faithful for an outside component. Thus
the checked binary FF theorem can also supply the required natural quotient
from the FF property of this precise restriction. The local FF property
and radical involution must still be proved by the source application.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.16(1)
and the first-page extension calculation in 15.3.23, printed pp.1126,1128.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension

variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)
  [(actionKernel d L).Normal] [IsElementaryAbelian 2 (d.componentSpan L)]
  (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G))
  (hcore : L.pCoreIn 2 ≤ centralizer (d.componentSpan L : Set G))
  (e : (L ⧸ pCore 2 L) ≃* SL)

/-- Restriction of the actual plus representation along the chosen two-core quotient marking. -/
noncomputable def componentRepresentation :
    Representation (ZMod 2) SL (Additive (d.componentSpan L)) :=
  (representation d hN).comp ((plusImage d L L).subtype.comp
    ((coreQuotientMap d L hcore).comp e.symm.toMonoidHom))

/-- A lifted matrix acts by the original ambient conjugation. -/
theorem componentRepresentation_apply (l : L) (w : Additive (d.componentSpan L)) :
    ((componentRepresentation d L hN hcore e (e (QuotientGroup.mk l)) w).toMul : G) =
      (l : G) * (w.toMul : G) * (l : G)⁻¹ := by
  change ((representation d hN ((plusImage d L L).subtype
    (coreQuotientMap d L hcore (e.symm (e (QuotientGroup.mk l)))) ) w).toMul : G) = _
  rw [e.symm_apply_apply]
  rfl

private abbrev subspace : Subgroup (d.componentSpan L) ≃o
    Submodule (ZMod 2) (Additive (d.componentSpan L)) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

/-- An ambient subgroup, intersected with the actual span and regarded as a binary subspace. -/
noncomputable abbrev subgroupSpace (A : Subgroup G) :
    Submodule (ZMod 2) (Additive (d.componentSpan L)) :=
  (Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2))
    (A.subgroupOf (d.componentSpan L))

/-- Every action displacement belongs to the ambient commutator subgroup. -/
theorem moving_le_spanCommutator :
    (moving (componentRepresentation d L hN hcore e)).toSubmodule ≤
      subgroupSpace d L (spanCommutator d L) := by
  rw [moving_eq]
  apply Submodule.span_le.mpr
  rintro v ⟨g, _, w, _, rfl⟩
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm g)
  have hg : e (QuotientGroup.mk l) = g := by
    change e ((QuotientGroup.mk' (pCore 2 L)) l) = g
    rw [hl, e.apply_symm_apply]
  rw [← hg]
  change (((componentRepresentation d L hN hcore e (e (QuotientGroup.mk l)) w - w).toMul) : G)
    ∈ spanCommutator d L
  simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [componentRepresentation_apply]
  rw [spanCommutator, commutator_comm]
  exact commutator_mem_commutator l.property w.toMul.property

/-- A fixed vector centralizes the original component. -/
theorem fixedSpace_toMul_le_centralizer
    {w : Additive (d.componentSpan L)}
    (hw : w ∈ fixedSpace (componentRepresentation d L hN hcore e) ⊤) :
    (w.toMul : G) ∈ centralizer (L : Set G) := by
  intro l hl
  have hh := congrArg (fun v : Additive (d.componentSpan L) => (v.toMul : G))
    (hw ⟨e (QuotientGroup.mk (⟨l, hl⟩ : L)), mem_top _⟩)
  change ((componentRepresentation d L hN hcore e (e (QuotientGroup.mk (⟨l, hl⟩ : L))) w).toMul : G) =
    (w.toMul : G) at hh
  rw [componentRepresentation_apply] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh


/-- The representation commutator is exactly U_L, with no assumed layer identification. -/
theorem moving_eq_spanCommutator :
    (moving (componentRepresentation d L hN hcore e)).toSubmodule =
      subgroupSpace d L (spanCommutator d L) := by
  apply le_antisymm (moving_le_spanCommutator d L hN hcore e)
  let ρ := componentRepresentation d L hN hcore e
  let H := (subspace d L).symm (moving ρ).toSubmodule
  have hU : spanCommutator d L ≤ H.map (d.componentSpan L).subtype := by
    rw [spanCommutator, commutator_comm]
    apply commutator_le.mpr
    intro l hl w hw
    let v : Additive (d.componentSpan L) := Additive.ofMul ⟨w, hw⟩
    let g := e (QuotientGroup.mk (⟨l, hl⟩ : L))
    have hd : ρ g v - v ∈ (moving ρ).toSubmodule := Coinvariants.sub_mem_ker g v
    refine ⟨(ρ g v - v).toMul, hd, ?_⟩
    change (((componentRepresentation d L hN hcore e g v - v).toMul) : G) = _
    simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [componentRepresentation_apply]
    rfl
  intro v hv
  obtain ⟨w, hw, he⟩ := hU hv
  have hwv : w = v.toMul := Subtype.ext he
  change v.toMul ∈ H
  exact hwv ▸ hw

/-- The representation fixed space is exactly C_WL(L). -/
theorem fixedSpace_eq_centralizer :
    fixedSpace (componentRepresentation d L hN hcore e) ⊤ =
      subgroupSpace d L (centralizer (L : Set G)) := by
  apply le_antisymm (fun _ hw => fixedSpace_toMul_le_centralizer d L hN hcore e hw)
  intro w hw g
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm g.val)
  have hg : e (QuotientGroup.mk l) = g.val := by
    change e ((QuotientGroup.mk' (pCore 2 L)) l) = g.val
    rw [hl, e.apply_symm_apply]
  change componentRepresentation d L hN hcore e g.val w = w
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [← hg, componentRepresentation_apply]
  exact mul_inv_eq_iff_eq_mul.mpr (hw l l.property)

/-- Fixed vectors for a lifted nontrivial quotient involution lie in U_L C_W(L). -/
theorem fixed_le_spanCommutator_sup_centralizer {m : ℕ}
    (q : ModuleQuotient (moving (componentRepresentation d L hN hcore e)).toRepresentation m)
    (l : L) (ht : e (QuotientGroup.mk l) ^ 2 = 1)
    (hne : e (QuotientGroup.mk l) ≠ 1) :
    d.componentSpan L ⊓ centralizer ({(l : G)} : Set G) ≤
      spanCommutator d L ⊔ (d.componentSpan L ⊓ centralizer (L : Set G)) := by
  intro w hw
  let v : Additive (d.componentSpan L) := Additive.ofMul ⟨w, hw.1⟩
  have hv : v ∈ fixedSpace (componentRepresentation d L hN hcore e)
      (zpowers (e (QuotientGroup.mk l))) := by
    apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [componentRepresentation_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hw.2 l (Set.mem_singleton _))
  have hs := involution_fixed_le_centralSum q (e (QuotientGroup.mk l)) ht hne hv
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hs
  have haC := fixedSpace_toMul_le_centralizer d L hN hcore e ha
  have hbU := moving_le_spanCommutator d L hN hcore e hb
  have hmem : (a.toMul : G) * (b.toMul : G) ∈
      spanCommutator d L ⊔ (d.componentSpan L ⊓ centralizer (L : Set G)) :=
    mul_mem (mem_sup_right ⟨a.toMul.property, haC⟩) (mem_sup_left hbU)
  have he := congrArg (fun x : Additive (d.componentSpan L) => (x.toMul : G)) hab
  change (a.toMul : G) * (b.toMul : G) = w at he
  exact he ▸ hmem

/-- The source radical fixes V. A quotient involution in R ∩ L detects the
upper extension, so the desired containment is proved rather than assumed. -/
theorem V_le_spanCommutator_sup_centralizer [Finite G]
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcoreR : L.pCoreIn 2 ≤ d.R) {m : ℕ}
    (q : ModuleQuotient (moving (componentRepresentation d L hN
      (core_centralizes_span d L hcoreR (hR.le.trans inf_le_right)) e)).toRepresentation m)
    (l : L) (hlR : (l : G) ∈ d.R)
    (ht : e (QuotientGroup.mk l) ^ 2 = 1) (hne : e (QuotientGroup.mk l) ≠ 1) :
    d.V ≤ spanCommutator d L ⊔ (d.componentSpan L ⊓ centralizer (L : Set G)) := by
  apply le_trans ?_ (fixed_le_spanCommutator_sup_centralizer d L hN
    (core_centralizes_span d L hcoreR (hR.le.trans inf_le_right)) e q l ht hne)
  refine le_inf (le_conjugateSpanBy d.V L) ?_
  intro v hv x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ((hR.le hlR).2 v hv).symm

/-- The component restriction of the plus representation is faithful: a
trivial action of the simple quotient would put the outside L in C_G(V). -/
theorem componentRepresentation_injective
    (houtside : ¬ L ≤ d.M) (hC : centralizer (d.V : Set G) ≤ d.M) :
    Function.Injective (componentRepresentation d L hN hcore e) := by
  let ρ := componentRepresentation d L hN hcore e
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact ρ.ker_eq_bot_iff.mp hb
  · have he : ρ = 1 := MonoidHom.ker_eq_top_iff.mp ht
    apply False.elim
    apply houtside
    intro l hl
    apply hC
    intro v hv
    let w : Additive (d.componentSpan L) := Additive.ofMul
      ⟨v, le_conjugateSpanBy d.V L hv⟩
    have hw : ρ (e (QuotientGroup.mk (⟨l, hl⟩ : L))) w = w := by rw [he]; rfl
    have hh := congrArg (fun a : Additive (d.componentSpan L) => (a.toMul : G)) hw
    change ((componentRepresentation d L hN hcore e (e (QuotientGroup.mk (⟨l, hl⟩ : L))) w).toMul : G) = v at hh
    rw [componentRepresentation_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The checked binary FF classification constructs the natural moving
quotient. Only the actual component FF property and radical involution
remain as local action inputs; no particular C.1.34 case is assumed. -/
theorem V_le_spanCommutator_sup_centralizer_of_FF [Finite G]
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcoreR : L.pCoreIn 2 ≤ d.R)
    (houtside : ¬ L ≤ d.M) (hC : centralizer (d.V : Set G) ≤ d.M)
    (hFF : IsFFModule (componentRepresentation d L hN
      (core_centralizes_span d L hcoreR (hR.le.trans inf_le_right)) e))
    (l : L) (hlR : (l : G) ∈ d.R)
    (ht : e (QuotientGroup.mk l) ^ 2 = 1) (hne : e (QuotientGroup.mk l) ≠ 1) :
    d.V ≤ spanCommutator d L ⊔ (d.componentSpan L ⊓ centralizer (L : Set G)) := by
  obtain ⟨m, _, ⟨q⟩⟩ := moving_quotient
    (componentRepresentation d L hN
      (core_centralizes_span d L hcoreR (hR.le.trans inf_le_right)) e)
    (componentRepresentation_injective d L hN _ e houtside hC) hFF
  exact V_le_spanCommutator_sup_centralizer d L hN e hR hcoreR q l hlR ht hne

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension

end
