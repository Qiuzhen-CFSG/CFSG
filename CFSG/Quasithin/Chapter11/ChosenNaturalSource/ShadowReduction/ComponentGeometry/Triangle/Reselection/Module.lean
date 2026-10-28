module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.FixedSpace
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Transitivity
public import Theory.SpecificGroups.SymplecticFour.Flag

/-!
# Recovering the whole chosen module and its Sylow-join kernel

A faithful simple-quotient chosen action has C_I(U)=O₂(I). Since IT/I is a
two-group, C_IT(U) is a normal two-group and is exactly O₂(IT). This step
does not require fixed-space vanishing or any model coordinates.

After the full preceding 11.3.2 implication kills C_U(I), the literal
projection U → U/C_U(I) becomes an isomorphism. Composing it with the
preceding symplectic marking gives coordinates on the whole original U,
with its actual conjugation equation. The new module's FF classification
and the placement of the old R₂ in its plane radical remain separate.
Source: Aschbacher--Smith 11.4.1(1--2), printed p.776.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T I U)

include D in
/-- The literal centralizer in IT is its two-core, including before killing
C_U(I). Only the actual T-invariance and simple quotient are needed. -/
theorem centralizer_join_eq_core
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hs : IsSimpleGroup (I ⧸ pCore 2 I)) :
    (I ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) =
      (I ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := I ⊔ (T : Subgroup G)
  let N := I.subgroupOf J
  let C := (centralizer (U : Set G)).subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer D.sylow_normalizes_component)
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    ((sup_le D.normalizes hTU).trans
      (le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer (U : Set G))))
  have hquot : IsPGroup 2 (J ⧸ N) := by
    apply isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hC : IsPGroup 2 C := by
    intro x
    obtain ⟨n, hn⟩ := hquot (QuotientGroup.mk' N x.val)
    have hnI : (x.val ^ 2 ^ n : J) ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' N) (x.val ^ 2 ^ n) = 1
      rw [map_pow]
      exact hn
    let y : I := ⟨(x.val : G) ^ 2 ^ n, hnI⟩
    have hy : y ∈ pCore 2 I :=
      (D.centralizer_eq_core_of_simple hs).le (C.pow_mem x.property (2 ^ n))
    obtain ⟨m, hm⟩ := pCore_isPGroup (p := 2) (G := I) ⟨y, hy⟩
    refine ⟨n + m, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg (fun z : pCore 2 I => (z.val : G)) hm
    simpa only [y, Subgroup.coe_pow, Subgroup.coe_mk, Subgroup.coe_one, pow_add, pow_mul] using hh
  have hle : C ≤ pCore 2 J := le_sSup ⟨inferInstance, hC⟩
  have hm := map_mono (f := J.subtype) hle
  rw [subgroupOf_map_subtype, inf_comm] at hm
  exact le_antisymm hm (le_inf (map_subtype_le _) D.core_centralizes)

/-- The fixed-free original projection, without choosing a complement. -/
def quotientEquiv (hfix : U ⊓ centralizer (I : Set G) = ⊥) :
    U ≃* Multiplicative D.chosenCentralQuotient :=
  MulEquiv.ofBijective D.toCentralQuotient
    ⟨centralQuotient_injective D hfix, D.toCentralQuotient_surjective⟩

variable {F : BinaryField}

/-- The actual full-module marking obtained from the original quotient marking. -/
def symplecticEquiv (hfix : U ⊓ centralizer (I : Set G) = ⊥)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))) :
    U ≃* Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector F.Carrier) :=
  (quotientEquiv D hfix).trans m.linearEquiv.toAddEquiv.toMultiplicative

/-- The coordinates retain literal conjugation and the original quotient map. -/
theorem symplecticEquiv_conj (hfix : U ⊓ centralizer (I : Set G) = ⊥)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
    (i : I) (u : U) :
    (symplecticEquiv D hfix m
      ⟨i.val * u.val * i.val⁻¹,
        (mem_normalizer_iff.mp (D.normalizes i.property) u.val).mp u.property⟩).toAdd =
      m.groupEquiv (QuotientGroup.mk' (pCore 2 I) i) •
        (symplecticEquiv D hfix m u).toAdd := by
  let v : D.space := (D.spaceEquiv.symm u).toAdd
  have hv : D.spaceEquiv (Multiplicative.ofAdd v) = u := D.spaceEquiv.apply_symm_apply u
  have hc : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction i v)) =
      ⟨i.val * u.val * i.val⁻¹,
        (mem_normalizer_iff.mp (D.normalizes i.property) u.val).mp u.property⟩ := by
    apply Subtype.ext
    rw [D.spaceEquiv_apply]
    have hv' := congrArg Subtype.val hv
    rw [D.spaceEquiv_apply] at hv'
    change i.val * (v.val.toMul.val : G) * i.val⁻¹ = _
    rw [hv']
  have he := centralQuotient_chosenAction D i v
  rw [hc, hv] at he
  change m.linearEquiv (D.toCentralQuotient _).toAdd = _
  rw [he]
  exact m.intertwines (QuotientGroup.mk' (pCore 2 I) i) (D.toCentralQuotient u).toAdd

/-- Apply the complete earlier shadow implication at the new choice before
turning its central-quotient symplectic marking into whole-module coordinates. -/
theorem exists_fixedFree_symplectic_coordinates (S : D.NonbinaryNaturalInput)
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (hlinear : Source.IsSL (I ⧸ pCore 2 I) 3 (2 ^ S.field.degree) →
      U ⊓ centralizer (I : Set G) = ⊥)
    (h1132 : ∀ H, Hypothesis1131At D S U₁ H → Proposition1132At D S U₁ H)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    U ⊓ centralizer (I : Set G) = ⊥ ∧
      ∃ e : U ≃* Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector S.field.Carrier),
        ∀ (i : I) (u : U),
          (e ⟨i.val * u.val * i.val⁻¹,
            (mem_normalizer_iff.mp (D.normalizes i.property) u.val).mp u.property⟩).toAdd =
          m.groupEquiv (QuotientGroup.mk' (pCore 2 I) i) • (e u).toAdd := by
  have hc := fixed_trivial D S U₁ hlinear h1132
  exact ⟨hc, symplecticEquiv D hc m, symplecticEquiv_conj D hc m⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
