module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.TransvectionSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents

/-!
# The actual A₇ component and its faithful sections

Under the literal supplement conclusion H = KT of 13.8.21, the image of T
surjects onto H*/K*. Relative normality and the intrinsic A₇ marking then
make K* the generalized Fitting subgroup and the monolith of H*. This
constructs the normal-subgroup premise used in 13.8.22–24. The last theorem
applies it to both actual sections of U_H/V₁ in 13.8.23.

The companion generation theorem uses the original seed identity and L₁ ≤ K;
it does not assume U_H = [U_H,K]. These are conditional source deductions:
the preceding component normality and supplement are still supplied by the
13.8.16–21 owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.21–24, printed pp.957–959.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open TransvectionRecognition.Component.ModelExtension

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The literal seed of order eight is nontrivial. -/
theorem seed_nontrivial (d : LocalSetup T L V V₁ V₂ V₃ M G₁) : V₃ ≠ ⊥ := by
  intro he
  have hc := d.seed_card
  rw [he, card_bot] at hc
  omega

/-- The larger conjugate span used for the critical actors is elementary
abelian, as a subgroup of the original abelian full span. -/
theorem vh_elementary (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M) :
    IsElementaryAbelian 2 (Source.VH H V) := by
  let := d.span_elementary
  exact IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)

omit [Finite G] in
/-- The Sylow subgroup in the partition argument is the restriction of the
original ambient Sylow, with its exact subgroup-of equality. -/
theorem source_sylow
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M) :
    ∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H :=
  ⟨T.subtype (le_sup_right.trans hH.1.2), rfl⟩

omit [Finite G] in
/-- The original seed commutator supplies the generation field of `Earlier`
once the actual earlier containment L₁ ≤ K has been proved. -/
theorem source_generated (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hLK : sourceOne L T V₁ ≤ K)
    (hseed : ⁅V₃, sourceOne L T V₁⁆ = V₃) :
    Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ := by
  let := hKn
  exact FieldComponents.UH_eq_commutator_of_seed H K (sourceOne L T V₁) V₃
    hKH hLK hseed.symm

/-- The component marking and the actual Sylow supplement construct all
three structural consequences used for faithful source sections. -/
theorem source_structure
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    generalizedFitting (Source.Hstar H) = Source.starImage H K ∧
      centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥ ∧
      ∀ N : Subgroup (Source.Hstar H),
        N.Normal → N ≠ ⊥ → Source.starImage H K ≤ N := by
  let := LocalGeometry.starImage_normal H K hKn
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let a := LocalGeometry.starAlternatingEquiv H K hKH hK e
  let : IsSimpleGroup (Source.starImage H K) := a.isSimpleGroup
  have ha : ¬ IsMulCommutative (Source.starImage H K) := by
    intro hh
    let := hh
    have hc : IsMulCommutative (alternatingGroup (Fin 7)) :=
      ⟨⟨fun x y => a.symm.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
    have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp hc
    norm_num at hh
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have htwo : IsPGroup 2 (Source.starImage H (T : Subgroup G)) :=
    (T.isPGroup'.of_equiv (subgroupOfEquivOfLe hTH).symm).map _
  have hsup : Source.starImage H K ⊔ Source.starImage H (T : Subgroup G) = ⊤ := by
    rw [← LocalGeometry.starImage_sup H K (T : Subgroup G) hKH hTH,
      hKT, LocalGeometry.starImage_self]
  exact FieldComponents.Hstar_structure_of_simple_component H K ha
    (LocalGeometry.quotient_two_of_sup _ _ htwo hsup)

/-- Apply the constructed monolith to the two literal module sections.
The rank-one actor and noncentrality premises are exactly those of 13.8.23;
faithfulness, both transvection codimensions, and fixed-vector lifting follow. -/
theorem source_rank_one_sections
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (W : Subrepresentation ρ) (A : Subgroup (Source.Hstar H))
    (hKW : ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule,
      W.toRepresentation k w ≠ w)
    (hKQ : ∃ k ∈ Source.starImage H K,
      ∃ q : Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule,
        W.quotientRepresentation k q ≠ q)
    (hA : A ≠ ⊥) (hrank : rank A = 1)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    Function.Injective W.toRepresentation ∧ Function.Injective W.quotientRepresentation ∧
      fixedCodim W.toRepresentation A = 1 ∧ fixedCodim W.quotientRepresentation A = 1 ∧
      fixedCodim ρ A = 2 ∧
      (fixedSpace ρ A).map W.toSubmodule.mkQ = fixedSpace W.quotientRepresentation A := by
  exact rank_one_faithful_sections ρ W (Source.starImage H K) A
    (source_structure hH hKH hK hKn hKT e).2.2 hKW hKQ hA hrank hbound

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
