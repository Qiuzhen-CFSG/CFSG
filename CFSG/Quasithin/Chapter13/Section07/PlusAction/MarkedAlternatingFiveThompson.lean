module
public import CFSG.Quasithin.ChapterB.Section04.AlternatingFiveThompson
public import CFSG.Quasithin.Chapter6.SourceDefs
public import Theory.Representation.BinaryPermutationMulAction
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Thompson fixation of the original marked A₅ modules

The original conjugation model identifies the K-action on I with the
binary deleted-permutation A₅ action. If each element of R acts on I as
an element of K, faithfulness gives a compatible even permutation action
of R. The five-point offender obstruction then makes J(R) centralize I.
The construction retains the original subgroup and quotient marking.

Source: Aschbacher–Smith 13.7.4, printed p.937, the application of B.4.2
to each I in Irr⁺(K,R₂(KT),T).
-/

public section
open Subgroup Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]

/-- Inner action on a literal A₅ module forces elementary Thompson fixation. -/
theorem thompson_centralizes_marked_a5_module
    (K I R : Subgroup G) [IsElementaryAbelian 2 I]
    (hIR : I ≤ R) (hRI : R ≤ normalizer (I : Set G))
    (hm : Chapter6.Source.IsConjugationModel K I Chapter6.Source.a5Module)
    (hinner : ∀ r : R, ∃ k : K, ∀ v : I,
      (r : G) * (v : G) * (r : G)⁻¹ = (k : G) * (v : G) * (k : G)⁻¹) :
    elementaryAbelianMaxJ R ≤ centralizer (I : Set G) := by
  classical
  obtain ⟨m,f,hf⟩ := hm
  let α : alternatingGroup (Fin 5) →* MulAut I :=
    (MulAut.congr f.symm).toMonoidHom.comp
      ((BinaryPermutation.naturalMulAction (Fin 5)).comp (alternatingGroup (Fin 5)).subtype)
  have hi : Function.Injective α := (MulAut.congr f.symm).injective.comp
    ((BinaryPermutation.naturalMulAction_injective_of_odd (Fin 5) (by decide)).comp
      (alternatingGroup (Fin 5)).subtype_injective)
  let β : R →* MulAut I := I.normalizerMonoidHom.comp (Subgroup.inclusion hRI)
  have hrange (r : R) : β r ∈ α.range := by
    obtain ⟨k,hk⟩ := hinner r
    refine ⟨m (QuotientGroup.mk' (pCore 2 K) k), ?_⟩
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    exact (hf k v).trans (hk v).symm
  let e := MonoidHom.ofInjective hi
  let qA : R →* alternatingGroup (Fin 5) :=
    e.symm.toMonoidHom.comp (β.codRestrict α.range hrange)
  let q : R →* Equiv.Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp qA
  have hq (r : R) : α (qA r) = β r :=
    MonoidHom.apply_ofInjective_symm hi (β.codRestrict α.range hrange r)
  let U := I.subgroupOf R
  let : U.Normal := normal_subgroupOf_of_le_normalizer hRI
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hIR
  let fR : U ≃* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
    (subgroupOfEquivOfLe hIR).trans f
  have hact (r : R) (v : U) :
      ((fR.symm (Multiplicative.ofAdd
        (BinaryPermutation.naturalRepresentation (Fin 5) (q r) (fR v).toAdd))) : R) =
        r * (v : R) * r⁻¹ := by
    apply Subtype.ext
    have hh := congrArg (fun a : MulAut I => ((a ((subgroupOfEquivOfLe hIR) v) : I) : G)) (hq r)
    exact hh
  have heven : (⊤ : Subgroup R).map q ≤ alternatingGroup (Fin 5) := by
    rintro a ⟨r,_,rfl⟩
    exact (qA r).property
  have hj := ChapterB.five_thompson_centralizes_of_even_action U (⊤ : Subgroup R)
    le_top q fR hact heven
  have hmap : (elementaryAbelianMaxJ (⊤ : Subgroup R)).map R.subtype =
      elementaryAbelianMaxJ R := by
    rw [← elementaryAbelianMaxJ_map_injective R.subtype R.subtype_injective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hmap]
  rintro r ⟨r,hr,rfl⟩ v hv
  exact congrArg R.subtype (hj hr ⟨v,hIR hv⟩ hv)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
