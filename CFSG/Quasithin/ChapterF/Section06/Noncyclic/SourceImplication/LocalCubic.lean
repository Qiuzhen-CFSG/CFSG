module
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ThreeResidual
public import Theory.GroupTheory.PCoreSurjective

/-!
# The intrinsic cubic quotient of a local residual

Restrict the local symmetric-three quotient to its two-residual.
Its image has order three and its kernel is a two-group. Prime-core
lifting identifies that kernel with the intrinsic two-core of the
residual. This preserves both subgroup inclusions and quotient maps.

Source: the local groups in Aschbacher–Smith, The Classification of
Quasithin Groups, F.6.2 and F.6.16, printed pp.304, 308–309.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic two-residual has cubic quotient by its intrinsic two-core. -/
theorem local_residual_quotient_card_three
    (he : Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3))) :
    Nat.card ((pResidual 2 G) ⧸ pCore 2 (pResidual 2 G)) = 3 := by
  obtain ⟨e⟩ := he
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := pResidual 2 G
  let f := q.subgroupMap R
  have hf := q.subgroupMap_surjective R
  have hcard : Nat.card (R.map q) = 3 := by
    rw [show R.map q = pResidual 2 (Equiv.Perm (Fin 3)) from
      map_pResidual_of_surjective 2 q hq]
    exact (residual_of_symmetricThree (MulEquiv.refl _)).2
  have hker : IsPGroup 2 f.ker := by
    let j : f.ker →* pCore 2 G :=
      { toFun := fun x => ⟨x.val.val, by
          apply (QuotientGroup.eq_one_iff _).mp
          apply e.injective
          exact (congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)).trans (map_one e).symm⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply pCore_isPGroup.of_injective j
    intro x y he
    have hh : x.val.val = y.val.val := congrArg (fun z : pCore 2 G => z.val) he
    exact Subtype.ext (Subtype.ext hh)
  have htwo : pCore 2 (R.map q) = ⊥ := by
    have h3 : IsPGroup 3 (R.map q) := IsPGroup.of_card (n := 1) hcard
    have hd : Disjoint (⊤ : Subgroup (R.map q)) (pCore 2 (R.map q)) :=
      (h3.to_subgroup ⊤).disjoint_of_coprime pCore_isPGroup (by decide)
    simpa using hd.symm.eq_bot_of_le le_top
  have hk : f.ker = pCore 2 R := by
    have hh := f.comap_pCore_of_ker_isPGroup hf hker
    rw [htwo] at hh
    exact hh
  exact (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)).toEquiv).trans hcard

end CFSG.Quasithin.ChapterF.Noncyclic
