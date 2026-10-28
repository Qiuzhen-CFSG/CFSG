module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
/-!
# Quasisimplicity above a centralized two-core

A local C-component containing a nonsolvable subgroup centralizing a normal
subgroup centralizes it itself. If its image above the ambient two-core has
two-rank at least two, the SQTK component theorem and a central-cover lift
make the original component quasisimple.

Source: Aschbacher–Smith, 2.4.11, printed p.531, using 1.2.1(5).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
variable {X : Type*} [Group X] [Finite X]

theorem component_centralizes_of_nonsolvable_subgroup
    (K B P : Subgroup X) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hB : ¬ Group.IsSolvable B) [P.Normal] (hBP : B ≤ centralizer (P : Set X)) :
    K ≤ centralizer (P : Set X) := by
  let C := (centralizer (P : Set X)).subgroupOf K
  have hBC : B ≤ K ⊓ centralizer (P : Set X) := le_inf hBK hBP
  by_contra hn
  have hCn : C ≠ ⊤ := fun he => hn (subgroupOf_eq_top.mp he)
  let : Group.IsSolvable C := hK.isSolvable_of_subnormal_lt_top
    (inferInstance : C.Normal).isSubnormal hCn
  let f : B →* C :=
    { toFun := fun b => ⟨⟨b,hBK b.property⟩,hBP b.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun c : C => ((c:K):X)) he)
  exact hB (Group.isSolvable_of_isSolvable_injective hf)

theorem quasisimple_of_core_centralizes_and_image_rank
    {κ : GroupClass} (hX : IsSQTK κ (X ⧸ pCore 2 X))
    (K : Subgroup X) (hK : K.IsCComponent)
    (hc : pCore 2 X ≤ centralizer (K : Set X))
    (hr : 2 ≤ primeRank 2 (K.map (QuotientGroup.mk' (pCore 2 X)))) : IsQuasisimple K := by
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 X)
  have hbar := hK.map_quotient (pCore 2 X)
  let : IsQuasisimple (K.map q) := quasisimple_of_two_le_two_rank hX
    (pCore_quotient_pCore_eq_bot 2) hbar hr
  let f := q.subgroupMap K
  have hk : f.ker ≤ center K := by
    intro k hk
    have hkQ : (k:X) ∈ pCore 2 X := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val hk)
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext ((mem_centralizer_iff.mp (hc hkQ)) l l.property)
  exact (show PerfectCentralCovering.Cover K (K.map q) from
    { toMonoidHom := f, surjective := q.subgroupMap_surjective K,
      isPerfect := hK.perfect, ker_le_center := hk }).isQuasisimple
end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
