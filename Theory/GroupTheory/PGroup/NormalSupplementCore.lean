module

public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The kernel inside a normal p-group supplement

For a homomorphism on KS, where K is normalized by the two-group S,
a two-group kernel on K makes the whole kernel on KS a normal two-subgroup.
It therefore lies in O₂(KS). The proof restricts the original homomorphism
to KS and uses the normal-supplement kernel theorem.

Source application: Aschbacher--Smith, preliminary 15.2.23,
printed p.1115, refs/quasithin.pdf.
-/

public section
open Subgroup

namespace Subgroup
variable {A B : Type*} [Group A] [Group B]

theorem inf_ker_le_core_of_two_supplement (f : A →* B) (K S : Subgroup A)
    (hSK : S ≤ normalizer (K : Set A)) (hS : IsPGroup 2 S)
    (hk : IsPGroup 2 (f.comp K.subtype).ker) :
    (K ⊔ S) ⊓ f.ker ≤ (K ⊔ S).pCoreIn 2 := by
  let J := K ⊔ S
  let K' := K.subgroupOf J
  let S' := S.subgroupOf J
  let g := f.comp J.subtype
  let : K'.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hSK)
  have hgen : K' ⊔ S' = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) (show S ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hk' : IsPGroup 2 (g.comp K'.subtype).ker := by
    let j : (g.comp K'.subtype).ker →* (f.comp K.subtype).ker :=
      { toFun := fun x => ⟨⟨x.val.val.val,x.val.property⟩,x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply hk.of_injective j
    intro x y hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun z : (f.comp K.subtype).ker => ((z : K) : A)) hxy)))
  have hker := g.kernel_isPGroup_of_normal_supplement K' S' hS.comap_subtype hgen hk'
  have hc : g.ker ≤ pCore 2 J := le_sSup ⟨inferInstance,hker⟩
  intro x hx
  exact mem_map_of_mem J.subtype (hc (show (⟨x,hx.1⟩ : J) ∈ g.ker from hx.2))
end Subgroup
