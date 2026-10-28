module

public import Theory.GroupTheory.RegularKernelConjugacy

/-!
# Prescribed local sections inside a conjugate global section

Regular kernel coordinates on one quotient subgroup conjugate a prescribed
local section onto the restriction of an existing global section. The
conjugating element lies in the full original kernel and the comparison
keeps both quotient maps literally.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {E P A : Type*} [Group E] [Group P] [CommGroup A]

/-- A specified local section is contained in a kernel conjugate of the
specified global section when the restricted kernel is regular. -/
theorem local_section_conjugate_of_regular_kernel
    (q : E →* P) (U : Subgroup P) (e : q.ker ≃* (U → A))
    (he : ∀ (g : U.comap q) (v : q.ker) (x : U),
      e (MulAut.conjNormal (g:E) v) x=e v ((⟨q g,g.property⟩:U)⁻¹*x))
    (s : P →* E) (hs : ∀ g,q (s g)=g)
    (r : U →* E) (hr : ∀ g,q (r g)=(g:P)) :
    ∃ v : q.ker, ∀ g : U, r g=(v:E)*s (g:P)*(v:E)⁻¹ := by
  let H := U.comap q
  let f : H →* U := {
    toFun g := ⟨q g,g.property⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' g h := Subtype.ext (map_mul q (g:E) (h:E)) }
  have hk : f.ker=q.ker.subgroupOf H := by
    ext g
    change (⟨q g,g.property⟩:U)=1 ↔ q (g:E)=1
    exact Subtype.ext_iff
  have hle : q.ker≤H := fun g hg => by
    change q g∈U
    rw [show q g=1 from hg]
    exact U.one_mem
  let ek : f.ker ≃* q.ker :=
    (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe hle)
  let r' : U →* H := r.codRestrict H (fun g => by
    change q (r g)∈U
    rw [hr]
    exact g.property)
  let s' : U →* H := (s.comp U.subtype).codRestrict H (fun g => by
    change q (s (g:P))∈U
    rw [hs]
    exact g.property)
  have hact (g : H) (v : f.ker) :
      ek (MulAut.conjNormal g v)=MulAut.conjNormal (g:E) (ek v) := by
    apply Subtype.ext
    rfl
  obtain ⟨v,hv⟩ := sections_conjugate_of_regular_kernel f (ek.trans e) (by
    intro g v x
    change e (ek (MulAut.conjNormal g v)) x=e (ek v) ((f g)⁻¹*x)
    rw [hact]
    exact he g (ek v) x) r' s'
    (fun g => Subtype.ext (hr g)) (fun g => Subtype.ext (hs (g:P)))
  refine ⟨ek v,fun g => ?_⟩
  exact congrArg (fun z : H => (z:E)) (hv g)

end Theory.GroupTheory
