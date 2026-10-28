module

public import Theory.Representation.G2BinaryIsotropicThree.Basic

/-!
# Normalization of an isotropic three-space through the first vector

Projection to the four middle coordinates splits off the first line. Thus an
isotropic three-space through the first vector gives a two-dimensional binary
plane. A basis of that plane is covered by the fifteen checked pairs. This
connects the finite certificate to arbitrary actual submodules.

Source: Aschbacher–Smith 13.3.12(3), printed p.890.
-/

@[expose] public section

open Atlas.SplitOctonion Module Submodule
namespace Atlas.G2.Natural.BinaryIsotropicThree
open BinaryNondegeneratePlane
abbrev Four := Certificate.Four

def middle : W →ₗ[K] Four where
  toFun v := ![v 1,v 2,v 3,v 4]
  map_add' x y := by ext i;fin_cases i <;> simp
  map_smul' a x := by ext i;fin_cases i <;> simp

def embed : Four →ₗ[K] W where
  toFun := Certificate.embed
  map_add' x y := by ext i;fin_cases i <;> simp [Certificate.embed]
  map_smul' a x := by ext i;fin_cases i <;> simp [Certificate.embed]

theorem first_perp_last_zero (P : Submodule K W) (hfirst : firstVector∈P)
    (hi : ∀v∈P,∀w∈P,form v w=0) {v : W} (hv : v∈P) : v 5=0 := by
  simpa [form_apply,firstVector] using hi firstVector hfirst v hv

theorem embed_middle_decomposition (v : W) (h5 : v 5=0) :
    v=v 0 • firstVector+embed (middle v) := by
  ext i
  fin_cases i <;> simp [firstVector,embed,middle,Certificate.embed,h5]

theorem embed_image_mem (P : Submodule K W) (hfirst : firstVector∈P)
    (hi : ∀v∈P,∀w∈P,form v w=0) {x : Four} (hx : x∈P.map middle) : embed x∈P := by
  obtain ⟨v,hv,rfl⟩ := hx
  have hd := embed_middle_decomposition v (first_perp_last_zero P hfirst hi hv)
  have he : embed (middle v)=v-v 0 • firstVector := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hd.symm
  rw [he]
  exact P.sub_mem hv (P.smul_mem _ hfirst)

noncomputable def middleSplit (P : Submodule K W) (hfirst : firstVector∈P)
    (hi : ∀v∈P,∀w∈P,form v w=0) : P≃ₗ[K](K×P.map middle) where
  toFun v := (v.val 0,⟨middle v.val,mem_map_of_mem v.property⟩)
  invFun z := ⟨z.1 •firstVector+embed z.2.val,
    P.add_mem (P.smul_mem _ hfirst) (embed_image_mem P hfirst hi z.2.property)⟩
  left_inv v := Subtype.ext (embed_middle_decomposition v.val
    (first_perp_last_zero P hfirst hi v.property)).symm
  right_inv z := by
    apply Prod.ext
    · simp [firstVector,embed,Certificate.embed]
    · apply Subtype.ext
      ext i
      fin_cases i <;> simp [middle,firstVector,embed,Certificate.embed]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (map_add _ _ _)
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (map_smul _ _ _)

theorem finrank_middle (P : Submodule K W) (hfirst : firstVector∈P)
    (hi : ∀v∈P,∀w∈P,form v w=0) (hd : finrank K P=3) : finrank K (P.map middle)=2 := by
  have h := (middleSplit P hfirst hi).finrank_eq
  rw [hd,Module.finrank_prod,Module.finrank_self] at h
  omega

def markedPlane (i : Fin 15) : Submodule K W :=
  span K {firstVector,embed (Certificate.left i),embed (Certificate.right i)}

private theorem embed_mem_markedPlane (i : Fin 15) {x : Four}
    (hx : Certificate.inPair (Certificate.left i) (Certificate.right i) x) :
    embed x∈markedPlane i := by
  rcases hx with rfl|rfl|rfl|rfl
  · simp
  · exact subset_span (by simp)
  · exact subset_span (by simp)
  · rw [map_add]
    exact (markedPlane i).add_mem (subset_span (by simp)) (subset_span (by simp))

theorem exists_markedPlane (P : Submodule K W) (hfirst : firstVector∈P)
    (hi : ∀v∈P,∀w∈P,form v w=0) (hd : finrank K P=3) :
    ∃i,P≤markedPlane i := by
  let Q := P.map middle
  let b := Module.finBasisOfFinrankEq K Q (finrank_middle P hfirst hi hd)
  let x := (b 0).val
  let y := (b 1).val
  have hx : x≠0 := by
    intro hh
    exact b.ne_zero 0 (Subtype.ext hh)
  have hy : y≠0 := by
    intro hh
    exact b.ne_zero 1 (Subtype.ext hh)
  have hxy : x≠y := by
    intro hh
    have h := b.injective (Subtype.ext hh)
    exact (by decide : (0:Fin 2)≠1) h
  have hpair : Certificate.pairing x y=0 := by
    have h := hi (embed x) (embed_image_mem P hfirst hi (b 0).property)
      (embed y) (embed_image_mem P hfirst hi (b 1).property)
    simpa [form_apply,embed,Certificate.embed,Certificate.pairing] using h
  obtain ⟨i,hix,hiy⟩ := Certificate.coverage x y ⟨hx,hy,hxy,hpair⟩
  refine ⟨i,?_⟩
  intro v hv
  let q : Q := ⟨middle v,mem_map_of_mem hv⟩
  have hq : middle v=(b.repr q 0)•x+(b.repr q 1)•y := by
    have h := congrArg Subtype.val (b.sum_repr q)
    simpa only [Fin.sum_univ_two,Submodule.coe_add,Submodule.coe_smul] using h.symm
  rw [embed_middle_decomposition v (first_perp_last_zero P hfirst hi hv),hq,
    map_add,map_smul,map_smul]
  exact (markedPlane i).add_mem
    ((markedPlane i).smul_mem _ (subset_span (by simp)))
    ((markedPlane i).add_mem
      ((markedPlane i).smul_mem _ (embed_mem_markedPlane i hix))
      ((markedPlane i).smul_mem _ (embed_mem_markedPlane i hiy)))
end Atlas.G2.Natural.BinaryIsotropicThree
