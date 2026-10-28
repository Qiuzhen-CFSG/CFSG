module
public import Theory.GroupTheory.IndexTwoOmegaDiagonal

/-!
# Recovering an index-two omega-center from an exchanged pair

If two disjoint exchanged subgroups of the omega-center of S contain the
omega-center of an index-two overgroup T, their product is all of the
omega-center of S. The norm x xᵗ is central in T; its unique two-factor
decomposition lets us correct x by a factor to obtain a T-fixed element.

This supplies the center comparison in Aschbacher--Smith 15.1.29,
printed pp.1103--1104, retaining the actual conjugation and embeddings.
-/

public section

open Subgroup Stellmacher
open scoped IsMulCommutative

/-- In an index-two extension an exchanged direct pair containing all central
involutions is the entire omega-center of the subgroup. -/
theorem Subgroup.omegaCenter_eq_exchanged_pair {G : Type*} [Group G]
    (S T A : Subgroup G) (hST : S ≤ T) (hi : S.relIndex T = 2)
    (t : G) (ht : t ∈ T) (htS : t ∉ S)
    (hA : A ≤ omegaOneCenterAmbient S)
    (hdis : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hZ : omegaOneCenterAmbient T ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) :
    omegaOneCenterAmbient S = A ⊔ A.map (MulAut.conj t).toMonoidHom := by
  let W := omegaOneCenterAmbient S
  let f := (MulAut.conj t).toMonoidHom
  have hSn : T ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp (normal_of_index_eq_two hi)
  have hfW : W.map f = W := by
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective]
    exact congrArg omegaOneCenterAmbient (mem_normalizer_iff_map_conj_eq.mp (hSn ht))
  have hBW : A.map f ≤ W := (map_mono hA).trans_eq hfW
  have habW : A ⊔ A.map f ≤ W := sup_le hA hBW
  have hcomm (x y : G) (hx : x ∈ W) (hy : y ∈ W) : Commute x y := by
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hy).2.2 x
      ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hf2 (x : G) (hx : x ∈ W) : f (f x) = x := by
    have ht2 : t^2 ∈ S := (S.subgroupOf T).sq_mem_of_index_two hi ⟨t,ht⟩
    have hc := ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2 (t^2) ht2
    change t*(t*x*t⁻¹)*t⁻¹ = x
    calc
      t*(t*x*t⁻¹)*t⁻¹ = t^2*x*(t^2)⁻¹ := by simp only [pow_two]; group
      _ = x := by rw [hc]; group
  have fixed_mem (x : G) (hx : x ∈ W) (hf : f x = x) :
      x ∈ omegaOneCenterAmbient T := by
    obtain ⟨hxS,hx2,hxC⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hx
    have hc : (⟨x,hST hxS⟩ : T) ∈ center T := by
      apply mem_center_of_commute_index_two (S.subgroupOf T) hi ⟨t,ht⟩ htS
      · intro s hs
        exact Subtype.ext (hxC s hs).symm
      · apply Subtype.ext
        exact ((mul_inv_eq_iff_eq_mul).mp hf).symm
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hST hxS,hx2,fun y hy => congrArg Subtype.val (mem_center_iff.mp hc ⟨y,hy⟩)⟩
  apply le_antisymm _ habW
  intro x hx
  have hfx : f x ∈ W := hfW ▸ mem_map_of_mem f hx
  have hn := indexTwo_diagonal_mem_omegaCenter S T hST hi t ht htS x hx (hcomm x (f x) hx hfx)
  have hnA := hZ hn
  have hBA : A.map f ≤ normalizer (A : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro b hb a ha
    exact (hcomm a b (hA ha) (hBW hb)).eq
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hBA] at hnA
  obtain ⟨a,ha,b,hb,he⟩ := hnA
  change a*b = x*f x at he
  obtain ⟨c,hc,rfl⟩ := hb
  have hnormfixed : f (x*f x) = x*f x := by
    rw [map_mul,hf2 x hx]
    exact (hcomm x (f x) hx hfx).eq.symm
  have he' : f a*c = a*f c := by
    calc
      f a*c = f (a*f c) := by rw [map_mul,hf2 c (hA hc)]
      _ = x*f x := by rw [he,hnormfixed]
      _ = a*f c := he.symm
  have hac : a⁻¹*c = f c*(f a)⁻¹ := by
    have hcomm' := hcomm (f a) c (hBW (mem_map_of_mem f ha)) (hA hc)
    calc
      a⁻¹*c = a⁻¹*(f a*c)*(f a)⁻¹ := by rw [hcomm'.eq]; group
      _ = f c*(f a)⁻¹ := by rw [he']; group
  have hac1 : a⁻¹*c = 1 := by
    apply mem_bot.mp
    rw [←hdis]
    exact ⟨A.mul_mem (A.inv_mem ha) hc, hac ▸
      (A.map f).mul_mem (mem_map_of_mem f hc) ((A.map f).inv_mem (mem_map_of_mem f ha))⟩
  have hca : c = a := (inv_mul_eq_one.mp hac1).symm
  subst c
  have hxa : f (x*a⁻¹) = x*a⁻¹ := by
    rw [map_mul,map_inv]
    have he1 : f x = x⁻¹*a*f a := by
      calc
        f x = x⁻¹*(x*f x) := by group
        _ = x⁻¹*(a*f a) := by rw [he]
        _ = x⁻¹*a*f a := by group
    rw [he1]
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.1)
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using ((mem_omegaOneCenterAmbient_iff _ _).mp (hA ha)).2.1)
    simp only [hxinv,hainv,mul_inv_cancel_right]
  have hfix := fixed_mem (x*a⁻¹) (W.mul_mem hx (W.inv_mem (hA ha))) hxa
  have hh := (A ⊔ A.map f).mul_mem (hZ hfix) (mem_sup_left ha)
  simpa only [inv_mul_cancel_right] using hh
