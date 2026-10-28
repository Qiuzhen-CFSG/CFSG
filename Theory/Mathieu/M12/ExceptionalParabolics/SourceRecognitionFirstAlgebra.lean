module
public import Theory.Mathieu.M12.ExceptionalParabolics.SourceRecognitionFirst
public import Theory.GroupTheory.SymmetricFourCoxeterRecognition.TranspositionChain
public import Theory.GroupTheory.BinaryCollection
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Tauto

/-!
# Normalization of the first Mathieu endpoint's source generators

The actual six-label relations determine an elementary eight and three
transposition lifts. An adjacent product's cube lies in the eight and is
fixed by its cyclic action, hence is either one or the distinguished central
involution. Multiplying the appropriate end lift by that involution makes
both cubes trivial while preserving the remaining relations and generation.
The resulting relations identify the concrete first M₁₂ parabolic.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12.6) and the following paragraph, printed p.405.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
open Subgroup
variable {G : Type*} [Group G]

private theorem eight_cases (e f z : G)
    (he : e ^ 2 = 1) (hf : f ^ 2 = 1) (hz : z ^ 2 = 1)
    (hef : Commute e f) (hze : Commute z e) (hzf : Commute z f)
    {x : G} (hx : x ∈ closure ({e,f,z} : Set G)) :
    ∃ y ∈ ({1,e,f,e*f} : Set G), x = y ∨ x = y*z := by
  have ht : Theory.GroupTheory.BinaryCollection.triangular [e,f,z] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [← pow_two, he]; exact one_mem _
    · intro b hb
      simp at hb
      rcases hb with rfl | rfl
      · rw [hef.inv_mul_cancel]; exact subset_closure (by simp)
      · rw [hze.symm.inv_mul_cancel]; exact subset_closure (by simp)
    · rw [← pow_two, hf]; exact one_mem _
    · intro b hb
      simp at hb
      subst b
      rw [hzf.symm.inv_mul_cancel]
      exact subset_closure (by simp)
    · rw [← pow_two, hz]; exact one_mem _
    · simp
  have hset : {x : G | x ∈ [e,f,z]} = ({e,f,z} : Set G) := by ext; simp
  obtain ⟨n, hn, hn'⟩ := Theory.GroupTheory.BinaryCollection.cover [e,f,z] ht x
    (by rw [hset]; exact hx)
  have hn8 : n < 8 := hn
  rw [← hn']
  interval_cases n <;> simp [Theory.GroupTheory.BinaryCollection.product, mul_assoc]

private theorem fixed_pair_eq_one (φ : G →* G) (e f : G)
    (he : φ e = f) (hf : φ f = e*f)
    {x : G} (hx : x ∈ ({1,e,f,e*f} : Set G)) (hfix : φ x = x) : x = 1 := by
  rcases hx with h1 | hxe | hxf | hxef
  · exact h1
  · rw [hxe] at hfix ⊢
    have hfe : f = e := he.symm.trans hfix
    have hfe' : e*f = f := (hf.symm.trans (congrArg φ hfe)).trans he
    exact mul_right_cancel (b := f) (by simpa using hfe')
  · rw [hxf] at hfix ⊢
    have hef : e*f = f := hf.symm.trans hfix
    have he1 : e = 1 := mul_right_cancel (b := f) (by simpa using hef)
    have := congrArg φ he1
    simpa only [he, map_one] using this
  · rw [hxef] at hfix ⊢
    have hh : f * (e*f) = e*f := by simpa only [map_mul, he, hf] using hfix
    have hf1 : f = 1 := mul_right_cancel (b := e*f) (by simpa using hh)
    have := congrArg φ hf1
    simpa only [hf, map_one] using this

/-- A cubic cycling the two noncentral basis directions fixes only the
distinguished central line in the actual elementary eight. -/
theorem fixed_eight_eq_one_or_central (φ : G →* G) (e f z : G)
    (he : e ^ 2 = 1) (hf : f ^ 2 = 1) (hz : z ^ 2 = 1)
    (hef : Commute e f) (hze : Commute z e) (hzf : Commute z f)
    (hφe : φ e = f) (hφf : φ f = e*f) (hφz : φ z = z)
    {x : G} (hx : x ∈ closure ({e,f,z} : Set G)) (hfix : φ x = x) :
    x = 1 ∨ x = z := by
  obtain ⟨y, hy, hxy | hxy⟩ := eight_cases e f z he hf hz hef hze hzf hx
  · left
    rw [hxy] at hfix ⊢
    exact fixed_pair_eq_one φ e f hφe hφf hy hfix
  · right
    rw [hxy, map_mul, hφz] at hfix
    have hy1 := fixed_pair_eq_one φ e f hφe hφf hy (mul_right_cancel hfix)
    rw [hxy, hy1, one_mul]


structure FirstBaseRelations (e f A B C z : G) : Prop where
  e_sq : e ^ 2 = 1
  f_sq : f ^ 2 = 1
  A_sq : A ^ 2 = 1
  B_sq : B ^ 2 = 1
  C_sq : C ^ 2 = 1
  z_sq : z ^ 2 = 1
  ef : Commute e f
  ze : Commute z e
  zf : Commute z f
  zA : Commute z A
  zB : Commute z B
  zC : Commute z C
  AC : (A * C) ^ 2 = z
  Ae : A * e * A⁻¹ = f
  Af : A * f * A⁻¹ = e
  Be : B * e * B⁻¹ = e
  Bf : B * f * B⁻¹ = e * f
  Ce : C * e * C⁻¹ = z * f
  Cf : C * f * C⁻¹ = z * e


private theorem twist_conj (z A e : G) (hzA : Commute z A) (hze : Commute z e) :
    (z*A)*e*(z*A)⁻¹ = A*e*A⁻¹ := by
  calc
    _ = A*(z*e*z⁻¹)*A⁻¹ := by rw [hzA.eq]; group
    _ = A*e*A⁻¹ := by rw [hze.eq, mul_assoc e, mul_inv_cancel, mul_one]

theorem FirstBaseRelations.twistA {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z) : FirstBaseRelations e f (z*A) B C z where
  e_sq := r.e_sq
  f_sq := r.f_sq
  A_sq := by rw [r.zA.mul_pow, r.z_sq, r.A_sq, one_mul]
  B_sq := r.B_sq
  C_sq := r.C_sq
  z_sq := r.z_sq
  ef := r.ef
  ze := r.ze
  zf := r.zf
  zA := (Commute.refl z).mul_right r.zA
  zB := r.zB
  zC := r.zC
  AC := by rw [mul_assoc, (r.zA.mul_right r.zC).mul_pow, r.z_sq, one_mul, r.AC]
  Ae := by rw [twist_conj z A e r.zA r.ze, r.Ae]
  Af := by rw [twist_conj z A f r.zA r.zf, r.Af]
  Be := r.Be
  Bf := r.Bf
  Ce := r.Ce
  Cf := r.Cf

theorem FirstBaseRelations.twistC {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z) : FirstBaseRelations e f A B (z*C) z where
  e_sq := r.e_sq
  f_sq := r.f_sq
  A_sq := r.A_sq
  B_sq := r.B_sq
  C_sq := by rw [r.zC.mul_pow, r.z_sq, r.C_sq, one_mul]
  z_sq := r.z_sq
  ef := r.ef
  ze := r.ze
  zf := r.zf
  zA := r.zA
  zB := r.zB
  zC := (Commute.refl z).mul_right r.zC
  AC := by
    rw [← mul_assoc A, r.zA.symm.eq, mul_assoc,
      (r.zA.mul_right r.zC).mul_pow, r.z_sq, one_mul, r.AC]
  Ae := r.Ae
  Af := r.Af
  Be := r.Be
  Bf := r.Bf
  Ce := by rw [twist_conj z C e r.zC r.ze, r.Ce]
  Cf := by rw [twist_conj z C f r.zC r.zf, r.Cf]

private theorem conj_prod (A B x : G) :
    (A*B)*x*(A*B)⁻¹ = A*(B*x*B⁻¹)*A⁻¹ := by group

theorem FirstBaseRelations.cube_AB {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z)
    (hm : (A*B)^3 ∈ closure ({e,f,z} : Set G)) :
    (A*B)^3 = 1 ∨ (A*B)^3 = z := by
  let φ := (MulAut.conj (A*B)).toMonoidHom
  apply fixed_eight_eq_one_or_central φ e f z r.e_sq r.f_sq r.z_sq r.ef r.ze r.zf
  · change (A*B)*e*(A*B)⁻¹=f
    rw [conj_prod, r.Be, r.Ae]
  · change (A*B)*f*(A*B)⁻¹=e*f
    rw [conj_prod, r.Bf]
    have hh := (MulAut.conj A).map_mul e f
    change A*(e*f)*A⁻¹=(A*e*A⁻¹)*(A*f*A⁻¹) at hh
    rw [hh, r.Ae, r.Af, r.ef.symm.eq]
  · change (A*B)*z*(A*B)⁻¹=z
    rw [(r.zA.mul_right r.zB).symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  · exact hm
  · change (A*B)*(A*B)^3*(A*B)⁻¹=(A*B)^3
    rw [(Commute.self_pow (A*B) 3).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem FirstBaseRelations.cube_BC {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z)
    (hm : (B*C)^3 ∈ closure ({e,f,z} : Set G)) :
    (B*C)^3 = 1 ∨ (B*C)^3 = z := by
  let q := z*e*f
  let φ := (MulAut.conj (B*C)).toMonoidHom
  have hze2 : (z*e)*(z*e)=1 := by
    rw [← pow_two, r.ze.mul_pow, r.z_sq, r.e_sq, one_mul]
  have he2 : e*e=1 := by simpa only [pow_two] using r.e_sq
  have hq2 : q^2=1 := by
    change (z*e*f)^2=1
    rw [(r.zf.mul_left r.ef).mul_pow, r.ze.mul_pow, r.z_sq, r.e_sq, r.f_sq]
    simp
  have heq : e*q=z*f := by
    change e*(z*e*f)=z*f
    calc
      _ = (e*z)*(e*f) := by group
      _ = (z*e)*(e*f) := by rw [r.ze.symm.eq]
      _ = z*f := by rw [mul_assoc, ← mul_assoc e, he2, one_mul]
  have hfle : f ∈ closure ({e,q,z} : Set G) := by
    have hh : z*e*q=f := by
      change z*e*(z*e*f)=f
      rw [← mul_assoc, hze2, one_mul]
    rw [← hh]
    exact mul_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
      (subset_closure (by simp))
  have hm' : (B*C)^3 ∈ closure ({e,q,z} : Set G) := by
    apply (show closure ({e,f,z} : Set G) ≤ closure ({e,q,z} : Set G) from ?_) hm
    apply (closure_le _).mpr
    rintro x (rfl | rfl | rfl)
    · exact subset_closure (by simp)
    · exact hfle
    · exact subset_closure (by simp)
  have hφe : φ e = q := by
    change (B*C)*e*(B*C)⁻¹=q
    rw [conj_prod, r.Ce]
    have hh := (MulAut.conj B).map_mul z f
    change B*(z*f)*B⁻¹=(B*z*B⁻¹)*(B*f*B⁻¹) at hh
    rw [hh, r.Bf]
    have hz : B*z*B⁻¹=z := by rw [r.zB.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hz]
    exact (mul_assoc z e f).symm
  have hφf : φ f = z*e := by
    change (B*C)*f*(B*C)⁻¹=z*e
    rw [conj_prod, r.Cf]
    have hh := (MulAut.conj B).map_mul z e
    change B*(z*e)*B⁻¹=(B*z*B⁻¹)*(B*e*B⁻¹) at hh
    rw [hh, r.Be]
    have hz : B*z*B⁻¹=z := by rw [r.zB.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hz]
  have hφz : φ z = z := by
    change (B*C)*z*(B*C)⁻¹=z
    rw [(r.zB.mul_right r.zC).symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  apply fixed_eight_eq_one_or_central φ e q z r.e_sq hq2 r.z_sq
    ((r.ze.symm.mul_right (Commute.refl e)).mul_right r.ef) r.ze
    (((Commute.refl z).mul_right r.ze).mul_right r.zf) hφe
  · change φ (z*e*f)=e*q
    rw [map_mul, map_mul, hφz, hφe, hφf]
    calc
      z*q*(z*e) = z*((z*e)*(f*(z*e))) := by dsimp [q]; group
      _ = z*((z*e)*((z*e)*f)) := by rw [(r.zf.mul_left r.ef).symm.eq]
      _ = z*f := by rw [← mul_assoc (z*e), hze2, one_mul]
      _ = e*q := heq.symm
  · exact hφz
  · exact hm'
  · change (B*C)*(B*C)^3*(B*C)⁻¹=(B*C)^3
    rw [(Commute.self_pow (B*C) 3).eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem closure_twistA (e f A B C z : G) :
    closure ({e,f,z*A,B,C,z} : Set G) = closure ({e,f,A,B,C,z} : Set G) := by
  apply le_antisymm <;> apply (closure_le _).mpr
  · rintro x (h1 | h2 | h3 | h4 | h5 | h6)
    all_goals subst x
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
  · rintro x (h1 | h2 | h3 | h4 | h5 | h6)
    all_goals subst x
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · have hh := mul_mem (inv_mem (subset_closure (by simp) :
          z ∈ closure ({e,f,z*A,B,C,z} : Set G)))
          (subset_closure (by simp) : z*A ∈ closure ({e,f,z*A,B,C,z} : Set G))
      change A ∈ closure ({e,f,z*A,B,C,z} : Set G)
      simpa only [inv_mul_cancel_left] using hh
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)

private theorem closure_twistC (e f A B C z : G) :
    closure ({e,f,A,B,z*C,z} : Set G) = closure ({e,f,A,B,C,z} : Set G) := by
  have hleft : ({e,f,A,B,z*C,z} : Set G) = {e,f,z*C,B,A,z} := by ext; simp; tauto
  have hright : ({e,f,A,B,C,z} : Set G) = {e,f,C,B,A,z} := by ext; simp; tauto
  rw [hleft, hright]
  exact closure_twistA e f C B A z

/-- Central involution twists remove the two cubic defects while preserving
every conjugation formula and the generated source subgroup. -/
theorem FirstBaseRelations.normalize {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z)
    (hAB : (A*B)^3 ∈ closure ({e,f,z} : Set G))
    (hBC : (B*C)^3 ∈ closure ({e,f,z} : Set G)) :
    ∃ A' C', FirstBaseRelations e f A' B C' z ∧
      (A'*B)^3=1 ∧ (B*C')^3=1 ∧
      closure ({e,f,A',B,C',z} : Set G) = closure ({e,f,A,B,C,z} : Set G) := by
  have hz3 : z^3=z := by rw [pow_succ, r.z_sq, one_mul]
  obtain ⟨A', r', hA', hgen⟩ : ∃ A', FirstBaseRelations e f A' B C z ∧
      (A'*B)^3=1 ∧
      closure ({e,f,A',B,C,z} : Set G) = closure ({e,f,A,B,C,z} : Set G) := by
    rcases r.cube_AB hAB with hh | hh
    · exact ⟨A, r, hh, rfl⟩
    · refine ⟨z*A, r.twistA, ?_, closure_twistA e f A B C z⟩
      rw [mul_assoc, (r.zA.mul_right r.zB).mul_pow, hz3, hh, ← pow_two, r.z_sq]
  rcases r.cube_BC hBC with hh | hh
  · exact ⟨A', C, r', hA', hh, hgen⟩
  · refine ⟨A', z*C, r'.twistC, hA', ?_, (closure_twistC e f A' B C z).trans hgen⟩
    rw [← mul_assoc B, r.zB.symm.eq, mul_assoc,
      (r.zB.mul_right r.zC).mul_pow, hz3, hh, ← pow_two, r.z_sq]

theorem FirstBaseRelations.e_ne_f {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z) (hz : z ≠ 1) : e ≠ f := by
  intro heq
  have hf1 : f=1 := by
    apply (MulAut.conj B).injective
    change B*f*B⁻¹=B*1*B⁻¹
    rw [r.Bf, ← heq, ← pow_two, r.e_sq]
    simp
  have he1 : e=1 := heq.trans hf1
  have hh := r.Ce
  rw [he1, hf1, mul_one, mul_inv_cancel, mul_one] at hh
  exact hz hh.symm

theorem FirstBaseRelations.f_ne_z {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z) (hz : z ≠ 1) : f ≠ z := by
  intro heq
  have hez : e=z := by
    rw [← r.Af, heq, r.zA.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hh := r.Bf
  rw [heq, hez, r.zB.symm.eq, mul_assoc, mul_inv_cancel, mul_one,
    ← pow_two, r.z_sq] at hh
  exact hz hh

theorem FirstBaseRelations.core_commute {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z)
    {x y : G} (hx : x ∈ closure ({e,f,z} : Set G))
    (hy : y ∈ closure ({e,f,z} : Set G)) : Commute x y := by
  let E := closure ({e,f,z} : Set G)
  have hi : IsMulCommutative E := Subgroup.isMulCommutative_closure (by
    rintro x (h1 | h2 | h3) y (h4 | h5 | h6)
    all_goals (subst x; subst y)
    all_goals first | rfl | exact r.ef.eq | exact r.ef.symm.eq |
      exact r.ze.eq | exact r.ze.symm.eq | exact r.zf.eq | exact r.zf.symm.eq)
  exact congrArg Subtype.val (isMulCommutative_iff.mp hi (⟨x,hx⟩ : E) (⟨y,hy⟩ : E))

theorem FirstBaseRelations.core_square {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z)
    {x : G} (hx : x ∈ closure ({e,f,z} : Set G)) : x^2=1 := by
  obtain ⟨y, hy, hxy | hxy⟩ := eight_cases e f z r.e_sq r.f_sq r.z_sq r.ef r.ze r.zf hx
  · rw [hxy]
    rcases hy with h1 | he | hf | hef
    · rw [h1, one_pow]
    · rw [he, r.e_sq]
    · rw [hf, r.f_sq]
    · rw [hef, r.ef.mul_pow, r.e_sq, r.f_sq, one_mul]
  · rw [hxy]
    rcases hy with h1 | he | hf | hef
    · rw [h1, one_mul, r.z_sq]
    · rw [he, r.ze.symm.mul_pow, r.e_sq, r.z_sq, one_mul]
    · rw [hf, r.zf.symm.mul_pow, r.f_sq, r.z_sq, one_mul]
    · rw [hef, (r.ze.symm.mul_left r.zf.symm).mul_pow, r.ef.mul_pow,
        r.e_sq, r.f_sq, r.z_sq, one_mul, one_mul]

private theorem conjugation_eq_of_equal_image (φ : G →* Equiv.Perm (Fin 4))
    {A B x : G} (he : φ A = φ B)
    (hcomm : ∀ y ∈ φ.ker, Commute y x) : A*x*A⁻¹=B*x*B⁻¹ := by
  have hm : B⁻¹*A ∈ φ.ker := by
    change φ (B⁻¹*A)=1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hh : (B⁻¹*A)*x*(B⁻¹*A)⁻¹=x := by
    rw [(hcomm _ hm).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hh' := congrArg (fun u => B*u*B⁻¹) hh
  convert hh' using 1
  group

theorem FirstBaseRelations.image_distinct {e f A B C z : G}
    (r : FirstBaseRelations e f A B C z) (hz : z ≠ 1)
    (φ : G →* Equiv.Perm (Fin 4)) (hker : φ.ker = closure ({e,f,z} : Set G)) :
    φ A ≠ φ B ∧ φ B ≠ φ C ∧ φ A ≠ φ C := by
  have hcen (x : G) (hx : x ∈ closure ({e,f,z} : Set G)) :
      ∀ y ∈ φ.ker, Commute y x := by
    intro y hy
    rw [hker] at hy
    exact r.core_commute hy hx
  refine ⟨?_,?_,?_⟩
  · intro hh
    have hc := conjugation_eq_of_equal_image φ hh (hcen e (subset_closure (by simp)))
    rw [r.Ae, r.Be] at hc
    exact r.e_ne_f hz hc.symm
  · intro hh
    have hc := conjugation_eq_of_equal_image φ hh (hcen f (subset_closure (by simp)))
    rw [r.Bf, r.Cf, r.ze.eq] at hc
    exact r.f_ne_z hz (mul_left_cancel hc)
  · intro hh
    have hm : A*C ∈ φ.ker := by
      change φ (A*C)=1
      rw [map_mul, hh, ← pow_two, ← map_pow, r.C_sq, map_one]
    rw [hker] at hm
    exact hz (r.AC.symm.trans (r.core_square hm))

theorem generation_of_image_and_kernel {e f A B C z : G}
    (φ : G →* Equiv.Perm (Fin 4)) (hker : φ.ker = closure ({e,f,z} : Set G))
    (hgen : closure ({φ A, φ B, φ C} : Set (Equiv.Perm (Fin 4))) = ⊤) :
    closure ({e,f,A,B,C,z} : Set G) = ⊤ := by
  let K := closure ({e,f,A,B,C,z} : Set G)
  have hE : φ.ker ≤ K := by
    rw [hker]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hmap : K.map φ = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (closure_le _).mpr
    rintro x (h1 | h2 | h3)
    all_goals subst x
    · exact mem_map_of_mem _ (subset_closure (by simp))
    · exact mem_map_of_mem _ (subset_closure (by simp))
    · exact mem_map_of_mem _ (subset_closure (by simp))
  apply top_unique
  intro x _
  obtain ⟨y, hy, hxy⟩ := (show φ x ∈ K.map φ from hmap ▸ mem_top _)
  have hh : y⁻¹*x ∈ φ.ker := by
    change φ (y⁻¹*x)=1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hh' := K.mul_mem hy (hE hh)
  simpa only [mul_inv_cancel_left] using hh'

theorem FirstBaseRelations.of_injective {H : Type*} [Group H]
    (φ : G →* H) (hinj : Function.Injective φ) {e f A B C z : G}
    (r : FirstBaseRelations (φ e) (φ f) (φ A) (φ B) (φ C) (φ z)) :
    FirstBaseRelations e f A B C z where
  e_sq := by
    apply hinj
    simpa only [map_pow, map_one] using r.e_sq
  f_sq := by
    apply hinj
    simpa only [map_pow, map_one] using r.f_sq
  A_sq := by
    apply hinj
    simpa only [map_pow, map_one] using r.A_sq
  B_sq := by
    apply hinj
    simpa only [map_pow, map_one] using r.B_sq
  C_sq := by
    apply hinj
    simpa only [map_pow, map_one] using r.C_sq
  z_sq := by
    apply hinj
    simpa only [map_pow, map_one] using r.z_sq
  ef := by
    apply hinj
    simpa only [map_mul] using r.ef.eq
  ze := by
    apply hinj
    simpa only [map_mul] using r.ze.eq
  zf := by
    apply hinj
    simpa only [map_mul] using r.zf.eq
  zA := by
    apply hinj
    simpa only [map_mul] using r.zA.eq
  zB := by
    apply hinj
    simpa only [map_mul] using r.zB.eq
  zC := by
    apply hinj
    simpa only [map_mul] using r.zC.eq
  AC := by
    apply hinj
    simpa only [map_pow, map_mul] using r.AC
  Ae := by
    apply hinj
    simpa only [map_mul, map_inv] using r.Ae
  Af := by
    apply hinj
    simpa only [map_mul, map_inv] using r.Af
  Be := by
    apply hinj
    simpa only [map_mul, map_inv] using r.Be
  Bf := by
    apply hinj
    simpa only [map_mul, map_inv] using r.Bf
  Ce := by
    apply hinj
    simpa only [map_mul, map_inv] using r.Ce
  Cf := by
    apply hinj
    simpa only [map_mul, map_inv] using r.Cf

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition


namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
open Subgroup Theory.GroupTheory.SymmetricFourCoxeterRecognition
variable {G : Type*} [Group G]

theorem firstParabolic_equiv_of_base_action [Finite G] (e f A B C z : G)
    (r : FirstBaseRelations e f A B C z) (hz : z ≠ 1)
    (φ : G →* Equiv.Perm (Fin 4)) (hker : φ.ker = closure ({e,f,z} : Set G))
    (hA : (φ A).IsSwap) (hB : (φ B).IsSwap) (hC : (φ C).IsSwap)
    (hcard : 192 ≤ Nat.card G) : Nonempty (G ≃* firstParabolic) := by
  obtain ⟨hneAB,hneBC,hneAC⟩ := r.image_distinct hz φ hker
  have hzker : z ∈ φ.ker := hker ▸ subset_closure (by simp)
  have hφz : φ z=1 := hzker
  have hAC2 : (φ A * φ C)^2=1 := by
    rw [← map_mul, ← map_pow, r.AC, hφz]
  have hAC : Commute (φ A) (φ C) := by
    have hAi : (φ A)⁻¹=φ A := inv_eq_of_mul_eq_one_right (by
      rw [← pow_two, ← map_pow, r.A_sq, map_one])
    have hCi : (φ C)⁻¹=φ C := inv_eq_of_mul_eq_one_right (by
      rw [← pow_two, ← map_pow, r.C_sq, map_one])
    have hi : (φ A*φ C)⁻¹=φ A*φ C := inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using hAC2)
    change (φ A) * (φ C) = (φ C) * (φ A)
    simpa only [mul_inv_rev,hAi,hCi] using hi.symm
  let a : Transposition := ⟨φ A,hA⟩
  let b : Transposition := ⟨φ B,hB⟩
  let c : Transposition := ⟨φ C,hC⟩
  have hneac : a ≠ c := fun hh => hneAC (congrArg Subtype.val hh)
  have hneab : a ≠ b := fun hh => hneAB (congrArg Subtype.val hh)
  have hnebc : b ≠ c := fun hh => hneBC (congrArg Subtype.val hh)
  have hg := closure_three_transpositions_eq_top a b c hAC hneac hneab hnebc
  have hgen := generation_of_image_and_kernel φ hker hg
  obtain ⟨hAB,hBC⟩ := transposition_chain_cubes a b c hAC hneac hneab hnebc
  have hABmem : (A*B)^3 ∈ closure ({e,f,z} : Set G) := by
    rw [← hker]
    change φ ((A*B)^3)=1
    simpa only [map_pow,map_mul] using hAB
  have hBCmem : (B*C)^3 ∈ closure ({e,f,z} : Set G) := by
    rw [← hker]
    change φ ((B*C)^3)=1
    simpa only [map_pow,map_mul] using hBC
  obtain ⟨A',C',r',hA'B,hBC',hgen'⟩ := r.normalize hABmem hBCmem
  have rr : FirstRelations e f A' B C' z :=
    { e_sq := r'.e_sq, f_sq := r'.f_sq, A_sq := r'.A_sq, B_sq := r'.B_sq,
      C_sq := r'.C_sq, z_sq := r'.z_sq, ef := r'.ef, ze := r'.ze, zf := r'.zf,
      zA := r'.zA, zB := r'.zB, zC := r'.zC, AB := hA'B, BC := hBC',
      AC := r'.AC, Ae := r'.Ae, Af := r'.Af, Be := r'.Be, Bf := r'.Bf,
      Ce := r'.Ce, Cf := r'.Cf }
  exact firstParabolic_equiv_of_relations e f A' B C' z rr (hgen'.trans hgen) hcard

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition

