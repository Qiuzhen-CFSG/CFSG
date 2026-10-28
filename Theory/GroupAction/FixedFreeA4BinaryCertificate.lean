module
public import Theory.GroupAction.FixedFreeA4CertificateRowsZeroToThree
public import Theory.GroupAction.FixedFreeA4CertificateRowsFourToSeven
public import Theory.GroupAction.FixedFreeA4CertificateRowsEightToEleven
public import Theory.GroupAction.FixedFreeA4CertificateRowsTwelveToFifteen
public import Theory.GroupAction.FixedFreeA4InvolutionConjugacy
public import Mathlib.GroupTheory.Solvable

/-!
# A plane-moving overgroup of the binary fixed-free A4 is nonsolvable

On the literal four-coordinate elementary abelian two-group, let the cubic
have its displayed fixed-free coordinate formula and let r,t satisfy the
A4 presentation with r nontrivial. If a subgroup X of actual automorphisms
contains r,t and moves a four-element subgroup fixed pointwise by r, then
X is nonsolvable.

The proved involution-conjugacy theorem changes coordinates while preserving
the cubic. The normalized reflection fixes exactly the lower coordinate
plane, so cardinality identifies the supplied C with that plane. Four
exhaustive kernel-checked matrix shards supply a short identity expressing
the reflection as a product of two commutators of its conjugates. The same
words belong to X, and normality of each derived subgroup puts this nonidentity
reflection in every term of the derived series. Conjugation transports the
actual X and C throughout the argument.

This finite action result repairs the normalizer obstruction in Stellmacher
(8.6)(b3), Journal of Algebra 190 (1997), printed p.44. The arbitrary elementary
group and its actual normalizer image are handled by the transport and native
witness modules. All finite identities are checked by Lean's kernel.
-/

namespace FixedFreeA4BinaryProof
open FixedFreeA4BinaryData
private theorem all_certificates (g : Code) (hg : good g) (hm : moves g) :
    ∃ k : Fin 53, perfect g k := by
  by_cases h4 : g.1.val < 4
  · exact certificates_zero_to_three g (Nat.zero_le _) h4 hg hm
  by_cases h8 : g.1.val < 8
  · exact certificates_four_to_seven g (by omega) h8 hg hm
  by_cases h12 : g.1.val < 12
  · exact certificates_eight_to_eleven g (by omega) h12 hg hm
  exact certificates_twelve_to_fifteen g (by omega) g.1.isLt hg hm
private abbrev V := Fin 4 → Multiplicative (ZMod 2)
private abbrev Aut := MulAut V
private def vector (b : B) : V := fun i =>
  Multiplicative.ofAdd (if b.val.testBit i.val then 1 else 0)
private def unvector (v : V) : B :=
  ((List.finRange 16).find? (fun b => vector b = v)).getD 0
private theorem vector_unvector : ∀ v : V, vector (unvector v) = v := by decide +kernel
private theorem unvector_vector : ∀ b : B, unvector (vector b) = b := by decide +kernel
private theorem vector_injective : Function.Injective vector :=
  Function.LeftInverse.injective unvector_vector
private theorem vector_surjective : Function.Surjective vector :=
  Function.RightInverse.surjective vector_unvector
private theorem vector_zero : vector 0 = 1 := by decide +kernel
private theorem vector_xor : ∀ a b : B, vector (xor a b) = vector a * vector b := by
  decide +kernel
private theorem vector_decomposition : ∀ b : B,
    vector b = (if b.val.testBit 0 then vector 1 else 1) *
      (if b.val.testBit 1 then vector 2 else 1) *
      (if b.val.testBit 2 then vector 4 else 1) *
      (if b.val.testBit 3 then vector 8 else 1) := by decide +kernel
private def code (f : Aut) : Code :=
  (unvector (f (vector 1)),unvector (f (vector 2)),
    unvector (f (vector 4)),unvector (f (vector 8)))
private theorem apply_code (f : Aut) (b : B) :
    vector (applyCode (code f) b) = f (vector b) := by
  rw [vector_decomposition b,map_mul,map_mul,map_mul]
  simp only [applyCode,code,vector_xor]
  split_ifs <;> simp only [map_one,vector_zero,vector_unvector]
private theorem code_mul (f g : Aut) : code (f*g) = mulCode (code f) (code g) := by
  have hc (b : B) : vector (unvector ((f*g) (vector b))) =
      vector (applyCode (code f) (unvector (g (vector b)))) := by
    rw [apply_code,vector_unvector,vector_unvector]
    rfl
  exact Prod.ext (vector_injective (hc 1))
    (Prod.ext (vector_injective (hc 2))
      (Prod.ext (vector_injective (hc 4)) (vector_injective (hc 8))))
private theorem code_injective : Function.Injective (fun f : Aut => code f) := by
  intro f g h
  apply MulEquiv.ext
  intro v
  obtain ⟨b,rfl⟩ := vector_surjective v
  rw [←apply_code f,←apply_code g]
  exact congrArg (fun c => vector (applyCode c b)) h
private theorem code_good (f : Aut) : good (code f) := by
  intro b h
  apply vector_injective
  have hh := congrArg vector h
  rw [apply_code f,vector_zero] at hh
  simpa only [vector_zero] using f.map_eq_one_iff.mp hh
private theorem preimage_code (f : Aut) (b : B) :
    preimage (code f) b = unvector (f⁻¹ (vector b)) := by
  have hgood : applyCode (code f) (unvector (f⁻¹ (vector b))) = b := by
    apply vector_injective
    rw [apply_code,vector_unvector]
    exact f.apply_symm_apply (vector b)
  have hex : ∃ a, (List.finRange 16).find?
      (fun v => applyCode (code f) v = b) = some a := by
    cases h : (List.finRange 16).find? (fun v => applyCode (code f) v = b) with
    | some a => exact ⟨a,rfl⟩
    | none =>
      have hh := List.find?_eq_none.mp h (unvector (f⁻¹ (vector b)))
        (List.mem_finRange _)
      exact False.elim (hh (by simp only [hgood,decide_true]))
  obtain ⟨a,ha⟩ := hex
  have heval : applyCode (code f) a = b := of_decide_eq_true (List.find?_some (p := fun v : B => decide (applyCode (code f) v = b)) ha)
  unfold preimage
  rw [ha,Option.getD_some]
  apply vector_injective
  apply f.injective
  rw [←apply_code,heval,vector_unvector]
  exact (f.apply_symm_apply (vector b)).symm
private theorem code_inverse (f : Aut) : inverseCode (code f) = code (f⁻¹) := by
  unfold inverseCode
  rw [preimage_code,preimage_code,preimage_code,preimage_code]
  rfl
private def reflectionAut : Aut where
  toFun v := ![v 0*v 2,v 1*v 3,v 2,v 3]
  invFun v := ![v 0*v 2,v 1*v 3,v 2,v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
private def cubicAut : Aut where
  toFun v := ![v 1,v 0*v 1,v 2*v 3,v 2]
  invFun v := ![v 0*v 1,v 0,v 3,v 2*v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
private theorem code_reflection : code reflectionAut = reflection := by decide +kernel
private theorem code_cubic : code cubicAut = cubic := by decide +kernel
private theorem code_cubic_inverse : code (cubicAut⁻¹) = cubicInv := by decide +kernel
private theorem reflection_square : reflectionAut*reflectionAut = 1 := by
  apply MulEquiv.ext
  intro v
  exact (show ∀ v : V, reflectionAut (reflectionAut v) = v from by decide +kernel) v
private theorem reflection_ne_one : reflectionAut ≠ 1 := by
  have h : reflectionAut (vector 4) ≠ vector 4 := by decide +kernel
  exact fun he => h (congrArg (fun f : Aut => f (vector 4)) he)
private def plane : Subgroup V where
  carrier := {v | v 2 = 1 ∧ v 3 = 1}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel
private instance : DecidablePred (fun v : V => v ∈ plane) :=
  fun v => inferInstanceAs (Decidable (v 2 = 1 ∧ v 3 = 1))
private theorem plane_card : Nat.card plane = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem mem_plane_iff : ∀ v : V, v ∈ plane ↔ reflectionAut v = v := by
  decide +kernel
private theorem vector_mem_plane : ∀ b : B, vector b ∈ plane ↔ b.val < 4 := by
  decide +kernel
open scoped commutatorElement
private theorem reflection_inverse : reflectionAut⁻¹=reflectionAut :=
  inv_eq_of_mul_eq_one_left reflection_square
private def letterAut (g : Aut) (k : Fin 5) : Aut :=
  ![reflectionAut,cubicAut,cubicAut⁻¹,g,g⁻¹] k
private def wordAut (g : Aut) (w : List (Fin 5)) : Aut :=
  (w.map (letterAut g)).prod
private theorem letter_code (g : Aut) (k : Fin 5) :
    code (letterAut g k) = letter (code g) k := by
  fin_cases k
  · exact code_reflection
  · exact code_cubic
  · exact code_cubic_inverse
  · rfl
  · exact (code_inverse g).symm
private theorem inverse_letter_code (g : Aut) (k : Fin 5) :
    code ((letterAut g k)⁻¹) = inverseLetter (code g) k := by
  fin_cases k
  · change code reflectionAut⁻¹ = reflection
    rw [reflection_inverse,code_reflection]
  · exact code_cubic_inverse
  · change code ((cubicAut⁻¹)⁻¹) = cubic
    rw [inv_inv,code_cubic]
  · exact (code_inverse g).symm
  · change code ((g⁻¹)⁻¹) = code g
    rw [inv_inv]
private theorem conjugate_word_code (g : Aut) (w : List (Fin 5)) :
    code (wordAut g w*reflectionAut*(wordAut g w)⁻¹) = conjugateWord (code g) w := by
  induction w with
  | nil => simpa only [wordAut,List.map_nil,List.prod_nil,one_mul,inv_one,mul_one,
      conjugateWord] using code_reflection
  | cons k w ih =>
    have hword : wordAut g (k::w) = letterAut g k*wordAut g w := rfl
    have heq : wordAut g (k::w)*reflectionAut*(wordAut g (k::w))⁻¹ =
        letterAut g k*(wordAut g w*reflectionAut*(wordAut g w)⁻¹)*(letterAut g k)⁻¹ := by
      rw [hword]
      group
    rw [heq,code_mul,code_mul,letter_code,ih,inverse_letter_code]
    rfl
private theorem involution_conjugate_inverse (a : Aut) :
    (a*reflectionAut*a⁻¹)⁻¹ = a*reflectionAut*a⁻¹ := by
  rw [mul_inv_rev,mul_inv_rev,inv_inv,reflection_inverse]
  group
private theorem commutator_code (a b : Aut) :
    code (⁅a*reflectionAut*a⁻¹,b*reflectionAut*b⁻¹⁆) =
      commutatorInvolutions (code (a*reflectionAut*a⁻¹)) (code (b*reflectionAut*b⁻¹)) := by
  rw [commutatorElement_def,involution_conjugate_inverse,involution_conjugate_inverse]
  simp only [code_mul,commutatorInvolutions]
private theorem standard_obstruction
    (X : Subgroup Aut) (hr : reflectionAut ∈ X) (ht : cubicAut ∈ X)
    (g : Aut) (hg : g∈X) (hm : moves (code g)) : ¬ Group.IsSolvable X := by
  obtain ⟨k,hk⟩ := all_certificates (code g) (code_good g) hm
  let w := certificates k
  have hword (w : List (Fin 5)) : wordAut g w ∈ X := by
    apply X.list_prod_mem
    intro x hx
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hx
    fin_cases i
    · exact hr
    · exact ht
    · exact X.inv_mem ht
    · exact hg
    · exact X.inv_mem hg
  let rX : X := ⟨reflectionAut,hr⟩
  let aX : X := ⟨wordAut g w.1,hword _⟩
  let bX : X := ⟨wordAut g w.2.1,hword _⟩
  let cX : X := ⟨wordAut g w.2.2.1,hword _⟩
  let dX : X := ⟨wordAut g w.2.2.2,hword _⟩
  have heq : ⁅aX*rX*aX⁻¹,bX*rX*bX⁻¹⁆ * ⁅cX*rX*cX⁻¹,dX*rX*dX⁻¹⁆ = rX := by
    apply Subtype.ext
    apply code_injective
    change code (⁅wordAut g w.1*reflectionAut*(wordAut g w.1)⁻¹,
      wordAut g w.2.1*reflectionAut*(wordAut g w.2.1)⁻¹⁆ *
      ⁅wordAut g w.2.2.1*reflectionAut*(wordAut g w.2.2.1)⁻¹,
      wordAut g w.2.2.2*reflectionAut*(wordAut g w.2.2.2)⁻¹⁆) = code reflectionAut
    rw [code_mul,commutator_code,commutator_code]
    simp only [conjugate_word_code,code_reflection]
    exact hk
  apply not_isSolvable_of_mem_derivedSeries
    (fun h : rX=1 => reflection_ne_one (congrArg Subtype.val h))
  intro n
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
    rw [←heq]
    apply (derivedSeries X (n+1)).mul_mem
    · exact Subgroup.commutator_mem_commutator
        ((derivedSeries_normal X n).conj_mem _ ih _)
        ((derivedSeries_normal X n).conj_mem _ ih _)
    · exact Subgroup.commutator_mem_commutator
        ((derivedSeries_normal X n).conj_mem _ ih _)
        ((derivedSeries_normal X n).conj_mem _ ih _)
private theorem plane_stable_of_not_moves (g : Aut) (h : ¬moves (code g)) :
    plane.map g.toMonoidHom = plane := by
  have hl1 : (code g).1.val < 4 := Nat.lt_of_not_ge (fun hh => h (Or.inl hh))
  have hl2 : (code g).2.1.val < 4 := Nat.lt_of_not_ge (fun hh => h (Or.inr hh))
  have h1 : g (vector 1) ∈ plane := by
    have hh := (vector_mem_plane (code g).1).mpr hl1
    simpa only [code,vector_unvector] using hh
  have h2 : g (vector 2) ∈ plane := by
    have hh := (vector_mem_plane (code g).2.1).mpr hl2
    simpa only [code,vector_unvector] using hh
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨v,hv,rfl⟩
    obtain ⟨b,rfl⟩ := vector_surjective v
    have hb := (vector_mem_plane b).mp hv
    have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 := by
      have hval : b.val=0 ∨ b.val=1 ∨ b.val=2 ∨ b.val=3 := by omega
      rcases hval with hval | hval | hval | hval
      · exact Or.inl (Fin.ext hval)
      · exact Or.inr (Or.inl (Fin.ext hval))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext hval)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext hval)))
    rcases hb' with rfl | rfl | rfl | rfl
    · simpa only [vector_zero,map_one] using plane.one_mem
    · exact h1
    · exact h2
    · have heq : vector 3 = vector 1*vector 2 := by decide +kernel
      rw [heq,map_mul]
      exact plane.mul_mem h1 h2
  · rw [Subgroup.card_map_of_injective g.injective]
private theorem standard_plane_obstruction
    (X : Subgroup Aut) (hr : reflectionAut ∈ X) (ht : cubicAut ∈ X)
    (C : Subgroup V) (hC : Nat.card C=4) (hrC : ∀c∈C,reflectionAut c=c)
    (hmove : ∃g∈X,C.map g.toMonoidHom≠C) : ¬Group.IsSolvable X := by
  have hCP : C ≤ plane := fun c hc => (mem_plane_iff c).mpr (hrC c hc)
  have hCeq : C=plane := Subgroup.eq_of_le_of_card_ge hCP (by rw [hC,plane_card])
  obtain ⟨g,hg,hm⟩ := hmove
  rw [hCeq] at hm
  have hcode : moves (code g) := by
    by_contra h
    exact hm (plane_stable_of_not_moves g h)
  exact standard_obstruction X hr ht g hg hcode

private theorem binary_obstruction
    (X : Subgroup Aut) (r t : Aut) (hr : r∈X) (ht : t∈X)
    (hrne : r≠1) (hr2 : r^2=1) (_ht3 : t^3=1) (_htfixed : ∀v,t v=v→v=1)
    (hcanonical : ∀v,t v= ![v 1,v 0*v 1,v 2*v 3,v 2])
    (hcomm : Commute r (t*r*t⁻¹))
    (hnorm : r*(t*r*t⁻¹)*((t^2)*r*(t^2)⁻¹)=1)
    (C : Subgroup V) (hC : Nat.card C=4) (hrC : ∀c∈C,r c=c)
    (hmove : ∃g∈X,C.map g.toMonoidHom≠C) : ¬Group.IsSolvable X := by
  obtain ⟨a,hat,har⟩ := MulAut.exists_conjugacy_fixed_free_a4_involution r t hcanonical hrne hr2 hcomm hnorm
  let f := (MulAut.congr a).toMonoidHom
  let Y := X.map f
  let D := C.map a.toMonoidHom
  have hcongr (g:Aut) : f g=a*g*a⁻¹ := by
    apply MulEquiv.ext
    intro v
    rfl
  have hfr : f r=reflectionAut := by
    rw [hcongr]
    exact MulEquiv.ext har
  have hft : f t=cubicAut := by
    rw [hcongr,hat]
    exact MulEquiv.ext hcanonical
  have hrY : reflectionAut∈Y := hfr ▸ Subgroup.mem_map_of_mem f hr
  have htY : cubicAut∈Y := hft ▸ Subgroup.mem_map_of_mem f ht
  have hD : Nat.card D=4 := (Subgroup.card_map_of_injective a.injective).trans hC
  have hrD : ∀d∈D,reflectionAut d=d := by
    rintro _ ⟨c,hc,rfl⟩
    rw [←hfr]
    change a (r (a.symm (a c)))=a c
    rw [MulEquiv.symm_apply_apply,hrC c hc]
  have hmoveY : ∃g∈Y,D.map g.toMonoidHom≠D := by
    obtain ⟨g,hg,hm⟩ := hmove
    refine ⟨f g,Subgroup.mem_map_of_mem f hg,?_⟩
    intro heq
    apply hm
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    have hcomp : (f g).toMonoidHom.comp a.toMonoidHom =
        a.toMonoidHom.comp g.toMonoidHom := by
      apply MonoidHom.ext
      intro v
      change a (g (a.symm (a v)))=a (g v)
      rw [MulEquiv.symm_apply_apply]
    change (C.map a.toMonoidHom).map (f g).toMonoidHom=C.map a.toMonoidHom at heq
    rw [Subgroup.map_map,hcomp] at heq
    rw [Subgroup.map_map]
    exact heq
  have hY := standard_plane_obstruction Y hrY htY D hD hrD hmoveY
  intro hX
  let _ := hX
  let equiv := X.equivMapOfInjective f (MulAut.congr a).injective
  exact hY (Group.isSolvable_of_surjective (f := equiv.toMonoidHom) equiv.surjective)
end FixedFreeA4BinaryProof

public theorem MulAut.not_isSolvable_of_binary_a4_and_plane_move
    (X : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod 2))))
    (r t : MulAut (Fin 4 → Multiplicative (ZMod 2)))
    (hr : r∈X) (ht : t∈X) (hrne : r≠1) (hr2 : r^2=1) (ht3 : t^3=1)
    (htfixed : ∀ v, t v=v → v=1)
    (hcanonical : ∀ v, t v = ![v 1,v 0*v 1,v 2*v 3,v 2])
    (hcomm : Commute r (t*r*t⁻¹))
    (hnorm : r*(t*r*t⁻¹)*((t^2)*r*(t^2)⁻¹)=1)
    (C : Subgroup (Fin 4 → Multiplicative (ZMod 2))) (hC : Nat.card C=4)
    (hrC : ∀ c∈C,r c=c) (hmove : ∃ g∈X,C.map g.toMonoidHom≠C) :
    ¬Group.IsSolvable X := by
  exact FixedFreeA4BinaryProof.binary_obstruction X r t hr ht hrne hr2 ht3 htfixed
    hcanonical hcomm hnorm C hC hrC hmove
