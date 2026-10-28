module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.PointCentralizer
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Automorphisms
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.HyperplaneFixer
public import Theory.GroupTheory.DihedralPresentation
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The pointwise fixer of the canonical quaternion core

The intrinsic core of the two-residual of the point centralizer has coordinates
C₈ ⋊ V₄. An automorphism fixing it has permutation part either the identity or
(4 5), and cocycle part represented by a vector supported on the last two
letters. These give eight automorphisms. The last transposition exchanges the
two cocycle basis vectors, so the fixer is dihedral of order eight.

The generators retain their actual markings: `alpha` is the deleted class of
the fourth coordinate unit, and `beta` is the diagonal transposition (4 5).
Source: Aschbacher–Smith 14.3.19(10), and its uses in 14.3.20–22.
-/

@[expose] public section
open Subgroup SemidirectProduct
namespace BinaryPermutation.SixNaturalSplit
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

private def pointCorePair : core (Fin 6) :=
  ⟨Pi.single 4 1 + Pi.single 5 1, by simp [mem_core]; decide⟩

theorem point_pairing_core (v : core (Fin 6)) :
    form (pairVector 4 5) (coreToNatural (Fin 6) v) = v.val 4 + v.val 5 := by
  change naturalPairing (Fin 6) (coreToNatural (Fin 6) pointCorePair)
    (coreToNatural (Fin 6) v) = _
  rw [naturalPairing_apply_core]
  simp [pointCorePair, Fin.sum_univ_six, Pi.single_apply]

theorem swap45_fixes_hyperplane (v : natural (Fin 6)) (hv : v ∈ PointAction.Hyperplane) :
    naturalRepresentation (Fin 6) swap45 v = v := by
  obtain ⟨w,rfl⟩ := coreToNatural_surjective v
  have hh := (mem_hyperplane_iff _).mp hv
  rw [point_pairing_core] at hh
  have h45 : w.val 4 = w.val 5 := by
    have h := add_eq_zero_iff_eq_neg.mp hh
    simpa only [CharTwo.neg_eq] using h
  have he : representation (Fin 6) swap45 w.val = w.val := by
    ext i
    fin_cases i <;> simp [representation_apply,swap45,Equiv.swap_apply_def,h45]
  rw [← coreToNatural_equivariant]
  congr 1
  exact Subtype.ext he

theorem hyperplane_fixer (s : Equiv.Perm (Fin 6))
    (hs : ∀v∈PointAction.Hyperplane, naturalRepresentation (Fin 6) s v=v) :
    s=1 ∨ s=swap45 := by
  obtain ⟨t,ht,hbound⟩ := HyperplaneFixer.exists_swap_bound _ pairVector45_ne_zero
  have hswap : swap45=t := (hbound swap45 (fun v hv => swap45_fixes_hyperplane v
    ((mem_hyperplane_iff _).mpr hv))).resolve_left (by decide)
  rw [←hswap] at hbound
  exact hbound s (fun v hv => hs v ((mem_hyperplane_iff _).mpr hv))

noncomputable def canonicalFixer : Subgroup (MulAut Model) :=
  fixingSubgroup (MulAut Model) (canonicalCore : Set Model)

theorem diagonal_swap45_fixes : diagonal swap45 ∈ canonicalFixer := by
  rw [canonicalFixer, mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨hv,hg⟩ := (canonicalCore_coordinates x).mp hx
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    exact swap45_fixes_hyperplane x.left.toAdd hv
  · apply Subtype.ext
    change swap45*x.right.val*swap45⁻¹=x.right.val
    have hf := pointCoreEven_le_K hg
    have hc : Commute swap45 x.right.val := by
      have h4 : x.right.val 4=4 := hf.1.1
      have h5 : x.right.val 5=5 := hf.1.2
      exact (show x.right.val * swap45 = swap45 * x.right.val by
        simpa only [swap45,h4,h5] using Equiv.mul_swap_eq_swap_mul x.right.val 4 5).symm
    exact hc.eq.symm ▸ mul_inv_cancel_right x.right.val swap45

def tailFull : (Fin 2 → ZMod 2) →ₗ[ZMod 2] Full (Fin 6) where
  toFun c := Pi.single 4 (c 0) + Pi.single 5 (c 1)
  map_add' c d := by ext i; simp [Pi.single_apply]; split_ifs <;> ring
  map_smul' a c := by ext i; simp [Pi.single_apply]; split_ifs <;> ring

noncomputable def tailDeleted : (Fin 2 → ZMod 2) →ₗ[ZMod 2] Deleted (Fin 6) :=
  (constants (Fin 6)).mkQ.comp tailFull

theorem tailDeleted_injective : Function.Injective tailDeleted := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro c hc
  have hh : tailFull c ∈ constants (Fin 6) := (Submodule.Quotient.mk_eq_zero _).mp hc
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hh
  have h0 : a=0 := by
    have h := congrFun ha 0
    simpa [allOne,tailFull,Pi.single_apply] using h
  rw [h0,zero_smul] at ha
  change c=0
  ext i
  fin_cases i
  · simpa [tailFull,Pi.single_apply] using (congrFun ha 4).symm
  · simpa [tailFull,Pi.single_apply] using (congrFun ha 5).symm

noncomputable def tailKernel : Multiplicative (Fin 2 → ZMod 2) →* MulAut Model :=
  kernelHom.comp tailDeleted.toAddMonoidHom.toMultiplicative

theorem tailKernel_fixes (c : Multiplicative (Fin 2 → ZMod 2)) : tailKernel c ∈ canonicalFixer := by
  rw [canonicalFixer, mem_fixingSubgroup_iff]
  intro x hx
  have hg := pointCoreEven_le_K ((canonicalCore_coordinates x).mp hx).2
  change (kernelEquiv (Multiplicative.ofAdd (tailDeleted c.toAdd))).val x=x
  rw [kernelEquiv_apply]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change x.left.toAdd+(SixNaturalCocycles.deletedEquiv (tailDeleted c.toAdd)).val x.right=x.left.toAdd
    have he : representation (Fin 6) x.right.val (tailFull c.toAdd)=tailFull c.toAdd := by
      have h4 : x.right.val 4=4 := hg.1.1
      have h5 : x.right.val 5=5 := hg.1.2
      ext i
      simp only [representation_apply,tailFull,LinearMap.coe_mk,AddHom.coe_mk,Pi.add_apply,
        Pi.single_apply]
      have h4i : x.right.val.symm i=4 ↔ i=4 := by rw [Equiv.symm_apply_eq,h4]
      have h5i : x.right.val.symm i=5 ↔ i=5 := by rw [Equiv.symm_apply_eq,h5]
      simp only [h4i,h5i]
    have hz : (SixNaturalCocycles.deletedEquiv (tailDeleted c.toAdd)).val x.right=0 := by
      rw [tailDeleted,LinearMap.comp_apply,SixNaturalCocycles.deletedEquiv_mk]
      apply Subtype.ext
      change (constants (Fin 6)).mkQ (representation (Fin 6) x.right.val (tailFull c.toAdd)-tailFull c.toAdd)=0
      rw [he,sub_self,map_zero]
    rw [hz,add_zero]
  · rfl

private abbrev actorA : Actor := ⟨swap01*swap23, by decide⟩
private abbrev actorB : Actor := ⟨Equiv.swap 0 2*Equiv.swap 1 3, by decide⟩

private theorem actorA_mem : actorA.val ∈ pointCoreEven := by
  refine ⟨?_,actorA.property⟩
  rw [pointCore_eq_closure]
  exact subset_closure (by simp)
private theorem actorB_mem : actorB.val ∈ pointCoreEven := by
  refine ⟨?_,actorB.property⟩
  rw [pointCore_eq_closure]
  exact subset_closure (by simp)

private theorem full_fixed_of_displacement_zero (w : Full (Fin 6))
    (g : Actor) (h4 : g.val 4=4)
    (h : (naturalDisplacement (Fin 6) w).val g=0) :
    representation (Fin 6) g.val w=w := by
  have hc : representation (Fin 6) g.val w-w ∈ constants (Fin 6) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrArg (fun v : natural (Fin 6) => (v : Deleted (Fin 6))) h
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
  have he := congrFun hc 4
  have hi : g.val.symm 4=4 := (Equiv.symm_apply_eq _).mpr h4.symm
  have hz : c=0 := by simpa [allOne,representation_apply,hi] using he
  rw [hz,zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

theorem kernel_fixer_eq_tail (d : Multiplicative (Deleted (Fin 6)))
    (hd : kernelHom d ∈ canonicalFixer) : ∃ c, tailKernel c=kernelHom d := by
  obtain ⟨w,hw⟩ := (constants (Fin 6)).mkQ_surjective d.toAdd
  have hfix (g : Actor) (hg : g.val ∈ pointCoreEven) :
      (naturalDisplacement (Fin 6) w).val g=0 := by
    have hx := ((mem_fixingSubgroup_iff (MulAut Model)).mp hd) (inr g)
      ((canonicalCore_coordinates _).mpr ⟨(PointAction.Hyperplane).zero_mem,hg⟩)
    change (kernelEquiv d).val (inr g)=inr g at hx
    rw [kernelEquiv_apply] at hx
    have hh := congrArg (fun x : Model => x.left.toAdd) hx
    change 0+(SixNaturalCocycles.deletedEquiv d.toAdd).val g=0 at hh
    rw [zero_add,←hw,SixNaturalCocycles.deletedEquiv_mk] at hh
    exact hh
  have ha := full_fixed_of_displacement_zero w actorA (by decide) (hfix actorA actorA_mem)
  have hb := full_fixed_of_displacement_zero w actorB (by decide) (hfix actorB actorB_mem)
  have h01 : w 0=w 1 := by simpa [representation_apply,swap01,swap23,Equiv.swap_apply_def]
    using (congrFun ha 0).symm
  have h23 : w 2=w 3 := by simpa [representation_apply,swap01,swap23,Equiv.swap_apply_def]
    using (congrFun ha 2).symm
  have h02 : w 0=w 2 := by simpa [representation_apply,Equiv.swap_apply_def]
    using (congrFun hb 0).symm
  let c : Fin 2 → ZMod 2 := ![w 4-w 0,w 5-w 0]
  have hc : tailDeleted c=d.toAdd := by
    rw [←hw]
    apply (Submodule.Quotient.eq _).mpr
    have he : tailFull c-w=(-w 0) • allOne (Fin 6) := by
      ext i
      fin_cases i <;> simp [tailFull,c,allOne,←h01,←h02,←h23]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact ⟨Multiplicative.ofAdd c, congrArg kernelHom (congrArg Multiplicative.ofAdd hc)⟩

theorem canonicalFixer_decomposition
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range)
    (a : MulAut Model) (ha : a ∈ canonicalFixer) :
    ∃ c : Multiplicative (Fin 2 → ZMod 2),
      a=tailKernel c ∨ a=tailKernel c*diagonal swap45 := by
  obtain ⟨k,s,hks⟩ := exists_kernel_mul_diagonal hN a
  have hs : ∀v∈PointAction.Hyperplane, naturalRepresentation (Fin 6) s v=v := by
    intro v hv
    have hx := ((mem_fixingSubgroup_iff (MulAut Model)).mp ha) (inl (Multiplicative.ofAdd v))
      ((canonicalCore_coordinates _).mpr ⟨hv,one_mem _⟩)
    change a (inl (Multiplicative.ofAdd v))=inl (Multiplicative.ofAdd v) at hx
    rw [←restriction_apply,hks,map_mul] at hx
    have hk : restriction k.val=1 := by
      change k.val ∈ restriction.ker
      rw [restriction_ker]
      exact k.property
    rw [hk,one_mul,restriction_diagonal] at hx
    exact congrArg (fun x : Model => x.left.toAdd) hx
  rcases hyperplane_fixer s hs with rfl|rfl
  · have hk : a=k.val := by simpa using hks
    obtain ⟨d,hd⟩ := kernelEquiv.surjective k
    have hkd : kernelHom d=a := (congrArg Subtype.val hd).trans hk.symm
    obtain ⟨c,hc⟩ := kernel_fixer_eq_tail d (hkd.symm ▸ ha)
    exact ⟨c,Or.inl (hc.trans hkd).symm⟩
  · have hk : k.val ∈ canonicalFixer := by
      have hh := canonicalFixer.mul_mem ha (canonicalFixer.inv_mem diagonal_swap45_fixes)
      rwa [hks,mul_inv_cancel_right] at hh
    obtain ⟨d,hd⟩ := kernelEquiv.surjective k
    have hkd : kernelHom d=k.val := congrArg Subtype.val hd
    obtain ⟨c,hc⟩ := kernel_fixer_eq_tail d (by rw [hkd];exact hk)
    refine ⟨c,Or.inr ?_⟩
    rw [hks,hc]
    exact congrArg (fun z : MulAut Model => z*diagonal swap45) (congrArg Subtype.val hd).symm


theorem tailKernel_injective : Function.Injective tailKernel := by
  intro c d h
  have hh : tailDeleted c.toAdd=tailDeleted d.toAdd := by
    apply Multiplicative.ofAdd.injective
    apply kernelEquiv.injective
    exact Subtype.ext h
  exact Multiplicative.toAdd.injective (tailDeleted_injective hh)

noncomputable def canonicalFixerCoordinates
    (cb : Multiplicative (Fin 2 → ZMod 2) × Bool) : canonicalFixer :=
  ⟨tailKernel cb.1 * diagonal (if cb.2 then swap45 else 1),
    canonicalFixer.mul_mem (tailKernel_fixes _) (by
      cases cb.2 <;> simp only [Bool.false_eq_true,reduceIte,map_one]
      · exact canonicalFixer.one_mem
      · exact diagonal_swap45_fixes)⟩

theorem canonicalFixerCoordinates_injective : Function.Injective canonicalFixerCoordinates := by
  rintro ⟨c,b⟩ ⟨d,e⟩ h
  have hm : (⟨Multiplicative.ofAdd (tailDeleted c.toAdd),if b then swap45 else 1⟩ : AutomorphismModel)=
      ⟨Multiplicative.ofAdd (tailDeleted d.toAdd),if e then swap45 else 1⟩ :=
    automorphismHom_injective (congrArg Subtype.val h)
  have hc : c=d := Multiplicative.toAdd.injective
    (tailDeleted_injective (congrArg (fun x : AutomorphismModel => x.left.toAdd) hm))
  have hb : b=e := by
    have hs := congrArg (fun x : AutomorphismModel => x.right) hm
    cases b <;> cases e <;> first | rfl | exact False.elim ((by decide : swap45≠1) hs) |
      exact False.elim ((by decide : swap45≠1) hs.symm)
  exact Prod.ext hc hb

theorem canonicalFixerCoordinates_surjective
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    Function.Surjective canonicalFixerCoordinates := by
  intro a
  obtain ⟨c,hc|hc⟩ := canonicalFixer_decomposition hN a.val a.property
  · exact ⟨(c,false),Subtype.ext (by simpa [canonicalFixerCoordinates] using hc.symm)⟩
  · exact ⟨(c,true),Subtype.ext (by simpa [canonicalFixerCoordinates] using hc.symm)⟩

theorem canonicalFixer_card
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    Nat.card canonicalFixer=8 := by
  rw [← Nat.card_congr (Equiv.ofBijective canonicalFixerCoordinates
    ⟨canonicalFixerCoordinates_injective,canonicalFixerCoordinates_surjective hN⟩),Nat.card_prod]
  change Nat.card (Fin 2 → ZMod 2)*Nat.card Bool=8
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  decide

noncomputable def alpha : MulAut Model := tailKernel (Multiplicative.ofAdd ![1,0])
noncomputable def beta : MulAut Model := diagonal swap45

theorem alpha_deleted : alpha=kernelHom (Multiplicative.ofAdd
    ((constants (Fin 6)).mkQ (Pi.single 4 1))) := by
  change kernelHom (Multiplicative.ofAdd ((constants (Fin 6)).mkQ (tailFull ![1,0])))=_
  apply congrArg kernelHom
  apply congrArg Multiplicative.ofAdd
  apply congrArg ((constants (Fin 6)).mkQ)
  ext i
  simp [tailFull]

theorem beta_tailKernel (c : Multiplicative (Fin 2 → ZMod 2)) :
    beta * tailKernel c = tailKernel (Multiplicative.ofAdd (fun i => c.toAdd (Equiv.swap 0 1 i))) * beta := by
  change diagonal swap45 * kernelHom (Multiplicative.ofAdd (tailDeleted c.toAdd)) =
    kernelHom (Multiplicative.ofAdd (tailDeleted (fun i => c.toAdd (Equiv.swap 0 1 i)))) * diagonal swap45
  rw [diagonal_kernel]
  apply congrArg (fun d => kernelHom d * diagonal swap45)
  apply Multiplicative.toAdd.injective
  change deletedRepresentation (Fin 6) swap45 (tailDeleted c.toAdd)=_
  rw [tailDeleted,LinearMap.comp_apply,deletedRepresentation_mk]
  apply congrArg ((constants (Fin 6)).mkQ)
  ext i
  fin_cases i <;> simp [representation_apply,tailFull,swap45,Equiv.swap_apply_def]

theorem tailKernel_square (c : Multiplicative (Fin 2 → ZMod 2)) : tailKernel c^2=1 := by
  rw [←map_pow]
  have hc : c^2=1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    change c.toAdd+c.toAdd=0
    ext i
    exact CharTwo.add_self_eq_zero _
  rw [hc,map_one]

theorem alpha_square : alpha^2=1 := tailKernel_square _
theorem beta_square : beta^2=1 := by
  rw [beta,←map_pow]
  have h : swap45^2=1 := by decide
  rw [h,map_one]

theorem canonicalFixer_eq_closure
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    canonicalFixer=closure ({alpha,beta} : Set (MulAut Model)) := by
  have ha : alpha ∈ closure ({alpha,beta} : Set (MulAut Model)) := subset_closure (by simp)
  have hb : beta ∈ closure ({alpha,beta} : Set (MulAut Model)) := subset_closure (by simp)
  have hab : tailKernel (Multiplicative.ofAdd ![0,1]) ∈ closure ({alpha,beta} : Set (MulAut Model)) := by
    have hh := (closure ({alpha,beta} : Set (MulAut Model))).mul_mem
      ((closure ({alpha,beta} : Set (MulAut Model))).mul_mem hb ha)
      ((closure ({alpha,beta} : Set (MulAut Model))).inv_mem hb)
    have hc : (fun i : Fin 2 => (![1,0] : Fin 2 → ZMod 2) (Equiv.swap 0 1 i)) = ![0,1] := by decide
    change beta * tailKernel (Multiplicative.ofAdd ![1,0]) * beta⁻¹ ∈ _ at hh
    rw [beta_tailKernel] at hh
    change tailKernel (Multiplicative.ofAdd (fun i => (![1,0] : Fin 2 → ZMod 2) (Equiv.swap 0 1 i))) * beta * beta⁻¹ ∈ _ at hh
    rwa [hc,mul_inv_cancel_right] at hh
  have ht (c : Multiplicative (Fin 2 → ZMod 2)) : tailKernel c ∈ closure ({alpha,beta} : Set (MulAut Model)) := by
    have hc : c.toAdd=0 ∨ c.toAdd=![1,0] ∨ c.toAdd=![0,1] ∨ c.toAdd=![1,0]+![0,1] := by
      have hh : ∀ c : Fin 2 → ZMod 2, c=0 ∨ c=![1,0] ∨ c=![0,1] ∨ c=![1,0]+![0,1] := by decide
      exact hh c.toAdd
    rcases hc with hc|hc|hc|hc
    · have he : c=1 := Multiplicative.toAdd.injective hc
      rw [he,map_one]; exact one_mem _
    · have he : c=Multiplicative.ofAdd ![1,0] := Multiplicative.toAdd.injective hc
      rw [he];exact ha
    · have he : c=Multiplicative.ofAdd ![0,1] := Multiplicative.toAdd.injective hc
      rw [he];exact hab
    · have he : c=Multiplicative.ofAdd ![1,0]*Multiplicative.ofAdd ![0,1] := Multiplicative.toAdd.injective hc
      rw [he,map_mul];exact mul_mem ha hab
  apply le_antisymm
  · intro a ha'
    obtain ⟨c,hc|hc⟩ := canonicalFixer_decomposition hN a ha'
    · rw [hc];exact ht c
    · rw [hc];exact mul_mem (ht c) hb
  · apply (closure_le _).mpr
    intro a ha'
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha'
    rcases ha' with rfl|rfl
    · exact tailKernel_fixes _
    · exact diagonal_swap45_fixes


theorem alpha_beta_fourth : (alpha*beta)^4=1 := by
  have hc : (fun i : Fin 2 => (![1,0] : Fin 2 → ZMod 2) (Equiv.swap 0 1 i)) = ![0,1] := by decide
  have hb : beta*beta=1 := by simpa only [pow_two] using beta_square
  have hs : (alpha*beta)^2=tailKernel (Multiplicative.ofAdd (![1,0]+![0,1])) := by
    rw [pow_two]
    change (alpha*beta)*(tailKernel (Multiplicative.ofAdd ![1,0])*beta)=_
    rw [mul_assoc,←mul_assoc beta,beta_tailKernel]
    change alpha*(tailKernel (Multiplicative.ofAdd (fun i => (![1,0] : Fin 2 → ZMod 2) (Equiv.swap 0 1 i)))*beta*beta)=_
    rw [hc,mul_assoc _ beta beta,hb,mul_one]
    exact (tailKernel.map_mul _ _).symm
  rw [show (4:ℕ)=2*2 from rfl,pow_mul,hs]
  exact tailKernel_square _

theorem canonicalFixer_dihedral
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    Nonempty (canonicalFixer ≃* DihedralGroup 4) := by
  have haa : alpha*alpha=1 := by simpa only [pow_two] using alpha_square
  have hbb : beta*beta=1 := by simpa only [pow_two] using beta_square
  have hai : alpha⁻¹=alpha := inv_eq_of_mul_eq_one_right haa
  have hbi : beta⁻¹=beta := inv_eq_of_mul_eq_one_right hbb
  have hconj : beta*(alpha*beta)*beta⁻¹=(alpha*beta)⁻¹ := by
    simp only [mul_inv_rev,hai,hbi,mul_assoc,hbb,mul_one]
  have hg : closure ({alpha*beta,beta} : Set (MulAut Model))=canonicalFixer := by
    rw [canonicalFixer_eq_closure hN]
    apply le_antisymm
    · apply (closure_le _).mpr
      intro x hx
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
      rcases hx with rfl|rfl
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · exact subset_closure (by simp)
    · apply (closure_le _).mpr
      intro x hx
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
      rcases hx with rfl|rfl
      · have hh := (closure ({alpha*beta,beta} : Set (MulAut Model))).mul_mem
          (subset_closure (by simp : alpha*beta ∈ ({alpha*beta,beta} : Set (MulAut Model))))
          (subset_closure (by simp : beta ∈ ({alpha*beta,beta} : Set (MulAut Model))))
        rw [mul_assoc,hbb,mul_one] at hh
        exact hh
      · exact subset_closure (by simp)
  let a : canonicalFixer := ⟨alpha*beta,mul_mem (tailKernel_fixes _) diagonal_swap45_fixes⟩
  let b : canonicalFixer := ⟨beta,diagonal_swap45_fixes⟩
  have hg' : closure ({a,b} : Set canonicalFixer)=⊤ := by
    apply map_injective canonicalFixer.subtype_injective
    rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,canonicalFixer.range_subtype,
      Set.image_insert_eq,Set.image_singleton]
    exact hg
  exact dihedralGroup_equiv_of_relations (by decide : 0<4) a b
    (Subtype.ext alpha_beta_fourth) (Subtype.ext beta_square) (Subtype.ext hconj)
    hg' (canonicalFixer_card hN)

end BinaryPermutation.SixNaturalSplit
