module
public import Theory.Mathieu.M12.ExceptionalParabolics.SourceRecognitionCore

/-!
# Small coordinate facts for the source two-core

The five binary exponents in the three involutions and two central
commutators enumerate the concrete two-core. Marked recognition transfers
small centralizer and inner-action certificates to any source realization.
These calculations isolate the lift corrections in Goldschmidt (6.12), p.406.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
open Subgroup
open scoped commutatorElement

private def coreWord (i : Fin 32) : SecondCore :=
  coreX ^ (i.val % 2) * coreY ^ (i.val / 2 % 2) * coreZ ^ (i.val / 4 % 2) *
    coreA ^ (i.val / 8 % 2) * coreB ^ (i.val / 16 % 2)

private theorem coreWord_injective : Function.Injective coreWord := by
  have hc : ∀ i j : Fin 32,
      ((coreWord i).val : M12) = ((coreWord j).val : M12) → i = j := by
    simp only [coreWord, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_pow,
      coreX_val,coreY_val,coreZ_val,coreA_val,coreB_val]
    decide +kernel
  intro i j he
  exact hc i j (congrArg (fun q : SecondCore => (q.val : M12)) he)

private theorem coreWord_surjective : Function.Surjective coreWord :=
  ((Nat.bijective_iff_injective_and_card coreWord).mpr
    ⟨coreWord_injective, by rw [Nat.card_fin, secondCore_card]⟩).surjective

private theorem core_centralizer_cases (q : SecondCore)
    (hx : Commute q coreX) (hy : Commute q coreY) (hz : Commute q coreZ) :
    q = 1 ∨ q = coreA ∨ q = coreB ∨ q = coreA * coreB := by
  obtain ⟨i, rfl⟩ := coreWord_surjective q
  have hc : ∀ i : Fin 32,
      coreWord i * coreX = coreX * coreWord i →
      coreWord i * coreY = coreY * coreWord i →
      coreWord i * coreZ = coreZ * coreWord i →
      coreWord i = 1 ∨ coreWord i = coreA ∨ coreWord i = coreB ∨
        coreWord i = coreA * coreB := by
    simp only [coreWord, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_pow,
      Subgroup.coe_one, coreX_val,coreY_val,coreZ_val,coreA_val,coreB_val]
    decide +kernel
  exact hc i hx.eq hy.eq hz.eq

private theorem core_not_inner_one (q : SecondCore) :
    ¬ (q * coreX * q⁻¹ = coreX * (coreA * coreB) ∧
       q * coreY * q⁻¹ = coreY ∧ q * coreZ * q⁻¹ = coreZ * coreA) := by
  obtain ⟨i, rfl⟩ := coreWord_surjective q
  have hc : ∀ i : Fin 32,
      ¬ (coreWord i * coreX * (coreWord i)⁻¹ = coreX * (coreA * coreB) ∧
         coreWord i * coreY * (coreWord i)⁻¹ = coreY ∧
         coreWord i * coreZ * (coreWord i)⁻¹ = coreZ * coreA) := by
    simp only [coreWord, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_pow,
      Subgroup.coe_inv, coreX_val,coreY_val,coreZ_val,coreA_val,coreB_val]
    decide +kernel
  exact hc i

private theorem core_not_inner_two (q : SecondCore) :
    ¬ (q * coreX * q⁻¹ = coreX * coreA ∧
       q * coreY * q⁻¹ = coreY * coreB ∧ q * coreZ * q⁻¹ = coreZ * (coreA * coreB)) := by
  obtain ⟨i, rfl⟩ := coreWord_surjective q
  have hc : ∀ i : Fin 32,
      ¬ (coreWord i * coreX * (coreWord i)⁻¹ = coreX * coreA ∧
         coreWord i * coreY * (coreWord i)⁻¹ = coreY * coreB ∧
         coreWord i * coreZ * (coreWord i)⁻¹ = coreZ * (coreA * coreB)) := by
    simp only [coreWord, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_pow,
      Subgroup.coe_inv, coreX_val,coreY_val,coreZ_val,coreA_val,coreB_val]
    decide +kernel
  exact hc i

private theorem core_involution_commutator_cases (q : SecondCore)
    (hq : q ^ 2 = 1) (hc : ⁅coreX,q⁆ = coreB) :
    q = coreZ ∨ q = coreZ*coreA ∨ q = coreZ*coreB ∨ q = coreZ*(coreA*coreB) := by
  obtain ⟨i, rfl⟩ := coreWord_surjective q
  have hh : ∀ i : Fin 32,
      coreWord i ^ 2 = 1 → ⁅coreX,coreWord i⁆ = coreB →
      coreWord i = coreZ ∨ coreWord i = coreZ*coreA ∨
        coreWord i = coreZ*coreB ∨ coreWord i = coreZ*(coreA*coreB) := by
    simp only [coreWord, commutatorElement_def, Subtype.ext_iff, Subgroup.coe_mul,
      Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_one,
      coreX_val,coreY_val,coreZ_val,coreA_val,coreB_val]
    decide +kernel
  exact hh i hq hc

variable {G : Type*} [Group G] {x y z a b : G}

private theorem comm_mem (u v : G) (Q : Subgroup G) (hu : u ∈ Q) (hv : v ∈ Q) :
    ⁅u,v⁆ ∈ Q := Q.mul_mem (Q.mul_mem (Q.mul_mem hu hv) (Q.inv_mem hu)) (Q.inv_mem hv)

private structure MarkedCore (x y z a b : G) where
  ha : a ∈ closure ({x,y,z} : Set G)
  hb : b ∈ closure ({x,y,z} : Set G)
  e : closure ({x,y,z} : Set G) ≃* SecondCore
  ex : e ⟨x,subset_closure (by simp)⟩ = coreX
  ey : e ⟨y,subset_closure (by simp)⟩ = coreY
  ez : e ⟨z,subset_closure (by simp)⟩ = coreZ
  ea : e ⟨a,ha⟩ = coreA
  eb : e ⟨b,hb⟩ = coreB

private theorem exists_markedCore
    (r : ThreeInvolutionFourCommutators.Relations x y z a b) : Nonempty (MarkedCore x y z a b) := by
  have hx : x ∈ closure ({x,y,z} : Set G) := subset_closure (by simp)
  have hy : y ∈ closure ({x,y,z} : Set G) := subset_closure (by simp)
  have hz : z ∈ closure ({x,y,z} : Set G) := subset_closure (by simp)
  have ha := r.xy ▸ comm_mem x y _ hx hy
  have hb := r.xz ▸ comm_mem x z _ hx hz
  obtain ⟨e,hex,hey,hez⟩ := r.equiv_closure core_relations
  let e' := e.trans ((MulEquiv.subgroupCongr core_generation).trans topEquiv)
  have hmapx : e' ⟨x,hx⟩ = coreX := congrArg Subtype.val hex
  have hmapy : e' ⟨y,hy⟩ = coreY := congrArg Subtype.val hey
  have hmapz : e' ⟨z,hz⟩ = coreZ := congrArg Subtype.val hez
  refine ⟨⟨ha,hb,e',hmapx,hmapy,hmapz,?_,?_⟩⟩
  · have hh := congrArg e' (show ⁅(⟨x,hx⟩ : closure ({x,y,z} : Set G)),⟨y,hy⟩⁆ = ⟨a,ha⟩ from Subtype.ext r.xy)
    rw [map_commutatorElement,hmapx,hmapy,core_relations.xy] at hh
    exact hh.symm
  · have hh := congrArg e' (show ⁅(⟨x,hx⟩ : closure ({x,y,z} : Set G)),⟨z,hz⟩⁆ = ⟨b,hb⟩ from Subtype.ext r.xz)
    rw [map_commutatorElement,hmapx,hmapz,core_relations.xz] at hh
    exact hh.symm

private noncomputable def markedCore
    (r : ThreeInvolutionFourCommutators.Relations x y z a b) : MarkedCore x y z a b :=
  Classical.choice (exists_markedCore r)

/-- Both commutators are central on the three generators. -/
theorem core_first_commutator_central
    (r : ThreeInvolutionFourCommutators.Relations x y z a b) :
    Commute a x ∧ Commute a y ∧ Commute a z ∧ Commute a b := by
  let m := markedCore r
  have hc {u v : closure ({x,y,z} : Set G)}
      (hh : Commute (m.e u) (m.e v)) : Commute u v :=
    m.e.injective (by simpa only [map_mul] using hh.eq)
  refine ⟨?_,?_,?_,?_⟩
  · exact congrArg Subtype.val (hc (u := ⟨a,m.ha⟩) (v := ⟨x,subset_closure (by simp)⟩)
      (by
        rw [m.ea,m.ex]
        change coreA*coreX=coreX*coreA
        simp only [Subtype.ext_iff,Subgroup.coe_mul,coreA_val,coreX_val]
        decide +kernel))
  · exact congrArg Subtype.val (hc (u := ⟨a,m.ha⟩) (v := ⟨y,subset_closure (by simp)⟩)
      (by
        rw [m.ea,m.ey]
        change coreA*coreY=coreY*coreA
        simp only [Subtype.ext_iff,Subgroup.coe_mul,coreA_val,coreY_val]
        decide +kernel))
  · exact congrArg Subtype.val (hc (u := ⟨a,m.ha⟩) (v := ⟨z,subset_closure (by simp)⟩)
      (by
        rw [m.ea,m.ez]
        change coreA*coreZ=coreZ*coreA
        simp only [Subtype.ext_iff,Subgroup.coe_mul,coreA_val,coreZ_val]
        decide +kernel))
  · exact congrArg Subtype.val (hc (u := ⟨a,m.ha⟩) (v := ⟨b,m.hb⟩)
      (by
        rw [m.ea,m.eb]
        change coreA*coreB=coreB*coreA
        simp only [Subtype.ext_iff,Subgroup.coe_mul,coreA_val,coreB_val]
        decide +kernel))

/-- An involution in the core with the specified commutator is a central
translate of the third marked involution. -/
theorem core_involution_commutator_eq_four
    (r : ThreeInvolutionFourCommutators.Relations x y z a b)
    {q : G} (hq : q ∈ closure ({x,y,z} : Set G)) (hs : q ^ 2 = 1)
    (hc : ⁅x,q⁆ = b) :
    q = z ∨ q = z*a ∨ q = z*b ∨ q = z*(a*b) := by
  let m := markedCore r
  let qq : closure ({x,y,z} : Set G) := ⟨q,hq⟩
  have hzQ : z ∈ closure ({x,y,z} : Set G) := subset_closure (by simp)
  have hs' : (m.e qq)^2=1 := by
    rw [← map_pow,show qq^2=1 from Subtype.ext hs,map_one]
  have hc' : ⁅coreX,m.e qq⁆=coreB := by
    rw [← m.ex,← map_commutatorElement,← m.eb]
    exact congrArg m.e (Subtype.ext hc)
  rcases core_involution_commutator_cases (m.e qq) hs' hc' with hh|hh|hh|hh
  · left
    exact congrArg Subtype.val (m.e.injective (hh.trans m.ez.symm))
  · right; left
    exact congrArg Subtype.val (m.e.injective (by rw [map_mul,m.ez,m.ea]; exact hh :
      m.e qq=m.e (⟨z,hzQ⟩*⟨a,m.ha⟩)))
  · right; right; left
    exact congrArg Subtype.val (m.e.injective (by rw [map_mul,m.ez,m.eb]; exact hh :
      m.e qq=m.e (⟨z,hzQ⟩*⟨b,m.hb⟩)))
  · right; right; right
    exact congrArg Subtype.val (m.e.injective (by rw [map_mul,map_mul,m.ez,m.ea,m.eb]; exact hh :
      m.e qq=m.e (⟨z,hzQ⟩*(⟨a,m.ha⟩*⟨b,m.hb⟩))))

/-- The centralizer of the marked generators inside their closure is exactly
its four-group of commutators. -/
theorem core_centralizer_eq_four
    (r : ThreeInvolutionFourCommutators.Relations x y z a b)
    {q : G} (hq : q ∈ closure ({x,y,z} : Set G))
    (hx : Commute q x) (hy : Commute q y) (hz : Commute q z) :
    q = 1 ∨ q = a ∨ q = b ∨ q = a * b := by
  let m := markedCore r
  let qq : closure ({x,y,z} : Set G) := ⟨q,hq⟩
  have hcx : Commute (m.e qq) coreX := by
    rw [← m.ex]
    exact (show Commute qq ⟨x,subset_closure (by simp)⟩ from Subtype.ext hx.eq).map m.e.toMonoidHom
  have hcy : Commute (m.e qq) coreY := by
    rw [← m.ey]
    exact (show Commute qq ⟨y,subset_closure (by simp)⟩ from Subtype.ext hy.eq).map m.e.toMonoidHom
  have hcz : Commute (m.e qq) coreZ := by
    rw [← m.ez]
    exact (show Commute qq ⟨z,subset_closure (by simp)⟩ from Subtype.ext hz.eq).map m.e.toMonoidHom
  rcases core_centralizer_cases (m.e qq) hcx hcy hcz with h | h | h | h
  · left
    exact congrArg Subtype.val (m.e.injective (by simpa using h : m.e qq = m.e 1))
  · right; left
    exact congrArg Subtype.val (m.e.injective (h.trans m.ea.symm))
  · right; right; left
    exact congrArg Subtype.val (m.e.injective (h.trans m.eb.symm))
  · right; right; right
    have hh : m.e qq = m.e (⟨a,m.ha⟩ * ⟨b,m.hb⟩) := by
      rw [map_mul,m.ea,m.eb]
      exact h
    exact congrArg Subtype.val (m.e.injective hh)

/-- One incompatible central shift pattern cannot be an inner action. -/
theorem core_not_inner_shift_one
    (r : ThreeInvolutionFourCommutators.Relations x y z a b)
    {q : G} (hq : q ∈ closure ({x,y,z} : Set G)) :
    ¬ (q*x*q⁻¹=x*(a*b) ∧ q*y*q⁻¹=y ∧ q*z*q⁻¹=z*a) := by
  intro h
  let m := markedCore r
  let qq : closure ({x,y,z} : Set G) := ⟨q,hq⟩
  apply core_not_inner_one (m.e qq)
  constructor
  · have hh := congrArg m.e (show qq * ⟨x,subset_closure (by simp)⟩ * qq⁻¹ =
        ⟨x,subset_closure (by simp)⟩ * (⟨a,m.ha⟩ * ⟨b,m.hb⟩) from Subtype.ext h.1)
    simpa only [map_mul,map_inv,m.ex,m.ea,m.eb] using hh
  constructor
  · have hh := congrArg m.e (show qq * ⟨y,subset_closure (by simp)⟩ * qq⁻¹ =
        ⟨y,subset_closure (by simp)⟩ from Subtype.ext h.2.1)
    simpa only [map_mul,map_inv,m.ey] using hh
  · have hh := congrArg m.e (show qq * ⟨z,subset_closure (by simp)⟩ * qq⁻¹ =
        ⟨z,subset_closure (by simp)⟩ * ⟨a,m.ha⟩ from Subtype.ext h.2.2)
    simpa only [map_mul,map_inv,m.ez,m.ea] using hh

/-- The other incompatible central shift pattern cannot be an inner action. -/
theorem core_not_inner_shift_two
    (r : ThreeInvolutionFourCommutators.Relations x y z a b)
    {q : G} (hq : q ∈ closure ({x,y,z} : Set G)) :
    ¬ (q*x*q⁻¹=x*a ∧ q*y*q⁻¹=y*b ∧ q*z*q⁻¹=z*(a*b)) := by
  intro h
  let m := markedCore r
  let qq : closure ({x,y,z} : Set G) := ⟨q,hq⟩
  apply core_not_inner_two (m.e qq)
  constructor
  · have hh := congrArg m.e (show qq * ⟨x,subset_closure (by simp)⟩ * qq⁻¹ =
        ⟨x,subset_closure (by simp)⟩ * ⟨a,m.ha⟩ from Subtype.ext h.1)
    simpa only [map_mul,map_inv,m.ex,m.ea] using hh
  constructor
  · have hh := congrArg m.e (show qq * ⟨y,subset_closure (by simp)⟩ * qq⁻¹ =
        ⟨y,subset_closure (by simp)⟩ * ⟨b,m.hb⟩ from Subtype.ext h.2.1)
    simpa only [map_mul,map_inv,m.ey,m.eb] using hh
  · have hh := congrArg m.e (show qq * ⟨z,subset_closure (by simp)⟩ * qq⁻¹ =
        ⟨z,subset_closure (by simp)⟩ * (⟨a,m.ha⟩ * ⟨b,m.hb⟩) from Subtype.ext h.2.2)
    simpa only [map_mul,map_inv,m.ez,m.ea,m.eb] using hh

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
